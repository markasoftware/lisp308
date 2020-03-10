(ql:quickload :alexandria)
(use-package :alexandria)

(defmacro define-unary-op (fun var default doc)
  (with-gensyms (x)
    `(progn
       (defvar ,var ,default ,doc)
       (defun ,fun (,x)
         ,doc
         (funcall ,var ,x)))))
(defmacro define-binary-op (fun var default doc)
  (with-gensyms (x xs)
    `(progn
       (defvar ,var ,default ,doc)
       (defun ,fun (,x &rest ,xs)
         ,doc
         (reduce ,var (cons ,x ,xs))))))

(defvar *numerical-field* t "Non-nil when normal CL numerical operators will
work on the members of the field. Simply used to signal errors in functions that
rely on these operators (eg, finding eigenvalues).")

;; scalars
(define-binary-op s+ *scalar-adder* #'+ "Add two scalars")
(define-binary-op s* *scalar-multiplier* #'* "Multiply two scalars")
(define-unary-op s- *scalar-additive-inverter* #'- "Negate a scalar")
(define-unary-op s/ *scalar-multiplicative-inverter* #'/ "Invert a scalar")
(define-binary-op s= *scalar-equality* #'= "Compare scalars")
(defvar *s0* 0 "Scalar additive identity")
(defvar *s1* 1 "Scalar multiplicative identity")
(defun s-zerop (r) (s= *s0* r))

;; NOTE: we don't need equivalent vector functions because all vector spaces are
;; isomorphic to F^n, so we don't actually deal with vectors anywhere

(defun transpose-functional (mat &optional so-far)
  "Adds the first column of mat to so-far. It's a lot simpler than I thought!"
  (if (null (car mat))
      (nreverse so-far)
      (transpose-functional
       (mapcar #'cdr mat)
       (cons (mapcar #'car mat) so-far))))

(setf (symbol-function 'transpose) #'transpose-functional)

(defun repeat (val times)
  (loop for i from 0 below times collect val))

(defmacro loop-2d (i-var j-var height width &body body)
  `(loop for ,i-var from 0 below ,height
      collect (loop for ,j-var from 0 below ,width
                 collect (progn ,@body))))

(defun perform-row-op (mat op)
  (ecase (car op)
    (:swap                              ; (:swap i1 i2)
     (assert (not (= (second op) (third op))))
     (loop
        for row in mat
        for i from 0
        collect (cond
                  ((= i (second op)) (nth (third op) mat))
                  ((= i (third op)) (nth (second op) mat))
                  (t row))))
    (:+                                 ; (:+ r i1 i2)
     (assert (not (= (third op) (fourth op))))
     (loop
        for row in mat
        for i from 0
        collect (if (= i (fourth op))
                    (loop
                       for v2 in row
                       for v1 in (nth (third op) mat)
                       collect (s+ (s* (second op) v1) v2))
                    row)))

    (:*                                 ; (:* r i)
     (assert (not (zerop (second op))))
     (loop
        for row in mat
        for i from 0
        collect (if (= i (third op))
                    (mapcar (curry #'* (second op)) row)
                    row)))))

(defun perform-row-ops (mat ops)
  (if ops
      (perform-row-ops (perform-row-op mat (car ops)) (cdr ops))
      mat))

(defun mat* (a b)
  (let* ((b-t (transpose b))
         (m (length a))
         (p (length b))
         (n (length (car b))))
    (assert (= p (length (car a))))
    (loop-2d i k m n
         (apply #'s+
                (loop for j from 0 below p
                   collect (s* (nth j (nth i a))
                              (nth j (nth k b-t))))))))

(defun mat-expt (mat r)
  (assert (square-p mat))
  (if (diagonal-p mat)
      (mapcar (curry #'mapcar (lambda (b) (expt b r))) mat)
      (case r
        (0 (make-identity (length mat)))
        (1 mat)
        ;; r is always an integer, not a field member
        (otherwise (mat* (mat-expt mat (floor r 2))
                         (mat-expt mat (ceiling r 2)))))))

(defun mat-vec* (mat vec)
  "Take the row vector vec, convert to a column vector and multiply by mat, then
   convert back to a row vector."
  (car (transpose (mat* mat (transpose (list vec))))))

(defun mat+ (a &rest bs)
  (if bs
      (let ((b (apply #'mat+ bs)))
        (assert (= (length a) (length b)))
        (assert (= (length (car a)) (length (car b))))
        (mapcar (lambda (aa bb) (mapcar #'s+ aa bb)) a b))
      a))

(defun mat-scalar* (mat r &rest rs)
  (mapcar (curry #'mapcar (apply #'curry #'s* r rs)) mat))

(defun mat-append-cols (mat &rest mats)
  "Append mats to mat, column-wise. I.e, if mat1 is 3x3 and mat2 is 3x3, output
   will be 3x6."
  (apply (curry #'mapcar #'append) (cons mat mats)))

(defmacro row-opf (mat-place op-list-place op)
  (with-gensyms (evaled-op)
    `(let ((,evaled-op (list ,@op)))
       (setf ,op-list-place (cons ,evaled-op ,op-list-place))
       (setf ,mat-place (perform-row-op ,mat-place ,evaled-op)))))

(defun swaparoo (mat &optional seq)
  "Swap rows in mat so that the pivots do not move left as you move down."
  ;; time to implement bubble sort!
  (let ((n (length mat)))

    (flet ((key (row)
             (or (position-if-not #'s-zerop row)
                 (length row))))

      (dotimes (i n)
        (do ((k (1+ i) (1+ k))) ((= k n)) 
          (when (< (key (nth k mat)) (key (nth i mat)))
            (row-opf mat seq (:swap i k)))))

      (values mat seq))))

(defun pivot (self-divide mat &optional seq)
  "Eliminates on pivots, according to the order of the matrix."
  (loop
     with n = (length mat)
     for row-i from 0 below n
     ;; TODO: Can we avoid nthcdr and be more consy?
     for rowcdr = (nthcdr row-i mat)
     for row = (car rowcdr)
     for pivot-col = (position-if-not #'s-zerop row)
     when pivot-col
     do
       (loop
          for lower-row in (cdr rowcdr)
          for row-k from (1+ row-i)
          do (row-opf mat seq
                      (:+ (s- (s* (nth pivot-col lower-row)
                                  (s/ (nth pivot-col row))))
                          row-i row-k)))
       (when self-divide
         (row-opf mat seq (:* (s/ (nth pivot-col row)) row-i)))
     finally (return (values mat seq))))

(defun mat-reverse (mat &optional seq)
  (loop
     for i from 0 below (length mat)
     for k from (1- (length mat)) downto 0
     until (>= i k)
     do (row-opf mat seq (:swap i k)))
  (values mat seq))

(defun reduce-ef (mat &optional seq)
  "Reduce the given matrix to echelon form."
  ;; Wait a second, don't we have to reorder the rows /before/ we do the pivot?
  ;; No! In fact, swapping only before the pivot won't even necessarily give us
  ;; the matrix we want! Why? Imagine row 1 completely eliminates row 2 --
  ;; turning it into a zero row. But row 3 is nonempty. Now, after processing
  ;; row 1, the matrix is not "sorted" and further processing is not how we'd do
  ;; it on paper. We can fix this by swaparoo'ing after every elimination, but
  ;; this works well enough (although the result won't always be the same, it
  ;; will at least be in echelon form): The first row to contain a leading term
  ;; in a certain column will eliminate all the rest.
  (funcall (multiple-value-compose #'swaparoo (curry #'pivot nil)) mat seq))

(defun reduce-ref (mat &optional seq)
  "Reduce the given matrix to reduced echelon form. You must use the return
value and not re-use the argument."
  (funcall (multiple-value-compose
            #'mat-reverse (curry #'pivot t) #'mat-reverse #'reduce-ef)
           mat seq))

(defun mat-augment (mat augmented-col)
  "Plops the given column onto the end of mat. A thin wrapper over
  mat-append-cols."
  (mat-append-cols mat (transpose (list augmented-col))))

(defun solve (mat)
  "Propose a solution to the system of equations represented by mat. The last
  column of mat is taken to be the augmented part of an augmented matrix. Will
  return a solution where all free variables are zero. Returns nil if the system
  is inconsistent."
  (let* ((ref (reduce-ref mat))
         (augmented-col (lastcar (transpose ref)))
         (leaders (leading-var-pos ref)))
    ;; leading term in last col -> inconsistent
    (unless (find-if (compose (curry #'= (1- (length (car mat)))) #'cdr) leaders)
      (loop
         for j from 0 below (1- (length (car mat))) ; 1- to skip augmented col
         collect (if (and leaders (= (cdar leaders) j))
                     (prog1
                         (car augmented-col)
                       (setf leaders (cdr leaders))
                       (setf augmented-col (cdr augmented-col)))
                     0)))))

(defun make-change-of-basis-mat (old-basis new-basis)
  (mat* (invert (transpose new-basis)) (transpose old-basis)))

(defun invert (mat)
  (multiple-value-bind (ref ops) (reduce-ref mat)
    (assert (identity-p ref))
    ;; Interestingly, this still worked without the (reverse) for a while -- it
    ;; only sometimes fails using the wrong order of row operations.
    (perform-row-ops (make-identity (length ref)) (reverse ops))))

(defun invert-cofactors (mat)
  "Another method for computing the inverse."
  ;; Although it is another method, it's sorta dumb because our default
  ;; determinant implementation does the same row operations a normal inversion
  ;; would. If you truly want to do it in a different way, you'd have to use
  ;; determinant-cofactors here instead. TODO: that
  (mat-scalar* (transpose (cofactor-mat mat)) (s/ (determinant mat))))

(defun determinant (mat)
  "Returns the determinant of the matrix as calculated by row operations."
  (assert (square-p mat))
  (multiple-value-bind (ef ops) (reduce-ef mat)
    (let ((det (apply #'s* (loop
                              for row in ef
                              for i from 0
                              collect (nth i row)))))
      (dolist (op ops det)
        (ecase (car op)
          ;; swap is guaranteed not to swap a row with itself
          (:swap (setq det (s- det)))
          (:* (setq det (s* det (s/ (second op)))))
          (:+))))))

;;; All functions from here to (determinant-permutation) are utilities for it.

(defun permutation-lists (n)
  "Generate a list of all permutations of the list (0..n-1)"
  (let ((result))
    (map-permutations (lambda (p) (push p result)) (iota n))
    result))

(defun permutation-matrices (n)
  "Generate all n*n permutation matrices."
  (loop for perm in (permutation-lists n)
     collect (loop for row in perm
                collect (loop for j from 0 below n
                           collect (if (= j row) *s1* *s0*)))))

(defun select-by-mat (selection main)
  "Return a list of the values in main, from top left to bottom right in
  row-major order, where the corresponding value in the selection matrix is
  nonzero."
  (loop
     for srow in selection
     for mrow in main
     nconc (loop
              for sval in srow
              for mval in mrow
              when (not (s-zerop sval))
              collect mval)))

(defun permutation-mat-signum (mat)
  "Determine whether it will take an odd or even number of swaps to reduce the
  given permutation matrix to the identity matrix, and return -1 or 1."
  ;; It's horribly inefficient to determine the signum after we've already
  ;; generated the permutation matrix; we really ought to do it while generating
  ;; the permutations.
  (if (evenp (length (remove-if-not
                      (compose (curry #'eq :swap) #'car)
                      (second (multiple-value-list (reduce-ref mat))))))
      *s1* (s- *s1*)))

(defun determinant-permutation (mat)
  "Calculate the determinant of mat using its permutation expansion. A slower
  method than Gaussian operations (laughably so, with my implementation), but
  you get the added bonus of messier code too!"
  (assert (square-p mat))
  (apply #'s+ (loop
                 for perm-mat in (permutation-matrices (length mat))
                 collect (apply #'s*
                                (permutation-mat-signum perm-mat)
                                (select-by-mat perm-mat mat)))))

(defun minor (mat i j)
  "Return mat with row i and column j removed."
  (assert (< i (length mat)))
  (assert (< j (length (car mat))))
  (loop
     for row in mat
     for ic from 0
     unless (= i ic)
     collect (loop
                for col in row
                for jc from 0
                unless (= j jc)
                collect col)))

(defun cofactor (mat i j)
  (determinant (minor mat i j)))

(defun cofactor-mat (mat)
  (loop-2d i j (length mat) (length (car mat))
       ;; TODO: verify that it's correct to alternate between 1 and -1, rather
       ;; than exponentiating -1, in arbitrary fields.
       (if (evenp (+ i j))
           (cofactor mat i j)
           (s- (cofactor mat i j)))))

;; TODO: fix
;; (defun determinant-cofactor (mat &optional (expand-on 0) expand-on-col)
;;   "Find the determinant of the matrix using the Lagrange/cofactor expansion. By
;;   default, expands on the first row; use expand-on to specify a row to expand
;;   on, and set expand-on-col to non-nil to expand on that column instead of that
;;   row."
;;   (assert (square-p mat))
;;   (let* ((mat (if expand-on-col (transpose mat) mat))
;;          (row (nth expand-on mat)))
;;     (apply #'+ (loop
;;                   for j from 0 below (length mat)
;;                   collect (* (nth j row) (cofactor mat expand-on j))))))

(defun leading-var-pos (mat)
  "Return a list of (i . j) pairs indicating the location of each pivot in the
given REF matrix."
  (loop
     for row in mat
     for i from 0
     ;; This used to be (position 1 row) but that doesn't work for 1.0
     for j = (position-if-not #'s-zerop row)
     when j
     collect (cons i j)))

(defun nullspace-basis (mat)
  "Return a basis (list of vectors) of the nullspace of the linear
  transformation represented by the given matrix. I.e, the row space of the
  returned matrix is the kernel of the given matrix."
  ;; Do we need to run, say, (column-space-basis) on the output to eliminate
  ;; linearly dependent vectors in the return value? No! The dimension of the
  ;; nullspace is equal to the number of free variables, and this procedure
  ;; returns one vector for each free variable, so if they span the nullspace
  ;; (and they do) they form a basis.
  (or
   (loop
      with ref = (reduce-ref mat)
      with width = (length (car mat))
      with tref = (transpose ref)
      with leaders = (leading-var-pos ref)
      with free-js = (nset-difference
                      (iota width)
                      (mapcar #'cdr leaders))
      for free-j in free-js
      for free-col = (nth free-j tref)
      collect (loop
                 for result-j from 0 below width
                 for leader-cons =
                   (find-if (compose (curry #'eq result-j) #'cdr) leaders)
                 collect (cond
                           ((= result-j free-j) *s1*)
                           (leader-cons (s- (nth (car leader-cons) free-col)))
                           (t *s0*)))) ; it is a free column
   ;; When there are no free variables, we give the basis for the trivial
   ;; subspace of the domain
   (list (repeat *s0* (length (car mat))))))

(setf (symbol-function 'kernel-basis) #'nullspace-basis)

(defun column-space-basis-subset (mat)
  "Find a basis for the matrix's column space that is a subset of that
    matrix's column vectors. Returns a list of those vectors (i.e, if the return
    value is treated as a matrix, its row space is the argument's column
    space)."
  (or
   (loop
      with leader-js = (mapcar #'cdr (leading-var-pos (reduce-ref mat)))
      for col in (transpose mat)
      for j from 0
      when (and leader-js (= j (car leader-js)))
      collect (progn
                (setq leader-js (cdr leader-js))
                col))
   (list (repeat *s0* (length mat)))))

(defun column-space-basis-row-method (mat)
  "Find a basis for the matrix's column space that may or may not be a subset of
  the matrix's column vectors."
  (or
   (remove-if (curry #'every #'s-zerop) (reduce-ref (transpose mat)))
   (list (repeat *s0* (length mat)))))

(setf (symbol-function 'column-space-basis) #'column-space-basis-subset)

(defun row-space-basis (mat)
  (column-space-basis (transpose mat)))

;;;; EIGENVALUES

;; Code for finding the roots of arbitrary polynomials is beyond the scope of
;; this project, so instead we provide a method of generating the characteristic
;; polynomial without finding its roots and use closed-form root-finding
;; equations on small matrices, the only ones supported.

;; A polynomial is just a list, where the first element is the coefficient of
;; x^0, second is coefficient of x^1, etc.
(defun polynomial-canonicalize (p)
  "Remove trailing zero-coefficient terms."
  (do ((pr (reverse p) (cdr pr)))
      ((or (null pr) (not (s-zerop (car pr)))) (reverse pr))))

(defun polynomial+ (p1 &rest prest)
  (polynomial-canonicalize
   (loop
      for ps = (cons p1 prest) then (mapcar #'cdr ps)
      for power from 0
      while (some #'identity ps)
      collect (apply #'s+ (substitute *s0* nil (mapcar #'car ps))))))

(defun polynomial* (p1 &rest prest)
  ;; this is my new favorite name for local recursive functions
  (polynomial-canonicalize
   (labels ((%%% (power-left ps)
              (cond
                (ps (apply #'s+
                           (loop
                              for i from 0 to power-left
                              for p in (car ps)
                              collect (s* p (%%% (- power-left i) (cdr ps))))))
                ((= power-left 0) *s1*)
                (t *s0*))))
     (loop
        with ps = (cons p1 prest)
        for i from 0 to (apply #'+ (mapcar (compose #'1- #'length) ps))
        collect (%%% i ps)))))

;; I can't decide if I like this one or the recursive one more, so I wrote both!
(defun polynomial-non-recursive* (p1 &rest prest)
  (flet ((polynomial-binary* (p1 p2)
           (loop
              with degree = (+ -2 (length p1) (length p2))
              with p1-pad = (loop for i from 0 to degree
                               for p = p1 then (cdr p)
                               collect (or (car p) *s0*))
              with p2-pad-reverse = (reverse (loop for i from 0 to degree
                                                for p = p2 then (cdr p)
                                                collect (or (car p) *s0*)))
              for power from 0 to degree
              collect
                (loop
                   with total = *s0*
                   for val-1 in p1-pad
                   for val-2 in (nthcdr (- degree power) p2-pad-reverse)
                   do (setf total (s+ total (s* val-1 val-2)))
                   finally (return total)))))
    (polynomial-canonicalize
     (reduce #'polynomial-binary* (cons p1 prest)))))

(defun polynomial-roots (p)
  "Solve polynomials of up to degree 2 with the quadratic formula."
  (assert *numerical-field*)
  (destructuring-bind (&optional c b a) p
    (case (length p)
      (1 (list c))
      (2 (list (/ (- c) b)))
      (3 (list
          (/ (+ (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a))
          (/ (- (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a)))))))

(defun characteristic-polynomial (mat)
  (let ((*numerical-field* nil)
        (*scalar-adder* #'polynomial+)
        (*scalar-multiplier* #'polynomial*)
        (*scalar-additive-inverter* (curry #'polynomial* (list (s- *s1*))))
        (*scalar-equality* #'equalp)
        (*s0* (list *s0*))
        (*s1* (list *s1*)))
    (determinant mat)))

(defun characteristic-polynomial (mat)
  (assert (square-p mat))
  (let ((mat (loop for row in mat
                for i from 0
                collect (loop for val in row
                           for j from 0
                           collect (if (= i j) (list val -1) (list val))))))
    (apply #'polynomial+ (loop
                            for perm-mat in (permutation-matrices (length mat))
                            collect (apply #'polynomial*
                                           (list (permutation-mat-signum perm-mat))
                                           (select-by-mat perm-mat mat))))))

(defun eigenvalue-p (mat r)
  "Determine if r is an eigenvalue of mat."
  (assert (square-p mat))
  (not (nonsingular-p (mat+ mat (mat-scalar* (make-identity (length mat)) (- r))))))

(defun eigenspace-basis (mat r)
  (assert (square-p mat))
  (nullspace-basis (mat+ mat (mat-scalar* (make-identity (length mat)) (- r)))))

(defun eigenvalues-integers (mat &optional (start -1000) (end 1000))
  "Find integral eigenvalues for the given matrix by trial and error. Will
  attempt all integers between start and end."
  (remove-if-not (curry #'eigenvalue-p mat) (iota (- end start) :start start)))

(defun eigenvalues-roots (mat)
  (assert (square-p mat))
  (assert (<= (length mat) 2))
  (polynomial-roots (characteristic-polynomial mat)))

(defun eigenvalues-reasonable (mat)
  (if (<= (length mat) 2)
      (eigenvalues-roots mat)
      (eigenvalues-integers mat)))

(defvar *eigenvalue-function* #'eigenvalues-reasonable
  "The function to call to find the eigenvalues of a matrix. You should
  dynamically bind this if the default implementation doesn't find your
  eigenvalues.")

;; So we don't have to write funcall everywhere
(defun eigenvalues (mat)
  (funcall *eigenvalue-function* mat))

(defun diagonalize (mat)
  "Diagonalize the given matrix. Returns nil if not diagonalizable. Returns
  values D and P where P*D*P^(-1)=mat. You may want to dynamically bind
  *eigenvalue-function* if the default does no find all the eigenvalues for
  your matrix."
  (assert (square-p mat))
  (let*  ((n (length mat))
          (result
           (loop
              for evalue in (eigenvalues mat)
              nconc (loop
                       for evec in (eigenspace-basis mat evalue)
                       collect (cons evalue evec))))
          (result-d result)) ; just for iteration
    (when (= (length result) n) ; nil is a valid multiple-value
      (values
       (loop-2d i j n n
            (if (= i j)
                (prog1
                    (caar result-d)
                  (setf result-d (cdr result-d)))
                *s0*))
       (transpose (mapcar #'cdr result))))))

(defun mat-diagonalize-expt (mat r)
  (multiple-value-bind (d p) (diagonalize mat)
    (assert d) ; make sure it is diagonalizable
    (mat* p (mat* (mat-expt d r) (invert p)))))

(defun make-identity (n)
  (loop-2d i j n n (if (= i j) *s1* *s0*)))

(defun square-p (mat)
  (= (length mat) (length (car mat))))

(defun identity-p (mat)
  (equalp (make-identity (length mat)) mat))

(defun nonsingular-p (mat)
  (identity-p (reduce-ref mat)))

(defun diagonal-p (mat)
  (and
   (square-p mat)
   (not (loop
           for row in mat
           for i from 0
           when (loop for val in row
                   for j from 0
                   unless (or (= i j) (s-zerop val))
                   do (return t))
           do (return t)))))

(defun rank (mat)
  (length (leading-var-pos mat)))

(defun nullity (mat)
  (- (length (car mat)) (rank mat)))

;;;; APPLICATIONS

;; TODO: rewrite using diagonalization and fast exponentiation
(defun fibonacci-lame (n)
  (car (mat-vec* (mat-expt '((0 1) (1 1)) n) '(0 1))))

(defun fibonacci-cool (n)
  "Warning: returns the wrong values for large n due to rounding errors."
  (values (round (car (mat-vec*
                       (mat-diagonalize-expt '((0 1) (1 1)) n)
                       '(0 1))))))
