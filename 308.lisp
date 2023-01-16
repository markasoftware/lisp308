(ql:quickload :alexandria)
(use-package :alexandria)

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
                       collect (+ (* (second op) v1) v2))
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
         (apply #'+
                (loop for j from 0 below p
                   collect (* (nth j (nth i a))
                              (nth j (nth k b-t))))))))

(defun mat-expt (mat r)
  (assert (square-p mat))
  (if (diagonal-p mat)
      (mapcar (curry #'mapcar (lambda (b) (expt b r))) mat)
      (case r
        (0 (make-identity (length mat)))
        (1 mat)
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
        (mapcar (lambda (aa bb) (mapcar #'+ aa bb)) a b))
      a))

(defun mat-scalar* (mat r &rest rs)
  (mapcar (curry #'mapcar (apply #'curry #'* r rs)) mat))

(defun mat-append-cols (mat &rest mats)
  "Append mats to mat, column-wise. I.e, if mat1 is 3x3 and mat2 is 3x3, output
   will be 3x6."
  (apply (curry #'mapcar #'append) (cons mat mats)))

(defmacro domat (mat (elt-sym &optional (i-sym (gensym "I")) (j-sym (gensym "J"))) &body body)
  "Evaluate the body on every element of the given matrix, binding i-sym to the row number and j-sym to the column number (both 0-indexed) while evaluating body."
  (declare (symbol elt-sym i-sym j-sym))
  (alexandria:with-gensyms (row-sym)
    `(loop for ,i-sym from 0
           for ,row-sym in ,mat
           do (loop for ,j-sym from 0
                    for ,elt-sym in ,row-sym
                    do (progn ,@body)))))

(defun mat-frobenius-norm (mat)
  "Treat the matrix as a vector, and return its l2-norm. Returns 0 on empty matrix."
  (let ((sum 0))
    (domat mat (elt)
      (setf sum (+ sum (expt elt 2))))
    (sqrt sum)))

(defun mat-infinity-norm (mat)
  "Return the matrix entry with the largest magnitude, breaking ties arbitrarily. Returns 0 on empty matrix."
  (let ((max 0))
    (domat mat (elt)
      (when (> (abs elt) (abs max))
        (setf max elt)))
    max))

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
             (or (position-if-not #'zerop row)
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
     for pivot-col = (position-if-not #'zerop row)
     when pivot-col
     do
       (loop
          for lower-row in (cdr rowcdr)
          for row-k from (1+ row-i)
          do (row-opf mat seq
                      (:+ (- (/ (nth pivot-col lower-row)
                                (nth pivot-col row)))
                          row-i row-k)))
       (when self-divide
         (row-opf mat seq (:* (/ (nth pivot-col row)) row-i )))
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
  "Return a solution to the system of equations represented by mat. The last
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
  (mat-scalar* (transpose (cofactor-mat mat)) (/ (determinant mat))))

(defun determinant (mat)
  "Returns the determinant of the matrix as calculated by row operations."
  (assert (square-p mat))
  (multiple-value-bind (ef ops) (reduce-ef mat)
    (let ((det (apply #'* (loop
                             for row in ef
                             for i from 0
                             collect (nth i row)))))
      (dolist (op ops det)
        (ecase (car op)
          ;; swap is guaranteed not to swap a row with itself
          (:swap (setq det (- det)))
          (:* (setq det (/ det (second op))))
          (:+))))))

;;; All functions from here to (determinant-permutation) are utilities for it.

(defun permutation-lists (n)
  "Generate a list of all permutations of the list (0..n-1)"
  (let ((result))
    (map-permutations (lambda (p) (push p result)) (iota n))
    result))

(defun make-permutation-matrix (perm-list)
  "Given a permutation represented as a list (ie, the 0-th element of the list says where the 0 is mapped to), return a corresponding permutation matrix."
  (loop with n = (length perm-list)
        for perm-destination in perm-list
        collect (loop for perm-possible-destination from 0 below n
                      collect (if (= perm-possible-destination perm-destination) 1 0))))

(defun permutation-matrices (n)
  "Generate all n*n permutation matrices."
  (mapcar 'make-permutation-matrix (permutation-lists n)))

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
              when (not (zerop sval))
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
      1 -1))

(defun determinant-permutation (mat)
  "Calculate the determinant of mat using its permutation expansion. A slower
  method than Gaussian operations (laughably so, with my implementation), but
  you get the added bonus of messier code too!"
  (assert (square-p mat))
  (apply #'+ (loop
                for perm-mat in (permutation-matrices (length mat))
                collect (apply #'*
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
       (* (expt -1 (+ i j)) (cofactor mat i j))))

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
     for j = (position-if (compose #'not #'zerop) row)
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
                           ((= result-j free-j) 1)
                           (leader-cons (- (nth (car leader-cons) free-col)))
                           (t 0)))) ; it is a free column
   ;; When there are no free variables, we give the basis for the trivial
   ;; subspace of the domain
   (list (repeat 0 (length (car mat))))))

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
   (list (repeat 0 (length mat)))))

(defun column-space-basis-row-method (mat)
  "Find a basis for the matrix's column space that may or may not be a subset of
  the matrix's column vectors."
  (or
   (remove-if (curry #'every #'zerop) (reduce-ref (transpose mat)))
   (list (repeat 0 (length mat)))))

(setf (symbol-function 'column-space-basis) #'column-space-basis-subset)

(defun row-space-basis (mat)
  (column-space-basis (transpose mat)))

;;;; EIGENVALUES

;; Code for finding the roots of arbitrary polynomials is beyond the scope of
;; this project, so instead we provide a method of generating the characteristic
;; polynomial without finding its roots and use closed-form root-finding
;; equations on small matrices, the only ones supported.

;; A polynomial is just a list, where the first element is the coefficient of
;; x^0, second is coefficient of x^1, etc. nil is a valid way to denote the zero
;; polynomial.
(defun polynomial-canonicalize (p)
  "Remove trailing zero-coefficient terms."
  (do ((pr (reverse p) (cdr pr)))
      ((or (null pr) (not (zerop (car pr)))) (reverse pr))))

(defun polynomial+ (p1 &rest prest)
  (polynomial-canonicalize
   (loop
      for ps = (cons p1 prest) then (mapcar #'cdr ps)
      for power from 0
      while (some #'identity ps)
      collect (apply #'+ (substitute 0 nil (mapcar #'car ps))))))

(defun polynomial- (p &rest prest)
  (if prest
      (apply 'polynomial+ p (mapcar (curry #'mapcar #'-) prest))
      (mapcar #'- p)))

(defun polynomial* (p1 &rest prest)
  ;; this is my new favorite name for local recursive functions
  (polynomial-canonicalize
   (labels ((%%% (power-left ps)
              (cond
                (ps (apply #'+
                           (loop
                              for i from 0 to power-left
                              for p in (car ps)
                              collect (* p (%%% (- power-left i) (cdr ps))))))
                ((= power-left 0) 1)
                (t 0))))
     (loop
        with ps = (cons p1 prest)
        for i from 0 to (apply #'+ (mapcar (compose #'1- #'length) ps))
        collect (%%% i ps)))))

(defun polynomial-zerop (p)
  (or (null p)
      (and (not (cdr p)) (zerop (car p)))))

(defun polynomial/ (dividend divisor)
  "Returns multiple values: The quotient and the remainder."
  ;; Idea of long division: The first coefficient is fully constrained by the
  ;; ratio between the leading coefficients and the difference between the
  ;; degree of the quotient and divisor
  (assert (not (polynomial-zerop divisor)) (divisor))
  (loop with remainder = (polynomial-canonicalize dividend)
        with divisor-deg = (polynomial-degree divisor)
        with quotient-degree = (- (polynomial-degree dividend) divisor-deg)
        for i from quotient-degree downto 0
        ; multiply divisor by quotient coefficient to cancel out leading term of remainder
        for quotient-coefficient = (/ (or (nth (+ divisor-deg i) remainder) 0) (lastcar divisor))
        do (setf remainder
                 (polynomial- remainder
                              (polynomial*
                               divisor
                               (list quotient-coefficient)
                               ;; construct x^i
                               (loop for k from 0 to i
                                     collect (if (= k i) 1 0)))))
        collect quotient-coefficient into result
        finally (return
                  (values (polynomial-canonicalize (reverse result))
                          (polynomial-canonicalize remainder)))))

(defun polynomial-expt (p n)
  "Naively exponentiate the given polynomial"
  (declare (number n))
  ;; a non-naive example might be doing it in logarithmic time by splitting the
  ;; exponent by powers of two, or maybe calculating the exponents directly
  ;; using the binomial theorem (though factorials may present their own
  ;; optimization problem)
  (if (zerop n)
      '(1)
      (loop repeat n
            for result = p then (polynomial* result p)
            finally (return result))))

(defun polynomial-evaluate (p1 p2)
  "Substitute p2 as the 'x' in p1. p2 should be a whole polynomial, not just a
  number."
  (loop for i from 0
        for coef in p1
        for result = (polynomial+
                      result
                      (polynomial*
                       (list coef)
                       (polynomial-expt p2 i)))
        finally (return result)))

;; I can't decide if I like this one or the recursive one more, so I wrote both!
(defun polynomial-non-recursive* (p1 &rest prest)
  (flet ((polynomial-binary* (p1 p2)
           (loop
              with degree = (+ -2 (length p1) (length p2))
              with p1-pad = (loop for i from 0 to degree
                               for p = p1 then (cdr p)
                               collect (or (car p) 0))
              with p2-pad-reverse = (reverse (loop for i from 0 to degree
                                                for p = p2 then (cdr p)
                                                collect (or (car p) 0)))
              for power from 0 to degree
              collect
                (loop
                   with total = 0
                   for val-1 in p1-pad
                   for val-2 in (nthcdr (- degree power) p2-pad-reverse)
                   do (incf total (* val-1 val-2))
                   finally (return total)))))
    (polynomial-canonicalize
     (reduce #'polynomial-binary* (cons p1 prest)))))

(defun polynomial-roots (p)
  "Solve polynomials of up to degree 2 with the quadratic formula. Real roots
only."
  ;; TODO: make it so it only returns real roots!
  (destructuring-bind (&optional c b a) p
    (case (length p)
      (1 (list c))
      (2 (list (/ (- c) b)))
      (3 (list
          (/ (+ (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a))
          (/ (- (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a)))))))

(defun polynomial-degree (p)
  "Returns -1 for the zero polynomial."
  (1- (length (polynomial-canonicalize p))))

(defun polynomial-gcd (a &rest bs)
  (flet ((polynomial-gcd-2 (a b)
           (assert (not (polynomial-zerop a)))
           (assert (not (polynomial-zerop b)))
           (when (> (polynomial-degree b) (polynomial-degree a))
             (psetq a b b a))
           ;; basically Euclid's algorithm
           (loop
              do (format t "a: ~a b: ~a~%" a b)
              until (polynomial-zerop b)
              do (psetq a b
                        b (cadr (multiple-value-list (polynomial/ a b))))
              finally (return (polynomial/ a (list (lastcar a)))))))
    (reduce #'polynomial-gcd-2 (cons a bs))))

(defun polynomial-to-string (p)
  "Polynomial to human-readable string."
  (loop with p = (reverse (polynomial-canonicalize p))
        with result = ""
        for deg from (1- (length p)) downto 0
        for coef in p
        for degstr = (case deg
                       (0 "")
                       (1 "x")
                       (otherwise (concatenate 'string "x^" (write-to-string deg))))
        for sep = "" then " + "
        do (setf result (concatenate 'string result sep (write-to-string coef) degstr))
        finally (return result)))

;; I originally wrote this by passing the addition and multiplication functions
;; to (determinant-permutation) instead of copy-pasting the
;; (determinant-permutation) code here. But then the problem became that signum
;; returns an integer, not a degree-zero polynomial. Since I have no intention
;; of expanding this project to work on arbitrary fields and vector spaces, I
;; opted to copy-paste instead.
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
  "Determine if r is an exact eigenvalue of mat."
  (assert (square-p mat))
  (not (nonsingular-p (mat+ mat (mat-scalar* (make-identity (length mat)) (- r))))))

(defun eigenspace-basis (mat r)
  "Find the basis of the eigenspace for the exact eigenvalue r of matrix r."
  (assert (square-p mat))
  (nullspace-basis (mat+ mat (mat-scalar* (make-identity (length mat)) (- r)))))

(defun eigenvalues-integers (mat &optional (start -1000) (end 1000))
  "Find integral eigenvalues for the given matrix by trial and error. Will
  attempt all integers between start and end."
  (remove-if-not (curry #'eigenvalue-p mat) (iota (- end start) :start start)))

(defun vector-normalize (vec &optional (norm-fn 'mat-frobenius-norm))
  "Given a vector (which can really be any matrix), return a version with norm 1. Assumes that norm-fn is linear with respect to multiplication of the vector by scalars."
  (mat-scalar* vec (/ (funcall norm-fn vec))))

(defun random-unit-vector (n)
  "Return a random n*1 real unit vector, randomly distributed over the (n-1)-sphere"
  ;; https://angms.science/doc/RM/randUnitVec.pdf
  (vector-normalize (loop repeat n collect (list (alexandria:gaussian-random -1 1)))))

(defun max-eigenvalue-power (mat &key initial-vector (epsilon 0.00001))
  "Use the power method to find the maximum eigenvalue. Returns an eigenvector as a multiple value. Stops iterating once the computed eigenvalue from two subsequent iterations are within epsilon of each other."
  (assert (square-p mat))
  (loop for old-x = (or initial-vector
                        (random-unit-vector (length mat)))
          then (vector-normalize new-x)
        for new-x = (mat* mat old-x)
        for previous-estimate = most-positive-fixnum then estimate
        for estimate = (mat-infinity-norm new-x)
        while (> (abs (- estimate previous-estimate)) epsilon)
        ;; don't need to divide estimate by previous-estimate as indicated in textbook because normalizing the vector each iteration is equivalent to dividing the next x by the current |x|.
        finally (return estimate)))

(defun eigenvalues-roots (mat)
  (assert (square-p mat))
  (assert (<= (length mat) 2))
  (polynomial-roots (characteristic-polynomial mat)))

(defvar *eigenvalue-function* #'eigenvalues-roots
  "The function to call to find the eigenvalues of a matrix. You should
  dynamically bind this if the default implementation doesn't find your
  eigenvalues.")

;; So we don't have to write funcall everywhere
(defun eigenvalues (mat)
  (funcall *eigenvalue-function* mat))

(defun eigen-values-and-vectors (mat)
  "Returns an alist of eigenvalues to a basis for their eigenspace."
  (loop for evalue in (eigenvalues mat)
     collect (cons evalue (eigenspace-basis mat evalue))))

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
                0))
       (transpose (mapcar #'cdr result))))))

(defun mat-diagonalize-expt (mat r)
  (multiple-value-bind (d p) (diagonalize mat)
    (assert d) ; make sure it is diagonalizable
    (mat* p (mat* (mat-expt d r) (invert p)))))

(defun make-identity (n)
  (loop-2d i j n n (if (= i j) 1 0)))

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
                   unless (or (= i j) (zerop val))
                   do (return t))
           do (return t)))))

(defun rank (mat)
  (length (leading-var-pos (reduce-ef mat))))

(defun nullity (mat)
  (- (length (car mat)) (rank mat)))

(defun rotation-mat (theta)
  `((,(cos theta) ,(- (sin theta)))
    (,(sin theta) ,(cos theta))))

(defun map-matrix (fn mat)
  "Run fn on every element of mat"
  (loop for row in mat
     collect (loop for col in row
                collect (funcall fn col))))

(defun ⮾ (m1 m2)
  "Kronecker Product. Should be both row or both column vectors if vectors."
  (loop for row1 in m1
     append (loop for row2 in m2
               collect (loop for col1 in row1
                          append (loop for col2 in row2
                                    collect (* col1 col2))))))

(defun † (mat)
  (map-matrix 'conjugate (transpose mat)))

(defun projection-matrix (basis)
  "Create a projection matrix onto the space spanned by the given
  basis (rowspace of parameter)"
  (assert (= (rank basis) (length basis))) ; check it's actually a basis
  (mat* (transpose basis) ; project it onto the new basis
        (mat* (invert (mat* basis (transpose basis))) ; correction factor
              basis ; find correlation with each basis vector
              )))

(defun project (vector basis)
  "takes and returns a simple list"
  (car (transpose (mat* (projection-matrix basis) (transpose (list vector))))))

(defun matrix->latex (mat &optional (environment "bmatrix"))
  (format nil "\\begin{~a}~{~{~a~^&~}~^\\\\~}\\end{~a}"
          environment mat environment))


;;;; APPLICATIONS

;; TODO: rewrite using diagonalization and fast exponentiation
(defun fibonacci-lame (n)
  (car (mat-vec* (mat-expt '((0 1) (1 1)) n) '(0 1))))

(defun fibonacci-cool (n)
  "Warning: returns the wrong values for large n due to rounding errors."
  (values (round (car (mat-vec*
                       (mat-diagonalize-expt '((0 1) (1 1)) n)
                       '(0 1))))))

;;;; Quantum Computing

(defvar *q-random-resolution* (expt 2 32))
(defvar *q-state-tolerance* 0.00001)

(defun q-near-1-p (num)
  (< (abs (- 1 num)) *q-state-tolerance*))

(defun q-state-p (state)
  (q-near-1-p (reduce '+ state)))

(defun q-unitary-p (gate)
  (and (square-p gate)
       (loop for row in (mat* († gate) gate)
          for i from 0
          always (q-near-1-p (nth i row)))))

(defun q-gate-identity (n)
  (make-identity (* 2 n)))

(defun q-offset-gate (offset-bits gate)
  (assert (square-p gate))
  (⮾ gate (make-identity (max 1 (* 2 offset-bits)))))

(defun q-gate-preset (a b which)
  "A gate that will turn |0> into |a>, |b>. For initializing a qubit."
  (assert (q-near-1-p (+ (expt a 2) (expt b 2))))
  (q-offset-gate which
                 `((,a ,(- b))
                   (,b ,a))))

(defun q-gate-random (which &aux (1-probability (/ (random 100000) 100000)))
  "Randomizes the state of the qubit. Only really useful for testing."
  (q-gate-preset (sqrt (- 1 1-probability)) (sqrt 1-probability) which))

(defun q-gate-h (which)
  (q-offset-gate which
                 (mat-scalar* '((1 1)
                                (1 -1)) (/ (sqrt 2)))))

(defun q-gate-x (which)
  (q-offset-gate which
                 '((0 1)
                   (1 0))))

(defun q-gate-z (which)
  (q-offset-gate which
                 '((1 0)
                   (0 -1))))

(defun q-gate-cnot (control-bit victim-bit
                    &aux (n (expt 2 (1+ (max control-bit victim-bit)))))
  (loop-2d i j n n
       ;; if the control bit is set...
       (if (logbitp control-bit j)
           ;; ...flip the victim bit
           (if (eq i (logxor j (ash 1 victim-bit))) 1 0)
           ;; otherwise, keep the state the same
           (if (eq i j) 1 0))))

(defun q-init (n)
  "Initialize a state containing n qubits, all certainly zero. To apply gates,
simply multiply a matrix on the left."
  (loop for i from 0 below (expt 2 n)
     collect (list (if (zerop i) 1 0))))

(defun squared-magnitude (c)
  (declare (number c))
  (* c (conjugate c)))

(defun q-measure-all (state)
  (loop
     with last-nonzero-outcome
     with format-specifier = (format nil "~~~d,'0b" (floor (length state) 2))
     for outcome-probability in (mapcar (compose 'squared-magnitude 'car) state)
     for i from 0
     unless (zerop outcome-probability)
     do (setq last-nonzero-outcome i)
     when (< (random *q-random-resolution*)
             (* outcome-probability *q-random-resolution*))
     return (format nil format-specifier i)
     finally (return (format nil format-specifier last-nonzero-outcome))))

(defun q-bit-probability (bit state)
  "The overall probability that the given qubit will be 1 when measured."
  (loop
     with result = 0
     for outcome-probability in (mapcar (compose 'squared-magnitude 'car) state)
     for i from 0
     when (logbitp bit i)
     do (incf result outcome-probability)
     finally (return result)))

(defun state= (state1 state2)
  (and (= (length state1) (length state2))
       (loop for amplitude1 in state1
          for amplitude2 in state2
          always (< (abs (- amplitude1 amplitude2)) *q-state-tolerance*))))

(defun q-bit-probability-distribution (bit state)
  "All the possible states the qubit may be in, and the probability it is in
  each, if all other bits were measured right now."
  ;; result is an alist from states to their probabilities
  (loop
     with result
     with reordered-state =
     ;; stable keeps zeroes and ones of the Bit In Question in order
       (stable-sort (loop for (amplitude) in state
                       for i from 0
                       collect (cons amplitude i))
                    (lambda (state1 state2)
                      (< (logandc1 (ash 1 bit) (cdr state1))
                         (logandc1 (ash 1 bit) (cdr state2)))))
     for ((0-amplitude) (1-amplitude)) on reordered-state by #'cddr
     for probability = (+ (expt 0-amplitude 2) (expt 1-amplitude 2))
     for 0-normalized = (/ 0-amplitude (sqrt probability))
     for 1-normalized = (/ 1-amplitude (sqrt probability))
     when (plusp probability)
     do (let* ((0-normalized (/ 0-amplitude (sqrt probability)))
               (1-normalized (/ 1-amplitude (sqrt probability)))
               (result-cons (or (assoc (list 0-normalized 1-normalized) result
                                       :test 'state=)
                                (car (push (cons
                                            (list 0-normalized 1-normalized)
                                            0)
                                           result)))))
          (incf (cdr result-cons) probability))
     finally (return result)))

(defun q-measure-bit (bit state)
  "Returns two values: Whether the qubit was measured as 1 and the new state"
  (let* ((1-probability (q-bit-probability bit state))
         (result-1 (< (random *q-random-resolution*)
                      (* 1-probability *q-random-resolution*)))
         ;; probability of measuring it the way it was actually measured
         (actual-probability (if result-1 1-probability (- 1 1-probability)))
         (probability-normalizer (sqrt actual-probability)))
    (values
     result-1
     (loop
        for (outcome-probability) in state
        for i from 0
        collect (list (if (eq result-1 (logbitp bit i))
                          (/ outcome-probability probability-normalizer)
                          0))))))

(defun q-run-gate (gate state)
  ;; "left-pad" the gate
  (mat* (⮾ (make-identity (max 1 (/ (length state)
                                    (length gate))))
           gate)
        state))

(defvar *q-state*)

(defun q-run-gates* (&rest gates)
  (dolist (gate gates)
    (setf *q-state* (q-run-gate gate *q-state*))))

(defun q-measure-bit* (bit)
  (multiple-value-bind (outcome new-state) (q-measure-bit bit *q-state*)
    (setf *q-state* new-state)
    outcome))

;;;; Applications of Quantum Computing

(defun q-teleport (a b &aux (*q-state* (q-init 3)))
  "Initializes the first qubit of the state with amplitudes a|0> and b|1>, then
makes the third qubit have those same amplitudes, despite not applying any
multi-qubit operations that involve the third qubit after any operations have
been performed on the first qubit."
  (format t "Entangling qubits~%")
  (q-run-gates*
   (q-gate-preset a b 0)
   (q-gate-h 1)
   (q-gate-cnot 1 2)
   ;; should now be 1/sqrt2 (|00> + |11>) on last two qubits

   ;; Now, the qubits are separated in space, with the first and
   ;; second kept together, isolated from the third leave for a
   ;; classical communications channel.
   (q-gate-cnot 0 1) ; if the qubit-in-question, hereafter referred to as the
                                        ; QIQ, is zero, then bits 1 and 2 remain in their bell
                                        ; state. But if the QIQ is one, their bell state is
                                        ; "flipped" into |10〉+|01〉. At this point, measuring both
                                        ; bits 1 and 2 tells us what would happen if we measure the
                                        ; QIQ. In fact, measuring any two of the qubits tells us
                                        ; what will happen to the last.
   (q-gate-h 0))  ; After this, measuring bits 0 and 1 no longer tells us what 2
                  ; will measure as.
  
  ;; now the person with the first two bits measures them, which informs the
  ;; person with the third bit what to do.
  (let ((bit-0 (q-measure-bit* 0))
        (bit-1 (q-measure-bit* 1)))
    (format t "Measured bits as ~a and ~a.~%" bit-0 bit-1)
    (switch ((list bit-0 bit-1) :test #'equal)
      ('(nil nil)
        ;; Nothing to do!
        )
      ('(nil t)
        (q-run-gates* (q-gate-x 2)))
      ('(t nil)
        (q-run-gates* (q-gate-z 2)))
      ('(t t)
        (q-run-gates*
         (q-gate-x 2)
         (q-gate-z 2)))))

  (q-bit-probability-distribution 2 *q-state*))

(defun linear-regression (data)
  "Finds the line of best fit (least squares) for the given data. Data should be
  a list of cons, with each car being the x-value, and each cdr being the
  y-value. Return multiple values: slope and y-intercept."
  (assert (>= (length data) 2))
  (assert (/= (cdar data) (cdadr data))) ; not same x-value
  (let* ((projection
           (project (mapcar #'cdr data)
                    ;; assertions ensure these are lin indep
                    (list
                     (repeat 1 (length data))
                     (mapcar #'car data))))
         (slope (/ (- (lastcar projection) (car projection))
                   (- (car (lastcar data)) (caar data))))
         (y-int (- (car projection) (* slope (caar data)))))
    (values slope y-int)))
