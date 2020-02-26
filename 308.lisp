;; The n- methods in this file mess with the top-level structure of the matrix
;; passed in. (copy-list) is sufficient to protect the original matrix.

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

(defmacro loop-2d (i-var j-var height width &body body)
  `(loop for ,i-var from 0 below ,height
      collect (loop for ,j-var from 0 below ,width
                   collect (progn ,@body))))

(defun elem-swap (n i1 i2)
  "Create an elementary matrix that swaps rows i1 and i2 (0-indexed). n is the
  number of rows in the matrix that will be multiplied by this elementary one,
  or the number of columns (and rows) in the returned matrix."
  (loop-2d i j n n
       (cond
         ((= i i1) (if (= j i2) 1 0))
         ((= i i2) (if (= j i1) 1 0))
         ((= j i) 1)
         (t 0))))

(defun elem+ (n i1 i2 &optional (r 1))
  "Create an elementary matrix that adds i1*r to i2 (i1 and i2 are rows)."
  (assert (not (= i1 i2)))
  (loop-2d i j n n
       (cond
         ((= j i) 1)
         ((and (= i i2) (= j i1)) r)
         (t 0))))

(defun elem* (n i1 r)
  "Create an elementary matrix that multiplies row i by r"
  (assert (not (zerop r)))
  (loop-2d i j n n
       (if (= i j) (if (= i i1) r 1) 0)))

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

(defmacro elemf (mat-place elem-place &body body)
  (with-gensyms (v1 v2 mat elem)
    `(multiple-value-bind (,v1 ,v2) (progn ,@body)
       (let ((,mat (if ,v2 ,v1 (mat* ,v1 ,mat-place)))
             (,elem (or ,v2 ,v1)))
         (setf ,mat-place ,mat)
         (setf ,elem-place (mat* ,elem ,elem-place))))))

(defun nswaparoo (mat)
  "Swap rows in mat so that the pivots do not move left as you move down."
  ;; time to implement bubble sort!
  (let* ((n (length mat))
         (elem (make-identity n)))

    (flet ((key (row)
             (or (position-if-not #'zerop row)
                 (length row))))

      (dotimes (i n)
        (do ((k (1+ i) (1+ k))) ((= k n)) 
          (when (< (key (nth k mat)) (key (nth i mat)))
            (elemf mat elem (elem-swap n i k)))))

      (values mat elem))))

(defun npivot (self-divide mat)
  "Eliminates on pivots, according to the order of the matrix. Returns the
modified matrix (though it may modify the argument too!) and the elementary
matrix to perform the pivot."
  (loop
     with n = (length mat)
     with elem = (make-identity n)
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
          do (elemf mat elem
               (elem+ n row-i row-k (- (/ (nth pivot-col lower-row)
                                          (nth pivot-col row))))))
       (when self-divide
         (elemf mat elem
           (elem* n row-i (/ (nth pivot-col row)))))
     finally (return (values mat elem))))

(defun elem-reverse (n)
  "Returns an elementary matrix that reverses the rows of a matrix."
  ;; And yes, this /is/ easier than multiplying a whole bunch of swap matrices
  ;; together, thank you for asking!
  (nreverse (make-identity n)))

(defun mat-reverse (mat)
  (elem-reverse (length mat)))

(defun pipe-elems (funs mat &optional (elem (make-identity (length mat))))
  "funs should be a list of functions that take a matrix as an argument, then
  returned a modified version of that matrix and the elementary matrix that
  would do the same thing they just did. The first function in the list is
  executed first, the opposite of function notation (more like piping)."
  (loop for fun in funs do (elemf mat elem (funcall fun mat)))
  (values mat elem))

(defun nreduce-ef (mat)
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
  (pipe-elems (list (curry #'npivot nil) #'nswaparoo) mat))

(defun nreduce-ref (mat)
  "Reduce the given matrix to reduced echelon form. You must use the return
value and not re-use the argument."
  (pipe-elems
   (list #'nreduce-ef #'mat-reverse (curry #'npivot t) #'mat-reverse)
   mat))

(defun mat-augment (mat augmented-col)
  "Plops the given column onto the end of mat. A thin wrapper over
  mat-append-cols."
  (mat-append-cols mat (transpose (list augmented-col))))

(defun solve (mat)
  "Return a solution to the system of equations represented by mat. The last
  column of mat is taken to be the augmented part of an augmented matrix. Will
  return a solution where all free variables are zero. Returns nil if the system
  is inconsistent."
  (let* ((ref (nreduce-ref mat))
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

;; TODO: a different (invert) that uses determinants
(defun invert (mat)
  (multiple-value-bind (ref elem) (nreduce-ref (copy-list mat))
    (assert (identity-p ref))
    (mat* elem (make-identity (length ref)))))

(defun leading-var-pos (mat)
  "Return a list of (i . j) pairs indicating the location of each pivot in the
given REF matrix."
  (loop
     for row in mat
     for i from 0
     for j = (position 1 row)
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
      with ref = (nreduce-ref (copy-list mat))
      with width = (length (car mat))
      with tref = (transpose ref)
      with leaders = (leading-var-pos ref)
      with free-js = (nset-difference
                    (loop for i from 0 below width collect i)
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
   (list (loop for i from 0 below (length (car mat)) collect 0))))

(setf (symbol-function 'kernel-basis) #'nullspace-basis)

(defun column-space-basis-subset (mat)
    "Find a basis for the matrix's column space that is a subset of that
    matrix's column vectors. Returns a list of those vectors (i.e, if the return
    value is treated as a matrix, its row space is the argument's column
    space)."
    (or
     (loop
        with leader-js = (mapcar #'cdr (leading-var-pos
                                        (nreduce-ref (copy-list mat))))
        for col in (transpose mat)
        for j from 0
        when (and leader-js (= j (car leader-js)))
        collect (progn
                  (setq leader-js (cdr leader-js))
                  col))
     (list (loop for i from 0 below (length mat) collect 0))))

(defun column-space-basis-row-method (mat)
  "Find a basis for the matrix's column space that may or may not be a subset of
  the matrix's column vectors."
  (or
   (remove-if (curry #'every #'zerop) (nreduce-ref (transpose mat)))
   (list (loop for i from 0 below (length mat) collect 0))))

(setf (symbol-function 'column-space-basis) #'column-space-basis-subset)

(defun row-space-basis (mat)
  (column-space-basis (transpose mat)))

(defun make-identity (n)
  (loop-2d i j n n (if (= i j) 1 0)))

(defun identity-p (mat)
  (equal (make-identity (length mat)) mat))

(defun nonsingular-p (mat)
  (identity-p (nreduce-ref (copy-list mat))))

(defun rank (mat)
  (length (leading-var-pos (copy-list mat))))

(defun nullity (mat)
  (- (length (car mat)) (rank mat)))
