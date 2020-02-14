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

(defun n+-row (mat i1 i2 r)
  "Add row i1*r to i2 in mat, in-place."
  (assert (not (eq i1 i2)))
  (setf (nth i2 mat)
        (loop
           with i1r = (mapcar (curry #'* r) (nth i1 mat))
           for c in (nth i2 mat)
           for i1rr in i1r
           collect (+ c i1rr)))
  mat)

(defun n*-row (mat i r)
  (assert (not (zerop r)))
  (setf (nth i mat) (mapcar (curry #'* r) (nth i mat))))

(defun mat* (a b)
  (let* ((b-t (transpose b))
         (m (length a))
         (p (length b))
         (n (length (car b))))
    (assert (= p (length (car a))))
    (loop for i from 0 below m
       collect (loop for k from 0 below n
                  collect (apply #'+
                                 (loop for j from 0 below p
                                    collect (* (nth j (nth i a))
                                               (nth j (nth k b-t)))))))))
(defun nswaparoo (mat)
  "Swap rows in mat so that the pivots do not move left as you move down."
  ;; fun fact: sort is destructive by default.
  (sort mat #'< :key (lambda (row)
                       (or (position-if-not #'zerop row)
                           (length row)))))

(defun npivot (mat &optional self-divide)
  "Eliminates on pivots, according to the order of the matrix."
  (loop
     for row in mat
     for rowcdr on mat
     for row-i from 0
     for pivot-col = (position-if-not #'zerop row)
     when pivot-col
     do 
       (loop
          for lower-row in (cdr rowcdr)
          for row-k from (1+ row-i)
          do (n+-row mat row-i row-k (- (/ (nth pivot-col lower-row)
                                           (nth pivot-col row)))))
       (when self-divide
         (n*-row mat row-i (/ (nth pivot-col row)))))
  mat)

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
  (nswaparoo (npivot mat)))

(defun nreduce-ref (mat)
  "Reduce the given matrix to reduced echelon form. You must use the return
value and not re-use the argument."
  (nreverse (npivot (nreverse (nreduce-ef mat)) t)))

(defun invert (mat)
  (assert (nonsingular-p mat))
  ;; Because we've verified that the matrix is nonsingular, we know all the
  ;; leading terms after row reduction will occur left of the identity columns
  ;; we are adding, so that the identity columns will not affect the row
  ;; reduction.

  ;; TODO: a routine for generating the elementary matrix for row reduction
  ;; rather than just a function for doing it.
  (let* ((n (length mat))
         (id (make-identity n))
         (wide (loop for a in mat for b in id collect (append a b)))
         (wide-ref (nreduce-ref wide))
         (skinny (loop for row in wide-ref collect (nthcdr n row))))
    skinny))

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

(defun make-identity (n)
  (loop
     for i from 0 below n
     collect (loop for k from 0 below n collect (if (= i k) 1 0))))

(defun identity-p (mat)
  (equal (make-identity (length mat)) mat))

(defun nonsingular-p (mat)
  (identity-p (nreduce-ref (copy-list mat))))
