;; This buffer is for text that is not saved, and for Lisp evaluation.
;; To create a file, visit it with C-x C-f and enter text in its buffer.

;; (defun transpose (mat)
;;   (let ((res (loop for i in (car mat) collecting ())))
;;     (loop for row in mat
;;        do (loop for n from 0
;;              for col in row
;;              do (push col (nth n res))))
;;     res))

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
  (loop
     with i1r = (mapcar (curry #'* r) (nth i1 mat))
     for c on (nth i2 mat)
     for i1rr in i1r
     do (rplaca c (+ (car c) i1rr)))
  mat)

(defun n*-row (mat i r)
  (assert (not (zerop r)))
  (setf (nth i mat) (mapcar (curry #'* r) (nth i mat))))

(defun matrix-multiply (a b)
  (let* ((b-t (transpose b))
         (m (length a))
         (p (length b))
         (n (length (car b))))
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
                       (or (position-if (compose #'not #'zerop) row)
                           (length row)))))

(defun npivot (mat &optional self-divide)
  "Eliminates on pivots, according to the order of the matrix."
  (loop
     for row in mat
     for rowcdr on mat
     for row-i from 0
     for pivot-col = (position-if (compose #'not #'zerop) row)
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
  (nswaparoo mat)
  (npivot mat))

(defun nreduce-ref (mat)
  "Reduce the given matrix to reduced echelon form. You must use the return
value and not re-use the argument."
  (nreverse (npivot (nreverse (nreduce-ef mat)) t)))

(defun nullspace-basis (mat)
  "Return a basis of the nullspace of the linear transformation represented by
  the given matrix.")

(defun range-basis (mat)
  "Return a basis for the image of the linear transformation represented by the
  given matrix.")
