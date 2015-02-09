#||
? ? 2
1 0 ?
? ? ?
||#

;; realistically, we'll never need more than n-machine-word-bits.
(deftype box (&optional n)
  `(simple-array simple-bit-vector (,n)))

(deftype instance (&optional n)
  `(simple-array (mod ,most-positive-fixnum) (,n)))

(defstruct store
  (clauses nil :type list))

(defun prefix-max (x y)
  (declare (type simple-bit-vector x y))
  (when (> (length x) (length y))
    (rotatef x y))
  (let ((n (length x)))
    (assert (not (mismatch x y :end1 n :end2 n)))
    y))

(defun resolve (x y)
  (declare (type box x y))
  (let ((found-match nil))
    (assert (= (length x) (length y)))
    (map 'box
         (lambda (a b)
           (declare (type simple-bit-vector a b))
           (cond ((equal a b)
                  a)
                 ((/= (length a) (length b))
                  (prefix-max a b))
                 (t
                  (assert (not found-match))
                  (let* ((diff (mismatch a b))
                         (m (length a)))
                    (assert (= (length b) m))
                    (assert (and diff (= diff (1- m))))
                    (setf found-match t)
                    (subseq a 0 (1- m))))))
         x y)))

(defun covers-p (cover goal)
  (declare (type box cover goal))
  (assert (= (length cover) (length goal)))
  (every (lambda (a b)
           (and (<= (length a) (length b))
                (not (mismatch a b :end2 (length a)))))
         cover goal))

;; check for simple containment in a learned box
(defun any-covered-p (clauses goal)
  (dolist (clause (store-clauses clauses) nil)
    (when (covers-p clause goal)
      (return clause))))

(defun adjoin-clause (clause clauses &key unsafe)
  (cond (unsafe
         (assert (not (any-covered-p clauses clause)))
         (push clause (store-clauses clauses)))
        ((not (any-covered-p clauses clause))
         (push clause (store-clauses clauses)))))

(defun unit-box-p (box instance)
  (declare (type box box)
           (type instance instance))
  (assert (= (length box) (length instance)))
  (every (lambda (spec length)
           (assert (<= (length spec) length))
           (= (length spec) length))
         box instance))

(defun split (goal instance)
  (declare (type box goal)
           (type instance instance))
  (assert (= (length goal) (length instance)))
  (let* ((split (dotimes (i (length goal) (error "Unable to split"))
                  (when (< (length (aref goal i)) (aref instance i))
                    (return i))))
         (left (copy-seq goal))
         (right (copy-seq goal)))
    (setf (aref left split)  (concatenate 'simple-bit-vector
                                          (aref left split) #*0)
          (aref right split) (concatenate 'simple-bit-vector
                                          (aref right split) #*1))
    (values left right)))

(defun tetris-skeleton (instance clauses goal)
  (declare (type instance instance)
           (type store clauses)
           (type box goal))
  (flet ((check (infeasible clause)
           (if (or (not infeasible) ;; success, this seems feasible
                   (covers-p clause goal)) ;; certified infeasible
               (return-from tetris-skeleton (values infeasible clause))
               clause)))
    (declare (dynamic-extent #'check))
    (let ((cover (any-covered-p clauses goal)))
      (when cover
        (return-from tetris-skeleton (values t cover))))
    (when (unit-box-p goal instance)
      (return-from tetris-skeleton (values nil goal)))
    (multiple-value-bind (left right)
        (split goal instance)
      (let ((w (resolve (multiple-value-call #'check
                          (tetris-skeleton instance clauses left))
                        (multiple-value-call #'check
                          (tetris-skeleton instance clauses right)))))
        (assert (covers-p w goal))
        (adjoin-clause w clauses :unsafe t)
        (values t w)))))

(defun bit-vector-to-integer (x)
  (declare (type simple-bit-vector x))
  (let ((acc 0))
    (map nil (lambda (bit)
               (setf acc (+ (* 2 acc) bit)))
         x)
    acc))

(defun integer-to-bit-vector (x width)
  (let ((acc (make-array width :element-type 'bit :initial-element 0)))
    (dotimes (i width acc)
      (setf (aref acc i) (if (logbitp i x) 1 0)))))

(defvar *current-solution*)

(defun conflict (&rest variables)
  (let ((ret (make-array (length *current-solution*) :initial-element #*)))
    (map nil (lambda (variable)
               (setf (aref ret variable) (aref *current-solution* variable)))
         variables)
    ret))

(defun listify (x)
  (if (listp x)
      x
      (list x)))

(defun tetris (instance certifier
               &key clauses enumerate)
  (let* ((instance (coerce instance 'instance))
         (clauses (or clauses (make-store)))
         (goal (make-array (length instance) :initial-element #*))
         (solutions '()))
    (loop
     (multiple-value-bind (infeasible witness)
         (tetris-skeleton instance clauses goal)
       (when infeasible
         (return (values (nreverse solutions) witness clauses)))
       (let* ((*current-solution* witness)
              (ok (funcall certifier (map 'simple-vector
                                          'bit-vector-to-integer
                                          witness))))
         (case ok
           ((t)
            (unless enumerate
              (return (values t witness clauses)))
            (adjoin-clause witness clauses)
            (push witness solutions))
           ((nil) (adjoin-clause witness clauses))
           (otherwise (dolist (clause (listify ok))
                        (adjoin-clause clause clauses)))))))))

(defun certify-all-diff (n indices)
  (lambda (solution)
    (let ((seen (make-array n :initial-element nil)))
      (dolist (index indices t)
        (let* ((x (aref solution index))
               (old (if (>= x n)
                        (return (conflict index))
                        (shiftf (aref seen x) index))))
          (when old
            (return (conflict old index))))))))

(defun certify-latin-square-row (row n)
  (certify-all-diff n
                    (loop for i below n
                          collect (+ (* row n) i))))

(defun certify-latin-square-column (column n)
  (certify-all-diff n
                    (loop for i below n
                          collect (+ column (* i n)))))

(defun certify-range (i low high)
  (lambda (solution)
    (let ((x (aref solution i)))
      (or (and (<= low x) (< x high))
          (conflict i)))))

(defun certify-conjunction (&rest conjunctions)
  (lambda (solution)
    (let ((all-ok t)
          (counters '()))
      (dolist (test conjunctions (or all-ok counters))
        (let ((result (funcall test solution)))
          (unless (eql result t)
            (setf all-ok nil
                  counters (append (listify result) counters))))))))

(defun certify-latin-square (n)
  (let ((tests '()))
    (dotimes (i (* n n))
      (push (certify-range i 0 n) tests))
    (dotimes (i n)
      (push (certify-latin-square-row i n) tests)
      (push (certify-latin-square-column i n) tests))
    (apply 'certify-conjunction (nreverse tests))))
