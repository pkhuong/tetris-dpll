(defstruct node
  value left right)

(defstruct store
  node
  list)

(defmethod print-object ((object store) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (format stream "~D ~S"
            (length (store-list object))
            (store-list object))))

(defun lookup-2 (node value depth continuation)
  (declare (type (or node null) node)
           (type simple-bit-vector value)
           (type (and unsigned-byte fixnum) depth))
  (when (null node)
    (return-from lookup-2))
  (when (node-value node)
    (funcall continuation (node-value node)))
  (when (< depth (length value))
    (lookup-2 (if (zerop (aref value depth))
                  (node-left node)
                  (node-right node))
              value
              (1+ depth)
              continuation)))

(defun lookup-1 (node values i continuation)
  (declare (type (simple-array simple-bit-vector 1) values)
           (type (and unsigned-byte) i))
  (if (< i (length values))
      (lookup-2 node (aref values i) 0
                (lambda (node)
                  (lookup-1 node values (1+ i) continuation)))
      (funcall continuation node)))

(defun lookup (store values)
  (check-type store store)
  (check-type values (simple-array simple-bit-vector 1))
  (assert (every #'simple-bit-vector-p values))
  (lookup-1 (store-node store) values 0
            (lambda (clause)
              (when clause
                (return-from lookup clause)))))

(defun insert-2 (node value depth continuation)
  (declare (type (or null node) node)
           (type simple-bit-vector value)
           (type (and unsigned-byte fixnum) depth))
  (let ((node (or node (make-node))))
    (cond ((>= depth (length value))
           (setf (node-value node)
                 (funcall continuation (node-value node))))
          ((zerop (aref value depth))
           (setf (node-left node)
                 (insert-2 (node-left node) value (1+ depth) continuation)))
          (t
           (setf (node-right node)
                 (insert-2 (node-right node) value (1+ depth) continuation))))
    node))

(defun insert-1 (node values i continuation)
  (declare (type (simple-array simple-bit-vector 1) values)
           (type (and unsigned-byte) i))
  (cond ((< i (length values))
         (let ((node (or node (make-node))))
           (insert-2 node (aref values i) 0
                     (lambda (node)
                       (insert-1 node values (1+ i) continuation)))
           node))
        ((null node)
         (funcall continuation t)
         values)
        (t
         (assert (= (length node) (length values)))
         (assert (every #'equal node values))
         (funcall continuation nil)
         node)))

(defun insert (store values)
  (check-type store store)
  (check-type values (simple-array simple-bit-vector 1))
  (assert (every #'simple-bit-vector-p values))
  (let ((stored nil))
    (setf (store-node store) (insert-1 (store-node store)
                                       values 0
                                       (lambda (x)
                                         (setf stored x))))
    (when stored
      (push values (store-list store)))
    stored))
