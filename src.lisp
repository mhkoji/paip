
(defconstant fail nil)

(defstruct (path (:print-function print-path))
  state (previous nil) (cost-so-far 0) (total-cost 0))

(defun print-path (path &optional (stream t) depth)
  (declare (ignore depth))
  (format stream "#<Path to ~a cost ~,1f>"
          (path-state path) (path-total-cost path)))

(defun a*-search (paths goal-p successors cost-fn cost-left-fn
                  &optional (state= #'eq) old-paths)
  (format t ";; Search: ~a~%" paths)
  (cond
    ((null paths) fail)
    ((funcall goal-p (path-state (first paths)))
     (values (first paths) paths))
    (t (let* ((path (pop paths))
              (state (path-state path)))
         ;; Update PATHS and OLD-PATHs to reflect
         ;; the new successors of STATE:
         (setf old-paths (insert-path path old-paths))
         (dolist (state2 (funcall successors state))
           (let* ((cost (+ (path-cost-so-far path)
                           (funcall cost-fn state state2)))
                  (cost2 (funcall cost-left-fn state2))
                  (path2 (make-path
                           :state state2 :previous path
                           :cost-so-far cost
                           :total-cost (+ cost cost2)))
                  (old nil))
             ;; Place the new path, path2, in the right list:
             (cond
               ((setf old (find-path state2 paths state=))
                (when (better-path path2 old)
                  (setf paths (insert-path
                                path2 (delete old paths)))))
               ((setf old (find-path state2 old-paths state=))
                (when (better-path path2 old)
                  (setf paths (insert-path path2 paths))
                  (setf old-paths (delete old old-paths))))
               (t (setf paths (insert-path path2 paths))))))
         ;; Finally, call A* again with the updated path list:
         (a*-search paths goal-p successors cost-fn cost-left-fn
                    state= old-paths)))))

(defun find-path (state paths state=)
  (find state paths :key #'path-state :test state=))

(defun better-path (path1 path2)
  (< (path-total-cost path1) (path-total-cost path2)))

(defun insert-path (path paths)
  (merge 'list (list path) paths #'< :key #'path-total-cost))

(defun path-states (path)
  (if (null path)
      nil
      (cons (path-state path)
            (path-states (path-previous path)))))


(defun next2 (x) (list (+ x 1) (+ x 2)))

(defun is (value &key (key #'identity) (test #'eql))
  #'(lambda (path) (funcall test value (funcall key path))))

(defun diff (num)
  (lambda (x) (abs (- x num))))

#+nil
(a*-search (list (make-path :state 1)) (is 6)
           #'next2 (lambda (x y) (declare (ignore x y)) 1) (diff 6))
