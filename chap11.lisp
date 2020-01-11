(defpackage :paip.chap11 (:use :cl :paip.chap6))
(in-package :paip.chap11)

(defun reuse-cons (x y x-y)
  "Returns (cons x y), or just x-y if it is equal to (cons x y)."
  (if (and (eql x (car x-y)) (eql y (cdr x-y)))
      x-y
      (cons x y)))


(defparameter *occurs-check* t "Should we do the occurs check?")

(defun unify (x y &optional (bindings no-bindings))
  "See if x and y match with given bindings."
  (cond ((eq bindings fail) fail)
        ((eql x y) bindings)
        ((variable-p x) (unify-variable x y bindings))
        ((variable-p y) (unify-variable y x bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
                (unify (first x) (first y) bindings)))
        (t fail)))

(defun unify-variable (var x bindings)
  "Unify var with x, using (and maybe extending) bindings."
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable-p x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        ((and *occurs-check* (occurs-check var x bindings))
         fail)
        (t (extend-bindings var x bindings))))

(defun occurs-check (var x bindings)
  "Does var occur anywhere inside x?"
  (cond ((eq var x) t)
        ((and (variable-p x) (get-binding x bindings))
         (occurs-check var (lookup x bindings) bindings))
        ((consp x) (or (occurs-check var (first x) bindings)
                       (occurs-check var (rest x) bindings)))
        (t nil)))

(defun subst-bindings (bindings x)
  "Substitute the value of variables in bindings into x,
  taking recursively bound variables into account."
  (cond ((eq bindings fail) fail)
        ((eq bindings no-bindings) x)
        ((and (variable-p x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

(defun unifier (x y)
  "Returns something that unifies with both x and y (or fail)."
  (subst-bindings (unify x y) x))

(defun lisp-member (item list)
  (and (consp list)
       (or (eql item (first list))
           (lisp-member item (rest list)))))

(defun clause-head (clause) (first clause))
(defun clause-body (clause) (rest clause))

(defun get-clauses (pred) (get pred 'clauses))
(defun predicate (relation) (first relation))

(defvar *db-predicates* nil
  "A list of all predicates stored in the database.")

(defmacro <- (&rest clause)
  "Add a clause to the cdata base."
  `(add-clause ',clause))

(defun add-clause (clause)
  "Add a clause to the data base, indexed by head's predicates."
  (let ((pred (predicate (clause-head clause))))
    (assert (and (symbolp pred) (not (variable-p pred))))
    (pushnew pred *db-predicates*)
    (setf (get pred 'clauses)
          (nconc (get-clauses pred) (list clause)))
    pred))

(defun clear-db ()
  "Remove all clauses (for all predicates) from the data base."
  (mapc #'clear-predicate *db-predicates*))

(defun clear-predicates (predicate)
  "Remove the clauses for a single predicate."
  (setf (get predicate 'clauses) nil))

(defun prove (goal bindings)
  "Return a list of possible solutions to goal."
  (mapcan (lambda (clause)
            (let ((new-clause (rename-variables clause)))
              (prove-all (clause-body new-clause)
                         (unify goal (clause-head new-clause)
                                     bindings))))
          (get-clauses (predicate goal))))


(defun prove-all (goals bindings)
  "Return a list of solutions to the conjunctuion of goals."
  (cond ((eq bindings fail) fail)
        ((null goals) (list bindings))
        (t (mapcan (lambda (goal1-solution)
                     (prove-all (rest goals) goal1-solution))
                   (prove (first goals) bindings)))))

(defun rename-variables (x)
  "Replace all variables in x with new ones."
  (sublis (mapcar (lambda (var) (cons var (gensym (string var))))
                  (variables-in x))
          x))

(defun variables-in (exp)
  "Return a list of all the variables in EXP."
  (unique-find-anywhere-if #'variable-p exp))

(defun unique-find-anywhere-if (predicate tree
                                &optional found-so-far)
  "Return a list of leaves of tree satisfying predicate,
with duplicates removed."
  (if (atom tree)
      (if (funcall predicate tree)
          (adjoin tree found-so-far)
          found-so-far)
      (unique-find-anywhere-if
       predicate
       (first tree)
       (unique-find-anywhere-if predicate (rest tree)
                                found-so-far))))

(defmacro ?- (&rest goals) `(prove-all ',goals no-bindings))

(progn
  (<- (likes Kim Robin))
  (<- (likes Sandy Lee))
  (<- (likes Sandy Kim))
  (<- (likes Robin cats))
  (<- (likes Sandy ?x) (likes ?x cats))
  (<- (likes Kim ?x) (likes ?x Lee) (likes ?x Lim))
  (<- (likes ?x ?x)))



;;;;
(defmacro ?- (&rest goals) `(top-level-prove ',goals))


(defun top-level-prove (goals)
  "Prove the goals, and print variables readably."
  (show-prolog-solutions
   (variables-in goals)
   (prove-all goals no-bindings)))

(defun show-prolog-solutions (vars solutions)
  "Print the variables in each of the solutions."
  (if (null solutions)
      (format t "~&No.")
      (mapc (lambda (solution) (show-prolog-vars vars solution))
            solutions))
  (values))

(defun show-prolog-vars (vars bindings)
  "Print each variable with its binding."
  (if (null vars)
      (format t "~&Yes.")
      (dolist (var vars)
        (format t "~&~a = ~a" var
                  (subst-bindings bindings var))))
  (princ ";"))


;;;
(defun prove-all (goals bindings)
  "Find a solution to the conjunction of goals."
  (cond ((eq bindings fail) fail)
        ((null goals) bindings)
        (t (prove (first goals) bindings (rest goals)))))

(defun prove (goal bindings other-goals)
  "Return al list of possible solutions to goal."
  (some (lambda (clause)
          (let ((new-clause (rename-variables clause)))
            (prove-all
             (append (clause-body new-clause) other-goals)
             (unify goal (clause-head new-clause) bindings))))
        (get-clauses (predicate goal))))

(defun prove (goal bindings other-goals)
  "Return al list of possible solutions to goal."
  (let ((clauses (get-clauses (predicate goal))))
    (if (listp clauses)
        (some (lambda (clause)
                (let ((new-clause (rename-variables clause)))
                  (prove-all
                   (append (clause-body new-clause) other-goals)
                   (unify goal (clause-head new-clause) bindings))))
              (get-clauses (predicate goal)))
        (funcall clauses (rest goal) bindings other-goals))))

(defun top-level-prove (goals)
  (prove-all `(,@goals (show-prolog-vars ,@(variables-in goals)))
             no-bindings)
  (format t "~&No.")
  (values))

(defun show-prolog-vars (vars bindings other-goals)
  "Print each variable with its binding.
The ask the user if more solutions are desired."
  (if (null vars)
      (format t "~&Yes")
      (dolist (var vars)
        (format t "~&~a = ~a" var
                  (subst-bindings bindings var))))
  (if (continue-p)
      fail
      (prove-all other-goals bindings)))

(setf (get 'show-prolog-vars 'clauses) 'show-prolog-vars)

(defun continue-p ()
  "Ask user if we should continue looking for solutions."
  (case (read-char)
    (#\; t)
    (#\. nil)
    (#\newline (continue-p))
    (t (format t " Type ; to see more or . to stop")
       (continue-p))))



