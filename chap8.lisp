(defpackage :paip.chap8
  (:use :cl :paip.chap6 :paip.chap7)
  (:shadow :paip.chap6 :variable-p))
(in-package :paip.chap8)

(defun infix->prefix (exp)
  "Translate an infix expresion into prefix notation."
  ;; Note we cannot do implicit multiplication in this system
  (cond ((atom exp) exp)
        ((= (length exp) 1) (infix->prefix (first exp)))
        ((paip.chap6::rule-based-translator exp *infix->prefix-rules*
           :rule-if #'rule-pattern :rule-then #'rule-response
           :action
           (lambda (bindings response)
             (sublis (mapcar
                      (lambda (pair)
                        (cons (first pair)
                              (infix->prefix (rest pair))))
                      bindings)
                     response))))
        ((symbolp (first exp))
         (list (first exp) (infix->prefix (rest exp))))
        (t (error "Illegal exp"))))

(dolist (sym '(?n ?m ?s)) (unintern sym))

(defun variable-p (exp)
  "Variables are the symbols M through Z."
  ;; put x,y,z first to find them a little faster
  (member exp '(x y z m n o p q r s t u v w)))

(paip.chap6::pat-match-abbrev 'x+ '(?+ x))
(paip.chap6::pat-match-abbrev 'y+ '(?+ y))


(defparameter *infix->prefix-rules*
  (mapcar #'paip.chap6::expand-pat-match-abbrev
    '(((x+ = y+) (= x y))
      ((- x+)     (- x))
      ((- y+)     (- y))
      ((x+ + y+)  (+ x y))
      ((x+ - y+)  (- x y))
      ((x+ * y+)  (* x y))
      ((x+ / y+)  (/ x y))
      ((x+ ^ y+)  (^ x y))))
  "A list of rules, ordered by precedence")

(defparameter *simplification-rules* (mapcar #'infix->prefix '(
  (x + 0 = x)
  (0 + x = x)
  (x + x = 2 * x)
  (x - 0 = x)
  (0 - x = - x)
  (x - x = 0)
  (- - x = x)
  (x * 1 = x)
  (1 * x = x)
  (x * 0 = x)
  (0 * x = 0)
  (x * x = x ^ 2)
  (x / 0 = undefined)
  (0 / x = 0)
  (x / 1 = x)
  (x / x = 1)
  (0 ^ 0 = undefined)
  (x ^ 0 = 1)
  (0 ^ x = 0)
  (1 ^ x = 1)
  (x ^ 1 = x)
  (x ^ -1 = 1 / x)
  (x * (y / x) = y)
  ((y / x) * x = y)
  ((y * x) / x = y)
  ((x * y) / x = y)
  (x + - x = 0)
  ((- x) + x = 0)
  (x + y - x = y))))

(defun ^ (x y) "Exponentiation" (expt x y))

(defun simplifier ()
  "Read a mathematial expression, simplify it, and print the result."
  (loop
    (print 'simplifier>)
    (print (simp (read)))))

(defun simp (inf) (prefix->infix (simplify (infix->prefix inf))))

(defun simplify (exp)
  "Simplify an expression by first simplifying its components."
  (if (atom exp) exp
      (simplify-exp (mapcar #'simplify exp))))

(defun simplify-exp (exp)
  "Simplify using a rule, or by doing arithmetic."
  (cond ((paip.chap6::rule-based-translator exp *simplification-rules*
          :rule-if #'exp-lhs :rule-then #'exp-rhs
          :action (lambda (bindings response)
                    (simplify (sublis bindings response)))))
        ((evaluable exp) (eval exp))
        (t exp)))

(defun evaluable (exp)
  "Is this an arithmetic expression that can be evaluated?"
  (and (every #'numberp (exp-args exp))
       (or (member (exp-op exp) '(+ - * /))
           (integerp (second (exp-args exp))))))

(paip.chap6::pat-match-abbrev '?n '(?is ?n numberp))
(paip.chap6::pat-match-abbrev '?m '(?is ?m numberp))
(paip.chap6::pat-match-abbrev '?s '(?is ?s not-numberp))

(defun not-numberp (x) (not (numberp x)))

(defun simp-rule (rule)
  "Transform a rule into proper format."
  (let ((exp (infix->prefix rule)))
    (mkexp (paip.chap6::expand-pat-match-abbrev (exp-lhs exp))
           (exp-op exp) (exp-rhs exp))))

(setf *simplification-rules*
  (append *simplification-rules* (mapcar #'simp-rule
     '((?s * ?n = ?n * ?s)
       (?n * (?m * x) = (?n * ?m) * x)
       (x * (?n * y) = ?n * (x * y))
       ((?n * x) * y = ?n * (x * y))
       (?n + ?s = ?s + ?n)
       ((x + ?m) + ?n = x + ?n + ?m)
       (x + (y + ?n) = (x + y) + ?n)
       ((x + ?n) + y = (x + y) + ?n)))))
