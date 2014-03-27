

(defparameter *prop-nd-test-1*
    '((P) P))

(defparameter *prop-nd-test-2*
    '((P Q) P))

(defparameter *prop-nd-test-3*
    '(() (implies P P)))


(defparameter *prop-nd-test-4*
  '(() (implies P (implies Q P))))

(defparameter *prop-nd-test-5*
  '((P Q ) (and P Q)))

(defparameter *prop-nd-test-6*
  '((P Q R) (and (and R Q) R)))

(defparameter *prop-nd-test-7*
  '((Q) (implies P (and Q P))))

(defparameter *prop-nd-test-8*
  '((Q R) (implies P (and R (and Q P)))))

(defparameter *prop-nd-test-9*
  (list (list '(and P Q))
	'P))

(defparameter *prop-nd-test-10*
  (list (list '(and P (and Q R)) 'U 'V)
	'(and R (and U V))))

(defparameter *prop-nd-test-11*
  (list (list '(or P Q))
	'(or Q P)))

(defparameter *prop-nd-test-12*
  (list (list '(or P (or Q R)))
	'(or (or R Q) P)))

(defparameter *prop-nd-test-13*
  (list (list '(not (or p q)))
	'(not p)))

;; DeMorgan's 1 (14 and 15)
(defparameter *prop-nd-test-14*
  (list (list '(not (or p q))) 
	'(and (not p) (not q))))

(defparameter *prop-nd-test-15*
  (list (list'(and (not p) (not q))) '(not (or p q))))

(defparameter *prop-nd-test-16*
  (list (list '(not (or (not P) Q))) 'P))



;;; Problems from ITL

(defparameter *prop-nd-test-17* 
  (list  (list '(implies H (and E D))
		 '(implies (or E My) R)
		 '(implies Ma (not R)))
	'(implies H (not Ma))))

(defun range (a b) (loop for i from a to b collect i))

(defparameter *prop-nd-tests* 
  (let ((total-tests 16))
    (mapcar (lambda (n)
	      (eval 
	       (read-from-string 
		(concatenate 'string 
			     "*prop-nd-test-"
			     (princ-to-string n)
			     "*"))))
	    (range 1 total-tests))))


(defun run-tests ()
  (let ((count 1))
    (mapcar (lambda (test-case) 
	      (format t "Running test on case ~a:~a ~%      Passed? ~a~% " 
		      count test-case (if (null (apply #'Prove test-case)) "NO!" "Yes."))
	      (incf count) (values))
	    *prop-nd-tests*)))

(run-tests)
