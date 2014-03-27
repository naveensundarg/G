

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
	'(implies H (not Ma)))
  "kok_o213_8_32")

(defparameter *prop-nd-test-18* 
  (list (list '(implies (not Cube_b) Small_b)
	      '(implies Small_c (or Small_d Small_e))
	      '(implies Small_d (not Small_c))
	      '(implies Cube_b (not Small_e)))
	'(implies Small_c Small_b))
  "kok_o213_8_35")

(defparameter *prop-nd-test-19* 
    (list  (list '(and Small_a (or Medium_b Large_c))
			'(implies Medium_b Front_Of_a_b)
			'(implies Large_c Tet_c))
	  '(implies (not Tet_c) Front_Of_a_b))
  "kok_o223_8_48")

(defparameter *prop-nd-test-20*  
  (list () '(iff (and A (not B))
	     (not (implies A B)))))

(defun range (a b) (loop for i from a to b collect i))

(defparameter *prop-nd-tests* 
  (let ((total-tests 20))
    (mapcar (lambda (n)
	      (eval 
	       (read-from-string 
		(concatenate 'string 
			     "*prop-nd-test-"
			     (princ-to-string n)
			     "*"))))
	    (range 1 total-tests))))


(defun run-tests ()
  (let ((count 0)
	(passed 0))
    (mapcar (lambda (test-case) 
	      (format t "Running test on case ~a:~a ~%      Passed? ~a~% " 
		      (1+ count) test-case (if (null (apply #'Prove test-case)) "NO!" (progn (incf passed) "Yes.")))
	      (incf count) (values))
	    *prop-nd-tests*)
    (format t "~% Total Passed ~a out of ~a." passed count)))

(run-tests)
