;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Completeness Tests ;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *prop-nd-true-test-1*
    '((P) P))

(defparameter *prop-nd-true-test-2*
    '((P Q) P))

(defparameter *prop-nd-true-test-3*
    '(() (implies P P)))


(defparameter *prop-nd-true-test-4*
  '(() (implies P (implies Q P))))

(defparameter *prop-nd-true-test-5*
  '((P Q ) (and P Q)))

(defparameter *prop-nd-true-test-6*
  '((P Q R) (and (and R Q) R)))

(defparameter *prop-nd-true-test-7*
  '((Q) (implies P (and Q P))))

(defparameter *prop-nd-true-test-8*
  '((Q R) (implies P (and R (and Q P)))))

(defparameter *prop-nd-true-test-9*
  (list (list '(and P Q))
	'P))

(defparameter *prop-nd-true-test-10*
  (list (list '(and P (and Q R)) 'U 'V)
	'(and R (and U V))))

(defparameter *prop-nd-true-test-11*
  (list (list '(or P Q))
	'(or Q P)))

(defparameter *prop-nd-true-test-12*
  (list (list '(or P (or Q R)))
	'(or (or R Q) P)))

(defparameter *prop-nd-true-test-13*
  (list (list '(not (or p q)))
	'(not p)))

;; DeMorgan's 1 (14 and 15)
(defparameter *prop-nd-true-test-14*
  (list (list '(not (or p q))) 
	'(and (not p) (not q))))

(defparameter *prop-nd-true-test-15*
  (list (list'(and (not p) (not q))) '(not (or p q))))

(defparameter *prop-nd-true-test-16*
  (list (list '(not (or (not P) Q))) 'P))

;;; Problems from ITL

(defparameter *prop-nd-true-test-17* 
  (list  (list '(implies H (and E D))
		 '(implies (or E My) R)
		 '(implies Ma (not R)))
	'(implies H (not Ma)))
  "kok_o213_8_32")

(defparameter *prop-nd-true-test-18* 
  (list (list '(implies (not Cube_b) Small_b)
	      '(implies Small_c (or Small_d Small_e))
	      '(implies Small_d (not Small_c))
	      '(implies Cube_b (not Small_e)))
	'(implies Small_c Small_b))
  "kok_o213_8_35")

(defparameter *prop-nd-true-test-19* 
    (list  (list '(and Small_a (or Medium_b Large_c))
			'(implies Medium_b Front_Of_a_b)
			'(implies Large_c Tet_c))
	  '(implies (not Tet_c) Front_Of_a_b))
  "kok_o223_8_48")

(defparameter *prop-nd-true-test-20*  
  (list () '(iff (and A (not B))
	     (not (implies A B)))))


(defparameter *prop-nd-true-test-21*  
  (list () '(or P (not P))))


(defparameter *prop-nd-true-test-22*
  (list ()
	'(implies P (implies Q P))))

;;; problems from "Seventy-five problems for testing ATP."
(defparameter *prop-nd-true-test-23* 
  (list () '(iff (implies p q) (implies (not q) (not p))))
  "1")

(defparameter *prop-nd-true-test-24* 
  (list () '(iff  (not (not p)) p))
  "2")


(defparameter *prop-nd-true-test-25* 
  (list () '(implies (not (implies p q))
	     (implies q p)))
  "3")


(defparameter *prop-nd-true-test-26* 
  (list () '(iff  (implies (not p) q)
	     (implies (not q) p)))
  "4")

(defparameter *prop-nd-true-test-27* 
  (list () '(implies (implies (or p q) (or p r))
	     (or p (implies q r))))
  "5")

(defparameter *prop-nd-true-test-28*
    (list ()
	   '(or P (not (not (not P)))))
  "7")

(defparameter *prop-nd-true-test-29*
  (list ()
	 '(implies (implies (implies p q) p) p))
  "8 (Peirce's Law)")


(defparameter *prop-nd-true-test-30*
  (list ()
	'(implies (and (and (or p q) (or (not p) q)) (or p (not q)))
	  (not (or (not p) (not q)))))
  "Problem 9")


(defparameter *prop-nd-true-test-31* (list (list '(implies q r)
			     '(implies r (and p q))
			     '(implies p (or q r)))
		       '(implies p q))
  "Problem 10")


(defparameter *prop-nd-true-test-32*
  (list () '(iff p p))
  "Problem 11")


(defparameter *prop-nd-true-test-33*
  (list () '(iff (iff (iff p q) r)
		     (iff p (iff q r))))
  "Problem 12")


(defparameter *prop-nd-true-test-34*
  (list () 
	'(iff (or p (and q r))
	  (and (or p q) (or p r)))))


(defparameter *prop-nd-true-test-35*
  (list ()
	'(implies (implies p (not p)) (implies p q))))


(defparameter *prop-nd-true-test-36*  
    (list (list 'p 
		'(implies p (and w e))
		'(implies e (and q  (and r s))))
	  'r)
  "testing chaining")


(defparameter *prop-nd-true-test-37*   
  (list 
   (list  '(implies (or p (not p)) (and w e)) '(implies e (and q  (and r s))))
   'r)
  "testing chaining with a theorem at the start.")


(defparameter *prop-nd-true-test-38*   
  (list 
   ()
   '(or (implies p (implies q r))
     (not (implies p (implies q r)))))
  "complex instantiation of a simple theorem.")

(defparameter *prop-nd-true-test-39*   
  (list 
   (list  '(implies (or p (not p)) (and w e)) '(implies e (and q  (and r s))))
   'r)
  "testing chaining with a theorem at the start.")


(defparameter *prop-nd-true-test-40* 
  (list () '(not (and p (not P))))
  "Negation of a contradiction")

(defparameter *prop-nd-true-test-41* 
  (list (list '(not (or p (not p)))) 'z)
  "Negation of a theorem leads to explosion")

(defparameter *prop-nd-true-test-42* 
  (list (list '(not (or p (not p)))) '(or p q))
  "Negation of a theorem leads to explosion")


(defparameter *prop-nd-true-test-43* 
  (list NIL '(implies (implies (implies P Q) R) (implies P (implies Q R)))))

(defparameter *prop-nd-true-test-44*
  (list NIL '(iff (iff P Q) (iff Q P))))

(defparameter *prop-nd-true-test-45*
  (list (list '(iff p (and q r)) '(iff q (and a b))) '(implies p a))
  "Biconditional chaining.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Soundness Tests ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *prop-nd-false-test-1*   
  (list 
   ()
   'p))

(defparameter *prop-nd-false-test-2*   
  (list 
   (list '(or p q))
   'p))

(defparameter *prop-nd-false-test-3*   
  (list 
   (list '(and p q))
   'r))

(defparameter *prop-nd-false-test-4*   
  (list 
   (list '(implies p q))
   'p))

(defparameter *prop-nd-false-test-5*   
  (list 
   (list '(implies p q))
   'q))


(defparameter *prop-nd-false-test-6*   
  (list 
   (list '(implies p q))
   '(not (or p (not q)))))


(defparameter *prop-nd-false-test-7*   
  (list 
   (list '(implies p q) '(not (not (or p (not q)))))
   '(not (or p (not q)))))

(defparameter *prop-nd-false-test-8* 
  (list () '(and p (not P))))

(defparameter *prop-nd-false-test-9*
 (list () '(not (not (and p (not P))))))

(defparameter *prop-nd-false-test-10*
 (list () '(implies p (not p))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun range (a b) (loop for i from a to b collect i))

(defparameter *prop-nd-true-test-ignores* (list 33))


(defparameter *prop-nd-false-test-ignores* nil)

(defparameter *prop-nd-true-tests* 
  (let ((total-tests 44))
    (mapcar (lambda (n)
	      (eval 
	       (read-from-string 
		(concatenate 'string 
			     "*prop-nd-true-test-"
			     (princ-to-string n)
			     "*"))))
	    (range 1 total-tests))))


(defparameter *prop-nd-false-tests* 
  (let ((total-tests 10))
    (mapcar (lambda (n)
	      (eval 
	       (read-from-string 
		(concatenate 'string 
			     "*prop-nd-false-test-"
			     (princ-to-string n)
			     "*"))))
	    (range 1 total-tests))))


(defun run-tests (type &optional (str nil))
  (let ((count 0)
	(passed 0)
	(failure-check (if (eq type :completeness) #'null (complement #'null)))
	(ignores-list (if (eq type :completeness) *prop-nd-true-test-ignores* *prop-nd-false-test-ignores*)))
    (mapcar (lambda (test-case) 
	      (if (not (member (1+ count) ignores-list))
		  (let ((result (apply #'abstract-prove test-case)))
		    (format str " Running test on case ~a:  Passed? ~a~%" 
				  (1+ count)  
				  (if (funcall failure-check result)
				      "NO!" 
				      (progn (incf passed) "Yes.")))
		    (force-output str)
		    (incf count))
		  (progn (format str "  [   Ignoring test case ~a]~%" 
				 (1+ count))
			 (force-output str)
			 (incf count))))
	    (if (eq type :completeness) *prop-nd-true-tests* *prop-nd-false-tests*))
   (format t "~% Total Passed ~a out of ~a." passed (- count (length ignores-list)))
   (format t "~% Ignored ~a" (length ignores-list))
   (force-output t)))

(defun run-all-tests (&optional (verbose nil))
  (format t "~% --- RUNNING TESTS FOR COMPLETENESS --- ~%" )
  (force-output t)
  (time (run-tests :completeness verbose))
  (format t "~% --- RUNNING TESTS FOR SOUNDESS  --- ~%" )
  (time (run-tests :soundness verbose))
  (force-output t))



;;;;;; Soundness checks