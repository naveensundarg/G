(declaim (ftype function first-sat prove-int))

(defparameter *solved* ())
(defparameter *interactive* nil)
(defparameter *proof-depth* 0)
(defparameter *line-number* 0)


(defparameter *strageties* ())
(defparameter *strategy-stack* ())

(defmacro define-strategy (name args &rest body)
   `(push ,name *strageties* )
  `(defun ,name ,args ,@body))

(defmacro trace-prover (&optional (strategy nil))
  `(if ,strategy
       (trace ,strategy)
       (progn ,@(mapcar (lambda (s) (list 'trace s)) *strageties*))))

(define-strategy incons! (B g)
  (if (inconsistent-pair B) 
       (proof-step :incons (inconsistent-pair B) g)))

(define-strategy reiterate! (B g)
  (if (can-reiterate? B g) (list (proof-step :reiterate  g)) nil))

(define-strategy cond-intro! (B g)
    (if (is-conditional? g) 
	(destructuring-bind 
	      (conn p q) g  (declare (ignore conn))
	      (Join 
	       (subproof p (Prove-Int (cons p B) q)) 
		    (proof-step :cond-intro (list :discharges p) g)))))

(define-strategy bicond-intro! (B g)
    (if (is-biconditional? g) 
	(destructuring-bind 
	      (conn p q) g  (declare (ignore conn))
	      (Join (Join 
		     (subproof p (let ((*ae-expanded* *ae-expanded*)
				       (*oe-expanded* *oe-expanded*)
				       (*reductio-tried* *reductio-tried*))
				   (Prove-Int (cons p B) q))) 
		     (proof-step :cond-intro (list :discharges p) g))
		    (Join 
		     (subproof q (let ((*ae-expanded* *ae-expanded*)
 				       (*oe-expanded* *oe-expanded*)
				       (*reductio-tried* *reductio-tried*))
				   (Prove-Int (cons q B) p))) 
		     (proof-step :cond-intro (list :discharges q) g))))))

(define-strategy and-intro! (B g)
   (if (is-conjunction? g) 
       (destructuring-bind 
	     (conn p q) g  (declare (ignore conn))
	     (Join (let ((*reductio-tried* *reductio-tried*) (*oe-expanded* *oe-expanded*)) 
		     (Prove-int B p))
		   (let ((*reductio-tried* *reductio-tried*) (*oe-expanded* *oe-expanded*)) 
		     (Prove-int B q )) 
		   (proof-step :&-intro (list p q) g)))))

(define-strategy and-elim! (B g)
  (if (fresh-AEWffs B) 
       (let* ((*ae-expanded* *ae-expanded*)
	      (focus (first (fresh-AEWffs B)) )
	      (new-B (append (and-elim focus) B)))
	 (let ((remainder (Prove-Int new-B g))) 
	   (if remainder
	       (cons (proof-step :&-elim focus (and-elim focus))
		    remainder))))))

(define-strategy or-intro! (B g)
  (if (is-disjunction? g) 
       (destructuring-bind 
	     (conn p q) g (declare (ignore conn))
	     (let ((remainder (or (let ((*oe-expanded* *oe-expanded*)(*reductio-tried* *reductio-tried*))
				    (Prove-int B p))
				  (let ((*oe-expanded* *oe-expanded*)(*reductio-tried* *reductio-tried*)) 
				    (Prove-int B q)))))
	       (if remainder
		   (append remainder (list (proof-step :v-intro g))))))))

(define-strategy or-elim! (B g)
 (if (fresh-OEWffs B)
       (let* ((*oe-expanded* *oe-expanded*)
	      (focus (first (fresh-OEWffs B)) )
	      (new-B-left  (cons (first  (or-elim focus)) B))
	      (new-B-right (cons (second (or-elim focus)) B)))
	 (let 
	     ((remainder-1 (let ((*oe-expanded* *oe-expanded*)) 
			     (Prove-int new-B-left g)))
	      (remainder-2 (let ((*oe-expanded* *oe-expanded*)) 
			     (Prove-int new-B-right g))))
	   (Join 
	    (subproof (first (or-elim focus)) remainder-1) (subproof (second (or-elim focus)) remainder-2)
	    (list (proof-step :v-elim  focus g)))))))

(define-strategy cond-elim! (B g)
  (let* ((fresh (fresh-MPWffs B))
	 (foci (first fresh))
	 (new-B (cons (cond-elim foci) B)))
    (if fresh
	(let ((remainder (Prove-Int new-B g) )) 
	  (if remainder  
	      (cons (proof-step :cond-elim (first foci) (second foci) )
		    remainder))))))


(define-strategy bicond-elim! (B g)
  (let* ((fresh (fresh-bicon-elim-Wffs B))
	 (foci (first fresh))
	 (new-B (cons (bicond-elim foci) B)))
    (if fresh 
	(let ((remainder (Prove-Int new-B g))) 
	  (if remainder  
	      (cons (proof-step :bicond-elim (first foci) (second foci) )
		    remainder))))))

(define-strategy bicond-elim-left! (B g)
 (if (fresh-MPWffs B)
       (let* ((foci (first (fresh-MPWffs B)))
	      (new-B (cons (cond-elim foci) B)))
	 (let ((remainder (Prove-Int new-B g) )) 
	   (if remainder  
	       (cons (proof-step :bicond-elim (first foci) (second foci) )
		     remainder))))))


(define-strategy inter-cond-goals! (B g)
   (if (first (igoals-mp B g))
       (let  ((i-mp (first (igoals-mp B g))))
	 (Join (Prove-int B (first (args i-mp)))
	       (proof-step :cond-elim   (second (args i-mp)))))))
 

(define-strategy inter-bicond-goals! (B g)
   (if (first (igoals-bicond-elim B g))
       (let  ((i-bicond  (first (igoals-bicond-elim B g))))
	 (or  (Join  
		    (Prove-int B (first (set-difference (args i-bicond) (list g) :test #'equal)))
		    (proof-step :bicond-elim  g))
	      (Join 
		    (Prove-int B (second (set-difference (args i-bicond) (list g) :test #'equal)))
		    (proof-step :bicond-elim  g))))))

(define-strategy reductio! (B g)
  (multiple-value-bind 
	(reductio-proof reductio-target)
      (try (lambda (red-target) 
	     (if (not (tried-reductio? (list g red-target)))
		 (let ((*oe-expanded* *oe-expanded*)
		       (*reductio-tried* *reductio-tried*))
		   (Prove-int
		    (remove-duplicates (cons (dual g) B) :test #'equal)
		    (dual red-target))))) 
	   B)
    (Join
     (subproof  (dual g) reductio-proof)
     (proof-step :reductio reductio-target g))))



(define-strategy all-reductio! (B g)
  (let ((subs (reduce #'append (mapcar #'subformulae  (cons g B)))))
    (if  (and  (not (member (dual  g) B :test #'equal)))
	(apply #'Any (mapcar (lambda (s) 
			       (if  (and
				     (not (tried-reductio?   g))) 
				   (Join
				    (subproof (dual g)  
					      (Join 			       
					       (let ( (*oe-expanded* *oe-expanded*)(*reductio-tried* *reductio-tried*)) 
						 (Prove-int (cons (dual g) B) s))
					       (let ( (*oe-expanded* *oe-expanded*)(*reductio-tried* *reductio-tried*)) 
						 (Prove-int (cons (dual g) B) (dual s)))))
				    (proof-step :reductio g))))
			     subs)))))



;;; Note: Here we have the linear style of natural deduction.
;;; This differs from the graphical style of natural deduction show in 
;;; Slate and other systems. 
(defun simple-prove (B g &optional (inner? nil))
  (catch 'out 
    (unwind-protect 
	 (let ((*solved* nil)
	       (*seen* nil) 
	       (*expanded* nil) 
	       (*reductio-tried* nil)
	       (*ae-expanded* nil)
	       (*bicon-elim-expanded* nil)
	       (*mp-expanded* nil)
	       (*oe-expanded* nil)
	       (*proof-depth* 0)
	       (*line-number* 0)
	       (*strategy-stack* ()))
	   (if *interactive*
	       (print-interactive-banner))
	   (let ((proof (Prove-Int (sort B (lambda (x y) (< (complexity x) (complexity y)))) g)))
	     (clear-problem-stack) 
	     (if (and proof (not inner?))
		 (list :Base B :Goal g
		       proof)
		 proof))))))



(defun log-step (s &optional (out t)) (print (concatenate 'string "" s) out))

(defmacro if* (test then &optional (else nil))
  `(let ((result ,test))
     (if result 
	 (progn 
	   (log-step
	    (concatenate 'string "branch on " (princ-to-string ,test)) ) ,then)
	 (progn 
	   (log-step (concatenate 'string "branch failed on " (princ-to-string ,test))) ,else))))

 

(defun already-solved? (problem)
  (first (last (first-sat (lambda (x) (if (subsumes? problem (first (butlast x)) )
					   t
					   nil))
			   *solved*))))


(defun str* (base n) 
  (let ((str "")) 
    (loop for i from 1 to n do 
	 (setf str (concatenate 'string str base)))
    str))


(defun print-interactive-banner () 
  (format t (concatenate 'string (str* "-" 90) 
			 "~%[c: CONTINUE; q: GLOABL QUIT; n: LOCAL QUIT; p: ORACLE PROOF (YES); d: ORACLE PROOF (NO)]~%" (str* "-" 90) "~%")))

(defun interactive-interface (B g)
  (let ((command (prompt-read 
		  (concatenate 'string 
			       (princ-to-string *line-number*) 
			       ":" (str* "[>]" *proof-depth*)
			       "["(princ-to-string (first *strategy-stack*)) "]"
			       (princ-to-string (list B :Goal g))))))
    (cond ((equal command "c") (setf *interactive* nil))
	  ((equal command "n") :n)
	  ((equal command "q") (throw 'out nil))
	  ((equal command "p") :p)
	  ((equal command "d") :d))))

(defun Prove-Int (B g)
  (if *interactive* 
      (let ((command (interactive-interface B g)))
	(cond ((eql :n command)(return-from Prove-int))
	      ((eql :p command)(return-from Prove-int (proof-step :oracle g)))
	      ((eql :d command)(return-from Prove-int nil)))))
  (incf *line-number*) 
  (let* ((problem (make-problem B g)) 
	 (cached? (already-solved? problem)))
    (or cached?
	(if (not (is-problem-in-stack? problem))
	    (progn (push-problem problem)
		   (incf *proof-depth*)
		   (let ((ans 
			  (multiple-value-bind
				(prob_ proof)
			      (first-sat 
			       (lambda (strategy) 
				 (push strategy *strategy-stack*)
				 (let ((this-ans (apply strategy (list B g))))
				   (push strategy *strategy-stack*)
				   this-ans))
			       '(reiterate!
				 or-intro! 
				 incons! 
				 and-elim!
				 cond-elim!
				 bicond-elim!
				 bicond-intro!
				 cond-intro!
				 and-intro!
				 or-elim!
				 inter-cond-goals!
				 inter-bicond-goals!
				 reductio!
				 all-reductio!))
			    (declare (ignore prob_))
			    proof)))
		     (decf *proof-depth*)
		     (if ans (progn
			       (push (list (make-problem B g) ans) *solved*)
			       (remove-problem-from-stack (make-problem B g))))
		     ans))))))
 


(defun prove (premises goal &optional (interactive nil))
  (let ((*interactive* interactive))
      (multiple-value-bind  (v f)  (abstract (cons :Whole (cons goal premises)))
	(subst (second (first f)) (first (first f)) (simple-prove (rest (rest v)) (first (rest v)))))))

;(abstract-prove () '(or (and p q) (not (and p q))))