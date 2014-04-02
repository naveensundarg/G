(declaim (ftype function first-sat prove-int))



(defparameter *strageties* ())
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
 (if (fresh-MPWffs B)
       (let* ((foci (first (fresh-MPWffs B)))
	      (new-B (cons (cond-elim foci) B)))
	 (let ((remainder (Prove-Int new-B g) )) 
	   (if remainder  
	       (cons (proof-step :cond-elim (first foci) (second foci) )
		     remainder))))))


(define-strategy bicond-elim-left! (B g)
 (if (fresh-MPWffs B)
       (let* ((foci (first (fresh-MPWffs B)))
	      (new-B (cons (cond-elim foci) B)))
	 (let ((remainder (Prove-Int new-B g) )) 
	   (if remainder  
	       (cons (proof-step :cond-elim (first foci) (second foci) )
		     remainder))))))


(define-strategy inter-cond-goals! (B g)
   (if (first (igoals-mp B g))
       (let  ((i-mp (first (igoals-mp B g))))
	 (Join (Prove-int B (first (args i-mp)))
	       (proof-step :cond-elim   (second (args i-mp)))))))
 
(define-strategy reductio! (B g)
  (multiple-value-bind 
	(reductio-proof reductio-target)
      (try (lambda (red-target) 
	     (if (not (tried-reductio? (list g red-target)))
		 (let ((*oe-expanded* *oe-expanded*)
		       (*reductio-tried* *reductio-tried*))
		   (Prove-int
		    (remove-duplicates (cons (dual g) B) :test #'equalp)
		    (dual red-target))))) 
	   B)
    (Join
     (subproof  (dual g) reductio-proof)
     (proof-step :reductio reductio-target g))))

(defun complexity (f)
  (if (atom f)
      1
      (apply #'+ (mapcar #'complexity f))))

(complexity '(and (and a (if a b)) b))
(define-strategy all-reductio! (B g)
  (let ((subs (reduce #'append (mapcar #'subformulae  (cons g B)))))
    (if  (and  (not (member (dual  g) B :test #'equalp)))
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
(defun Prove (B g &optional (inner? nil))
  (let ((*seen* nil) 
	(*expanded* nil) 
	(*reductio-tried* nil)
	(*ae-expanded* nil)
	(*mp-expanded* nil)
	(*oe-expanded* nil))
    ;(push-problem (make-problem B g))
    (let ((proof (Prove-Int B g)))
     (clear-problem-stack) 
      (if (and proof (not inner?))
	  (list :Base B :Goal g
		proof)
	  proof))))



(defun log-step (s &optional (out t)) (print (concatenate 'string "" s) out))

(defmacro if* (test then &optional (else nil))
  `(let ((result ,test))
     (if result 
	 (progn 
	   (log-step
	    (concatenate 'string "branch on " (princ-to-string ,test)) ) ,then)
	 (progn 
	   (log-step (concatenate 'string "branch failed on " (princ-to-string ,test))) ,else))))

(defparameter *debug* nil)
 
(defun Prove-Int (B g)
  (if *debug* 
      (progn
	(let ((command (prompt-read (princ-to-string (list B :Goal g)))))
	  (cond ((equalp command "n")
		 (progn (format t "[quitting]") (return-from Prove-Int nil)))
		(t (format t "[>]") )))))
  (if (not (is-problem-in-stack? 
	    (make-problem 
	    B 
	     g)))
      (progn (push-problem (make-problem B g))
	     (let ((ans (or
			 (reiterate! B g)
			 (or-intro! B g)

			 (incons! B g)
			 (and-elim! B g)
			 (cond-elim! B g)
		;	 (bicond-elim! B g)

			 (bicond-intro! B g)
			 (cond-intro! B g)
			 (and-intro! B g)
			 (or-elim! B g)
			 (inter-cond-goals! B g)
			 (reductio! B g)
			 (all-reductio! B g))))
	       (if ans (remove-problem-from-stack (make-problem B g)))
	       ans))))
 


(defun abstract-prove (premises goal &optional (inner nil))
  (multiple-value-bind  (v f)  (abstract (cons :Whole (cons goal premises)))
    (subst (second (first f)) (first (first f)) (prove (rest (rest v)) (first (rest v))))))

(abstract-prove () '(or (and p q) (not (and p q))))