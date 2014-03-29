
(defparameter *seen* nil)
(defparameter *expanded* nil)
(defparameter *ae-expanded* nil)
(defparameter *oe-expanded* nil)
(defparameter *mp-expanded* nil)
(defparameter *reductio-tried* nil)

(defun prompt-read (prompt)
  (format *query-io* "~a: " prompt)
  (force-output *query-io*)
  (read-line *query-io*))


(defparameter *problem-stack* nil)

(defun make-problem (premises goal) (list premises goal))
(defun premises (problem) (first problem))
(defun goal (problem) (second problem))

(defun compress (problem)
  (let ((premises (first problem))
	(goal (second problem)))
    (list (remove-duplicates premises :test #'equalp) goal)))

(defun push-problem (p) (push (compress p) *problem-stack*))

(defun subsumes? (P1 P2)
  (let ((premises1 (premises P1))
	(premises2 (premises P2))
	(goal1 (goal P1))
	(goal2 (goal P2)))
    (and (equalp goal1 goal2)
	 (subsetp (remove-duplicates premises2 :test #'equalp) premises1))))

(defun is-problem-in-stack? (p) (some (complement #'null)
				      (mapcar (lambda (x)
						(if (subsumes? x p) t nil))  
					      *problem-stack* )))

(defun clear-problem-stack () (setf *problem-stack* nil))

(defun remove-problem-from-stack (p)
  (setf *problem-stack*  (remove nil (mapcar (lambda (x)
					       (if (subsumes? x p) nil x))  
					     *problem-stack*))))

(defparameter *strageties* ())
(defmacro define-strategy (name args &rest body)
  (push name *strageties* )
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
		     (subproof p (Prove-Int (cons p B) q)) 
		     (proof-step :cond-intro (list :discharges p) g))
		    (Join 
		     (subproof q (Prove-Int (cons q B) p)) 
		     (proof-step :cond-intro (list :discharges q) g))))))

(define-strategy and-intro! (B g)
   (if (is-conjunction? g) 
       (destructuring-bind 
	     (conn p q) g  (declare (ignore conn))
	     (Join (let ( (*seen* nil) 
			 (*expanded* nil) 
			  (*reductio-tried* nil)
			  (*ae-expanded* nil)
			  (*mp-expanded* nil)
			  (*oe-expanded* nil))(Prove-int B p ))
		   (let
		       ( (*seen* nil) 
			(*expanded* nil) 
			 (*reductio-tried* nil)
			 (*ae-expanded* nil)
			 (*mp-expanded* nil)
			 (*oe-expanded* nil))
		     (Prove-int B q )) 
		   (proof-step :&-intro (list p q) g)))))

(define-strategy and-elim! (B g)
  (if (fresh-AEWffs B) 
       (let* ((*ae-expanded* *ae-expanded*)
	      (focus (first (fresh-AEWffs B)) )
	      (new-B (append (and-elim focus) B)))
	 (let ((remainder  (Prove-Int new-B g))) 
	   (if remainder
	       (cons (proof-step :&-elim focus (and-elim focus))
		    remainder))))))

(define-strategy or-intro! (B g)
  (if (is-disjunction? g) 
       (destructuring-bind 
	     (conn p q) g  (declare (ignore conn))
	     (let ((remainder (or (Prove-int B p)
				   (Prove-int B q))))
	       (if remainder
		   (append remainder (list (proof-step :v-intro g))
			 ))))))

(define-strategy or-elim! (B g)
 (if (fresh-OEWffs B)
       (let* ((*oe-expanded* *oe-expanded*)
	      (focus (first (fresh-OEWffs B)) )
	      (new-B-left  (cons (first  (or-elim focus)) B))
	      (new-B-right (cons (second (or-elim focus)) B)))
	 (let 
	     ((remainder-1 (let ((*oe-expanded* *oe-expanded*)
			;	 (*reductio-tried* *reductio-tried*)
				 ) 
			     (Prove-int new-B-left g)))
	      (remainder-2 (let ((*oe-expanded* *oe-expanded*)
				;(*reductio-tried* *reductio-tried*)
				 ) 
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

(define-strategy inter-cond-goals! (B g)
   (if (first (igoals-mp B g))
       (let  ((i-mp (first (igoals-mp B g))))
	 (Join (Prove-int B (first (args i-mp)))
	       (proof-step :cond-elim   (second (args i-mp)))))))
;(not (member g B :test #'equalp)) 
(define-strategy reductio! (B g)
  (multiple-value-bind 
	(reductio-proof reductio-target)
      (try (lambda (red-target) 
	     (if (not (tried-reductio? red-target))
		 (let ((*reductio-tried* *reductio-tried*))
		   (Prove-Int 
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
    (if t ;(and (not (member g B :test #'equalp)) (not (member (dual  g) B :test #'equalp)))
	(apply #'Any (mapcar (lambda (s) 
			       (if  (and
					(not (tried-reductio? g))) 
				   (Join
				    (subproof (dual g)  
					      (Join 			       
					       (let ((*reductio-tried* *reductio-tried*)) 
						 (Prove-int (cons (dual g) B) s))
					       (let ((*reductio-tried* *reductio-tried*)) 
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



(defun first-sat (pred list)
  "Given a predicate pred and a list, finds the first element of the
   list which satisfies the predicate, else returns nil"
  (if list
      (let ((elem (first list)))
	  (if (funcall pred elem)
	      elem
	      (first-sat pred (rest list))))))


(defun Join (&rest args)
  "If all the arguments are non nill, returns the list of arguments. 
   Else it returns nil."
  (if (every (complement #'null) args) args nil))



(defun Any (&rest args)
  "If any of the arguments are non nill, returns the first of those. 
   Else it returns nil."
  (let ((first-sat (first-sat (complement #'null) args)))
    (if first-sat first-sat nil)))

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
	(let ((*command* (prompt-read (princ-to-string (list B :Goal g)))))
	  (cond ((equalp *command* "n")
		 (progn (format t "[quitting]") (return-from Prove-Int nil)))
		(t (format t "[>]") )))))
  (if (not (is-problem-in-stack? 
	    (make-problem 
	     (remove-duplicates B :test #'equalp)
	     g)))
      (progn (push-problem (make-problem (remove-duplicates B :test #'equalp) g))
	     (let ((ans (or
			 (reiterate! B g)
			 (or-intro! B g)

			 (incons! B g)
			 (and-elim! B g)
			 (cond-elim! B g)
			 (bicond-intro! B g)
			 (cond-intro! B g)
			 (and-intro! B g)
			 (or-elim! B g)
			 (inter-cond-goals! B g)
			 (reductio! B g)
			 (all-reductio! B g))))
	       (if ans (remove-problem-from-stack (make-problem B g)))
	       ans))))
 


(defun subproof (added p) (if p (list :subproof :added added p) nil))



;;; Some simple helper functions.
(defun can-reiterate? (B g) (member g B :test #'equalp))
(defun is-conditional? (g) (matches g '(implies ?x ?y)))
(defun is-biconditional? (g) (matches g '(iff ?x ?y)))
(defun is-conjunction? (g) (matches g '(and ?x ?y)))
(defun is-disjunction? (g) (matches g '(or ?x ?y)))
(defun is-negation? (g) (matches g '(not ?x)))
(defun arg-1 (g) (second g))

;; returns the smallest formula which contains f, but is semantically opposite of f.
(defun dual (f) (if (is-negation? f) (arg-1 f) `(not ,f)))

(defun inconsistent-pair (B)
  (first-sat (complement #'null)
	     (mapcar (lambda (x) 
		       (first-sat (complement #'null)  (mapcar (lambda (y) (if (or (equalp x (dual y))
									    (equalp y (dual x)))
									(list x y)
									nil)) B))) B)))

(defun proof-step (&rest args)
  (cons :APPLY  args))



(defun matches (x y) 
 (simple-unify x y))




(defun simple-unify (x y)
  (handler-case
      (if  (cl-unification:unify x y) t)
    (cl-unification:UNIFICATION-FAILURE  () nil)))

(defun mp-expanded? (f) (member f *mp-expanded* :test #'equalp))

(defun ae-expanded? (f) (member f *ae-expanded* :test #'equalp))
(defun oe-expanded? (f) (member f *oe-expanded* :test #'equalp))

(defun  tried-reductio? (g &optional (b *reductio-tried*))
  (or (member g *reductio-tried* :test #'equalp) (not (setf *reductio-tried* (cons g *reductio-tried*)))))

(defun add-to-mp-expanded (f) (setf *mp-expanded* (cons f *mp-expanded*)))

(defun add-to-ae-expanded (f) (setf *ae-expanded* (cons f *ae-expanded*)))
(defun add-to-oe-expanded (f) (setf *oe-expanded* (cons f *oe-expanded*)))

(defun AEWffs (B) (remove-if-not #'is-conjunction? B))
(defun OEWffs (B) (remove-if-not #'is-disjunction? B))

(defun MPWffs (B) (remove-if-not #'mp-foci? (all-pairs B)))

(defun fresh-AEWffs (B) (set-difference (AEWffs B) *ae-expanded*))
(defun fresh-OEWffs (B) (set-difference (OEWffs B) *oe-expanded*))
(defun all-pairs (B) (reduce #'append (mapcar (lambda (x) (mapcar (lambda (y) (list x y)) B)) B)))
(defun fresh-MPWffs (B) (set-difference (MPWffs B) *mp-expanded* :test #'equalp))

(defun and-elim (f) 
  (if (not (ae-expanded? f))
      (add-to-ae-expanded f)) 
  (rest f))

(defun or-elim (f) 
  (if (not (oe-expanded? f))
    (add-to-oe-expanded f)) 
  (rest f))

(defun mp-foci? (f)
  (let ((antecedent (first f))
	(conditional (second f)))
    (and (is-conditional? conditional) (equalp antecedent (first (args conditional))))))
(defun cond-elim (f) 
  (let ((conditional (second f))
	(antecedent (first f)))
    (if (mp-foci? f)
	(add-to-mp-expanded f))
   ; (pprint (concatenate 'string "[ " (princ-to-string *mp-expanded*) " ]"))
    (second (args conditional))))


;;; 
;;; []
(defun goal (proof) ;(first (last)) 
       (first (last proof)))

(defun try (f cases)
  (if (null cases)
      nil
      (let ((first-try (funcall f (first cases))))
	(if first-try (values first-try (first cases)) (try f (rest cases)))))) 

(defun args (f) (rest f))
(defun subformulae (f)
  (if (atom f) (list f)
      (cons f (remove-duplicates (reduce #'append (mapcar #'subformulae-int (args f))) :test #'equalp))))
(defun subformulae-int (f)
  (if (atom f) 
      (list f)
      (cons f (reduce #'append (mapcar #'subformulae-int (args f))))))


(defun igoals-mp (B g)
  (remove-if-not (lambda (f)
		   (and (is-conditional? f)
			(equalp (second (args f)) g)))
		  B))

(subformulae '(and (if b r) a))