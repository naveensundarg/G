(defparameter *seen* nil)
(defparameter *expanded* nil)
(defparameter *ae-expanded* nil)
(defparameter *oe-expanded* nil)
(defparameter *mp-expanded* nil)
(defparameter *reductio-tried* nil)



(defun dual (f) (if (is-negation? f) (arg-1 f) `(not ,f)))

(defun simple-unify (x y)
  (handler-case
      (if  (cl-unification:unify x y) t)
    (cl-unification:UNIFICATION-FAILURE  () nil)))

(defun matches (x y) 
 (simple-unify x y))

(defun all-pairs (B) 
  (reduce #'append (mapcar (lambda (x) (mapcar (lambda (y) (list x y)) B)) B)))

(defun args (f) (rest f))

;;
(defun inconsistent-pair (B)
  (first-sat 
   (complement #'null)
   (mapcar (lambda (x) 
	     (first-sat (complement #'null)  
			(mapcar (lambda (y) (if (or (equal x (dual y))
						    (equal y (dual x)))
						(list x y)
						nil)) B))) B)))


(defun subproof (added p) (if p (list :subproof :added added p) nil))

;;; Some simple helper functions.
(defun can-reiterate? (B g) (member g B :test #'equal))
(defun is-conditional? (g) (matches g '(implies ?x ?y)))
(defun is-biconditional? (g) (matches g '(iff ?x ?y)))
(defun is-conjunction? (g) (matches g '(and ?x ?y)))
(defun is-disjunction? (g) (matches g '(or ?x ?y)))
(defun is-negation? (g) (matches g '(not ?x)))
(defun arg-1 (g) (second g))

;; returns the smallest formula which contains f, but is semantically opposite of f.


(defun proof-step (&rest args)
  (cons :APPLY  args))



(defun mp-expanded? (f) (member f *mp-expanded* :test #'equal))

(defun ae-expanded? (f) (member f *ae-expanded* :test #'equal))
(defun oe-expanded? (f) (member f *oe-expanded* :test #'equal))

(defun  tried-reductio? (g)
  (or (member g *reductio-tried* :test #'equal) (not (setf *reductio-tried* (cons g *reductio-tried*)))))

(defun add-to-mp-expanded (f) (setf *mp-expanded* (cons f *mp-expanded*)))

(defun add-to-ae-expanded (f) (setf *ae-expanded* (cons f *ae-expanded*)))
(defun add-to-oe-expanded (f) (setf *oe-expanded* (cons f *oe-expanded*)))

(defun AEWffs (B) (remove-if-not #'is-conjunction? B))
(defun OEWffs (B) (remove-if-not #'is-disjunction? B))

(defun mp-foci? (f)
  (let ((antecedent (first f))
	(conditional (second f)))
    (and (is-conditional? conditional) (equal antecedent (first (args conditional))))))

(defun MPWffs (B) (remove-if-not #'mp-foci? (all-pairs B)))

(defun fresh-AEWffs (B) (set-difference (AEWffs B) *ae-expanded*))
(defun fresh-OEWffs (B) (set-difference (OEWffs B) *oe-expanded*))

(defun fresh-MPWffs (B) (set-difference (MPWffs B) *mp-expanded* :test #'equal))

(defun and-elim (f) 
  (if (not (ae-expanded? f))
      (add-to-ae-expanded f)) 
  (rest f))

(defun or-elim (f) 
  (if (not (oe-expanded? f))
    (add-to-oe-expanded f)) 
  (rest f))

(defun cond-elim (f) 
  (let ((conditional (second f)))
    (if (mp-foci? f)
	(add-to-mp-expanded f))
   ; (pprint (concatenate 'string "[ " (princ-to-string *mp-expanded*) " ]"))
    (second (args conditional))))




;;; 
;;; []
;; (defun goal (proof) ;(first (last)) 
;;        (first (last proof)))

(defun try (f cases)
  (if (null cases)
      nil
      (let ((first-try (funcall f (first cases))))
	(if first-try (values first-try (first cases)) (try f (rest cases)))))) 


(defun subformulae-int (f)
  (if (atom f) 
      (list f)
      (cons f (reduce #'append (mapcar #'subformulae-int (args f))))))


(defun subformulae (f)
  (if (atom f) (list f)
      (cons f (remove-duplicates (reduce #'append (mapcar #'subformulae-int (args f))) :test #'equal))))

(defun igoals-mp (B g)
  (remove-if-not (lambda (f)
		   (and (is-conditional? f)
			(member g (subformulae (second (args f))) :test #'equal)
			))
		  B))


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
    (list (remove-duplicates premises :test #'equal) goal)))

(defun push-problem (p) (push p *problem-stack*))

(defun subsumes? (P1 P2)
  (let ((premises1 (premises P1))
	(premises2 (premises P2))
	(goal1 (goal P1))
	(goal2 (goal P2)))
    (and (equal goal1 goal2)
	 (equal premises2 premises1))))

(defun is-problem-in-stack? (p) (some (complement #'null)
				      (mapcar (lambda (x)
						(if (subsumes? x p) t nil))  
					      *problem-stack* )))

(defun clear-problem-stack () (setf *problem-stack* nil))

(defun remove-problem-from-stack (p)
  (setf *problem-stack*  (remove nil (mapcar (lambda (x)
					       (if (subsumes? x p) nil x))  
					     *problem-stack*))))
(defun complexity (f)
  (if (atom f)
      1
      (apply #'+ (mapcar #'complexity f))))




(defun count-deep (sub f)
  (if (equal sub f)
      1
      (if  (atom f)
	   0
	   (apply #'+ (mapcar (lambda (g) (count-deep sub g)) (args f))))))

(defun biggest-repeating-subf (f)
		(let* ((subs (sort (remove-if #'atom (subformulae f)) (lambda (x y) (>= (complexity x) (complexity y)))))
		       (counts (mapcar (lambda (s) (count-deep s f)) subs))
		       (ind (position (first-sat (lambda (c) (> c 1)) counts) counts)))
		  (if ind (nth ind subs))))

(defun atoms (f) (if (atom f) (list f) (reduce #'append (mapcar #'atoms (args f)))))

(defun abstract (f)
	   (if (atom f)
	        f
	       (let ((biggest-repeating (biggest-repeating-subf f)))
		 (if (and biggest-repeating (intersection (subformulae biggest-repeating)(subformulae f)))
		     (let* ((sym (gensym))
			    (curr (subst sym biggest-repeating f :test #'equal)))
		       (if (null (intersection (atoms biggest-repeating) (atoms curr)))
			   (values (abstract curr) (list (list sym  biggest-repeating)))
			   (values f nil))) 
		     (values f nil)))))