
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: constraints.lisp
;;; Author: Peter Clark
;;; Purpose: Constraint checking/enforcement mechanism for KM

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

#| ======================================================================
		  CONSTRAINT CHECKING / ENFORCEMENT
   ======================================================================

SATISFIABILITY vs CONSISTENCY: Used for has-definition,
	e.g., (a Person) doesn't SATISFY (every House-Owner has-definition (instance-of (Person)) (owns ((at-least 1 House))))
		       but is CONSISTENT with it.

filter-using-constraints: remove vals which fail a constraint. Violations aren't an error.
	Used solely to remove inconsistent projected vals in km-slotvals-from-kb.

(are-consistent-with-constraints vals constraints slot)		- lazy-unify
(satisfies-constraints vals constraints slot)			- subsumes
	returns t/nil if vals [can] satisfy constraints or not. Failure is not an error.
	Used by lazy-unify and subsumes, to check for consistency/satisfaction. No side effects.
	It ASSUMES vals are fully evaluated. It does naive counting, so will FAIL given
	    constraints which can be forcibly met, e.g.,:
	KM: (satisfies-constraints '#$(_House20 _House21) '#$((exactly 1 House)) '#$owns)
	nil
	Ug.

enforce-constraints: Apply the constraints. Failure IS an error and will be reported.
Used to process the values collected in km-slotvals-from-kb.

test-constraints calls test-set-constraint:
	used by is0 (subsumes.lisp), in mode SATISFIES
	used by check-slotvals-constraints (lazy-unify.lisp), in mode CONSISTENT

test-set-constraints calls test-set-constraint0: This is used ONLY by check-slotvals-constraints in lazy-unify.lisp.
  This only does a consistent check, not a satisfied check.
|#

;;; If t, then automatically delete vals which violate constraints. If not, keep going regardless.
;;; This is only significant if *error-report-silent* is t, otherwise KM will throw an error if there's a violation.
;;; PEC 11/14/10: This can probably be removed now and made a constant.
(defparameter *remove-violating-instances* nil)

;;; ======================================================================

(defun note-are-constraints ()
  (or *are-some-constraints* (km-setq '*are-some-constraints* t)))

;;; This will *REMOVE VIOLATORS* (but not necessarily fail) if a constraint is violated.
;;; It should be used as a filter, not as a test. For a test, use
;;; instead. It *DOESN'T* report violations.
;;; This has no side-effects. Returns a reduced list of values.
;;; It's solely used for filtering out projected values which conflict with current constraints.
;;; THIS ASSUME VALS IS A LIST OF ATOMS, IE. ANY KM EVALUATION HAS ALREADY BEEN PERFORMED.
(defun filter-using-constraints (vals constraints &optional slot)
  (cond ((null constraints) vals)
	((and (tracep) (not (traceconstraintsp)))
	 (let ((*trace* nil))
	   (filter-using-constraints0 vals constraints slot)))
;	 (prog2
;	     (suspend-trace)
;	     (filter-using-constraints0 vals constraints slot)
;	   (unsuspend-trace)))
	(t (km-trace 'comment "Testing constraints ~a" constraints)
	   (filter-using-constraints0 vals constraints slot))))

(defun filter-using-constraints0 (vals constraints slot)
  (remove-if-not #'(lambda (val) (test-val-constraints val (dereference constraints) (special-slot-type slot) :mode 'consistent)) vals))

;;; ======================================================================
;;;		ARE-CONSISTENT-WITH-CONSTRAINTS
;;; ======================================================================

#|
This will *FAIL* if a constraint is violated. Returns T/NIL.
8/16/00 - Extended to to handle special constraint handling for slots whose values are classes.
	(are-consistent-with-constraints '#$(Car) '#$((<> Vehicle)) '#$instance-of)
   should FAIL, as #$instance-of is a remove-subsumers-slotp, but
	(are-consistent-with-constraints '#$(Vehicle) '#$((<> Car)) '#$instance-of)
   should SUCCEED. Similarly,
	(are-consistent-with-constraints '#$(Vehicle) '#$((<> Car)) '#$subclasses
   should FAIL, as #$subclasses is a remove-subsumees-slotp, but
	(are-consistent-with-constraints '#$(Car) '#$((<> Vehicle)) '#$subclasses)
   should SUCCEED.
|#
(defun are-consistent-with-constraints (vals0 constraints0 slot)
  (not (violated-constraints vals0 constraints0 slot :mode 'consistent)))

(defun satisfies-constraints (vals0 constraints0 slot &key incompletep)
  (not (violated-constraints vals0 constraints0 slot :mode 'satisfies :incompletep incompletep)))

;;; [1] Could later be improved to be (violated-set-constraint ...) which returns (constraint violating-vals) directly
(defun violated-constraints (vals0 constraints0 slot &key mode incompletep)
  (cond ((null constraints0) nil)
	(t (let ((vals (remove-dup-instances vals0)) 		; does dereferencing etc.
		 (constraints (dereference (desource+decomment constraints0)))
		 (special-slot-type (special-slot-type slot)))
	     (or (case mode
		   (consistent (violated-set-constraints (list vals) constraints))
		   (satisfies (some #'(lambda (constraint)
					(cond ((and (set-constraint-exprp constraint)
						    (not (set-constraint-satisfied vals constraint :incompletep incompletep))) ; [1]
					       (list constraint vals))))
				    constraints)))
		 (some #'(lambda (val)
			   (violated-val-constraints val constraints special-slot-type :mode mode))
		       vals))))))

(defun special-slot-type (slot)
  (cond ((null slot) nil)
	((remove-subsumers-slotp slot) 'remove-subsumers-slot)
	((remove-subsumees-slotp slot) 'remove-subsumees-slot)))

(defun test-val-constraints (val constraints special-slot-type &key mode)
  (not (violated-val-constraints val constraints special-slot-type :mode mode)))

(defun violated-val-constraints (val constraints special-slot-type &key mode)
  (some #'(lambda (constraint)
	    (cond ((and (val-constraint-exprp constraint)
			(not (test-val-constraint val constraint special-slot-type :mode mode))) ; i.e., test fails
		   (list constraint val))))
	constraints))

;;; [1] ignore for now - could look for mutually inconsistent constraints later
;;; [2] Note we ASSUME for special-slot-types that the constraints are NECESSARILY of the form (<> ATOMIC-CLASS)
;;; [3b] Technically, if there's no possible values this is a failure. HOWEVER, KM may fail to find possible values
;;; 	 if the system is looping, and so aborts the computation. See enforce-val-constraint also, for identical issue
;;; [4] Important not to abort if looping on constraints
(defun test-val-constraint (val constraint special-slot-type &key mode)
  (cond ((constraint-exprp val))	; [1]
	(t (case (first constraint)
;  	     (#$must-be-a (unifiable-with-expr val `#$(a ,@(REST CONSTRAINT))))	; not complete enough, and may loop!!
	     (#$retain-expr t)
	     (#$must-be-a (cond ((instance-of val '#$Aggregate)
				 (let ( (element-type (cond ((not (km-structured-list-valp val)) ; NEW ADDED TEST
							     (km-int `#$(the element-type of ,VAL))))) )
				   (or (null element-type)
					   (compatible-classes :classes1 element-type :classes2 (list (second constraint))))))
													; ignore any "with ..." part, as
													; disjoint-class-sets can't handle it.
;				     (every #'(lambda (element-type)
;						(km-int `#$(,ELEMENT-TYPE is-subsumed-by (the-class ,@(REST CONSTRAINT)))))
;					    (km-int `#$(the element-type of ,VAL))))
				    ((equal constraint '#$(must-be-a Thing)))		; t
				    (t (case mode
					     (consistent (km-int `#$(,VAL &? (a ,@(REST CONSTRAINT)))))
					     (satisfies  (km-int `#$(,VAL is '(a ,@(REST CONSTRAINT)))))))))
		 (#$mustnt-be-a (km-int `#$(not (,VAL is '(a ,@(REST CONSTRAINT))))))
		 (<> (cond ((is-km-term (second constraint))
			    (case special-slot-type
				  (remove-subsumers-slot (not (is-subclass-of val (second constraint))))
				  (remove-subsumees-slot (not (is-subclass-of (second constraint) val)))
				  (t (not (equal val (second constraint))))))
			   (t (km-int `#$(,VAL /= ,(SECOND CONSTRAINT))))))	; [2]
		 (#$excluded-values
		  (let ( (excluded-values (km-int (vals-to-val (rest constraint)))) )
		    (cond
		     ((null excluded-values))
		     ((eq special-slot-type 'remove-subsumers-slot) ; #$instance-of	; val = Animal, excluded-values = (Tiger) OK
		      (not (intersection (all-superclasses0 val) excluded-values)))	; val = Tiger, excluded-values = (Animal) NOT OK
		     ((eq special-slot-type 'remove-subsumees-slot) ; #$subclasses	; val = Animal, excluded-values = (Tiger) NOT OK  [4]
		      (not (intersection (all-subclasses0 val) excluded-values)))	; val = Tiger, excluded-values = (Animal) OK
		     (t (not (member val excluded-values))))))			; test it
		 (#$possible-values
		  (let ( (possible-values (km-int (vals-to-val (rest constraint)))) )		; [3]
;		    (km-format t "possible-values = ~a~%" possible-values)
		    (cond (possible-values
			   (case special-slot-type
				 (remove-subsumers-slot (not (disjoint-class-sets (list val) possible-values)))
				 (remove-subsumees-slot (not (disjoint-class-sets (list val) possible-values)))
				 (t (case mode
					  (consistent (some #'(lambda (possible-value)
								 (km-int `(,val &? ,possible-value)))
							     possible-values))
					  (satisfies (member val possible-values :test #'equal))))))
			  (t))))	; [3b] fail, not succeed -- may be no vals due to looping, not really values
		 (#$constraint
		  (let ((constraint-expr (subst val '#$TheValue (second constraint))))
		    (cond ((looping-on constraint-expr) t) ; Don't abort if looping!
			  (t (km-int constraint-expr)))))
;		 (#$override t)
		 (#$no-inheritance t)
		 (t (report-error 'user-error "Unrecognized form of constraint ~a~%" constraint))))))

;;; Test for SATISFIABILITY not CONSISTENCY. Used for has-definition,
;;;		e.g., (a Person) doesn't SATISFY (every House-Owner has-definition (owns ((at-least 1 House))))
;;;		       but is CONSISTENT with it.
;;; [1] this computation is seemingly (but insignificantly) inefficient here, and could be moved earlier.
;;; But: it is a place-holder, where we might later want to check for mutually inconsistent constraints later.
;;; [2] Efficiency - only do the length test if needed later
;;  [3] Copy this special case from enforce-set-constraints: want to allow possible unifications for singleton values.
(defun set-constraint-satisfied (vals0 constraint &key incompletep)
  (cond
   ((eq constraint '#$:incomplete) t)
   (t (let*
	 ((vals (remove-constraints vals0)) 	; [1]
	  (n (second constraint))
	  (class (third constraint))
	  (nvals (cond ((member (first constraint) '#$(at-least exactly at-most))
			(length (remove-if-not #'(lambda (val) (isa val class)) vals)))))
	  (forced-class (or (minimatch1 constraint '#$(at-most 1 ?class)) 	 ; [3]
			    (minimatch1 constraint '#$(exactly 1 ?class))))
	  (vals-in-class (cond (forced-class (remove-if-not #'(lambda (val) (isa val forced-class)) vals)))))
	(cond
          ((> (length vals-in-class) 1)	; necc. 0 if no forced class
  	   (every #'(lambda (pair) (km-int `(,(first pair) &? ,(second pair)))) (all-adjacent-pairs vals-in-class)))
	  (t (case (first constraint)
	       (#$at-least (>= nvals n))
	       (#$exactly  (and (not incompletep) (= nvals n)))  ; else more vals might be added later
	       (#$at-most  (and (not incompletep) (<= nvals n))) ; else more vals might be added later
	       (#$set-constraint (km-int (subst (vals-to-val vals) '#$TheValues (second constraint))))
	       (#$sometimes t)
	       (#$set-filter t)
	       (t (report-error 'user-error "Unrecognized form of set constraint ~a~%" constraint)
		  vals0))))))))

;;; ======================================================================
;;;		IS-CONSISTENT
;;; ======================================================================

;;; Returns T/NIL. Here, we have vals and constraints mixed, and in principle could check
;;; constraints are mutually consistent also.
(defun is-consistent (vals+constraints)
  (let ((constraints (remove-if-not #'constraint-exprp vals+constraints))
	(vals (remove-if #'constraint-exprp vals+constraints)))
    (not (violated-constraints vals constraints nil :mode 'consistent))))

;(defun is-consistent (vals+constraints0)
;  (cond ((null vals+constraints0) t)
;	(t (let ( (vals+constraints (remove-dup-instances (desource+decomment vals+constraints0))) )
;	     (and (every #'(lambda (constraint)
;			     (or (not (set-constraint-exprp constraint))
;				 (test-set-constraint vals+constraints constraint :mode 'consistent)))
;			 vals+constraints)
;	     (every #'(lambda (val) (test-val-constraints val vals+constraints nil :mode 'consistent)) vals+constraints))))))

;;; ======================================================================
;;;		ENFORCE-CONSTRAINTS
;;; ======================================================================

;;; Returns revised vals, after constraints have been enforced
;;; This one will do coersion, as well as testing.
;;; This assume vals is a list of atoms, ie. any km evaluation has already been performed.
;;; It also ASSUMES vals and constraints are ALREADY dereferenced
;;; IF constraints can't be satisfied THEN this throws an error (report-error), i.e., we ASSUME that
;;;    passability has already been tested via satisfies-constraints.
(defun enforce-constraints (vals constraints &key target)
    (cond ((and (tracep) (not (traceconstraintsp)))
	   (let ((*trace* nil))
	     (enforce-constraints0 vals constraints :target target)))
;	 (prog2 (suspend-trace) (enforce-constraints0 vals constraints instance slot) (unsuspend-trace)))
	  (t (km-trace 'comment "Enforcing constraints ~a" constraints)
	     (enforce-constraints0 vals constraints :target target))))

;;; ******* NOTE!! **********
;;; 9/7/99: Disable the set-valued constraints! It's causing too many problems! See constraints.README
;;; We now reduce it to are-consistent-with-constraints for set-valued constraints.
;;; 9/17/99: Put it back again, then hurriedly take it out again (see enforcement-problem.km)
;;; [1] 9/19/00: Should do set constraint checks first, as they may enforce coercion enabling later val checks to succeed.
;;; ASSUME: Dereferencing has already been done
(defun enforce-constraints0 (vals constraints &key target)
; ENFORCEMENT VERSION
;  (enforce-set-constraints
;   (remove-if-not #'(lambda (val) (enforce-val-constraints val constraints slot)) vals)		; revised vals
;   constraints))
  (let* ((slot (second target))
	 (instance (fourth target))
	 (special-slot-type (cond ((remove-subsumers-slotp slot) 'remove-subsumers-slot)
				  ((remove-subsumees-slotp slot) 'remove-subsumees-slot)))
	 (vals2 (enforce-set-constraints vals constraints :target target))
	 (vals-to-keep (remove-if-not #'(lambda (val) ; [1]
					  (enforce-val-constraints val constraints special-slot-type :target target))
				      vals2))
	 (vals-to-drop (set-difference vals2 vals-to-keep)))
    (cond
     (*remove-violating-instances*
      (cond (target (mapc #'(lambda (val-to-drop)
			      (delete-val instance slot val-to-drop))
			  vals-to-drop)))
      vals-to-keep)
     (t vals2))))

; TESTING ONLY VERSION
; (let ( (newvals (remove-if-not #'(lambda (val) (enforce-val-constraints val constraints)) vals)) )
;   (mapc #'(lambda (constraint)				; test but don't enforce set constraints, for now
;	     (cond ((not (set-constraint-exprp constraint)))
;		   ((is-consistent-with-set-constraint newvals constraint))
;		   (t (report-error 'user-error "Constraint violation! Values ~a conflict with constraint ~a!~%"
;				    newvals constraint))))
;	 constraints)
;   newvals))

(defun enforce-val-constraints (val constraints special-slot-type &key target)
  (let ((slot (second target))
	(instance (fourth target)))
    (and val (every #'(lambda (constraint)
			(or (not (val-constraint-exprp constraint))
			    (enforce-val-constraint val constraint instance slot special-slot-type)
			    (report-error 'user-error
					  `(|val-constraint| ,instance ,slot ,val ,constraint)
					  "Constraint violation! Value ~a conflicts with ~a!~%"
					  val constraint)))
		    constraints))))

;;; RETURNS: non-nil OR NIL if there's an error in the enforcement
;;; 5.3.00 add to report error later
;;; [1] This is actually a check, rather than an enforcement. It's the best we can do for now.
;;; [2] This could be more efficient - I only care if there's a unique solution or not
;;; [3] Technically, this is a failure - if there's no possible values. HOWEVER, KM may fail to find possible values if the
;;;	system is looping, and so aborts the computation. See is-consistent-with-val-constraint also, for identical issue
;;; [4] I'm not sure about this - leave it in for completeness for now.
;;; [5] Add target, to allow recording of explanation
(defun enforce-val-constraint (val constraint0 instance slot special-slot-type)
 (declare (ignore slot))
 (let ((constraint (desource+decomment constraint0)))
  (case (first constraint)
    (#$retain-expr t)
    (#$must-be-a (cond ((instance-of val '#$Aggregate) ; NB constraints on the aggregates elements should be implemented at KB, not KM, level. Here we only do a test, not an enforcement
;			(let ( (element-type (km-int `#$(the element-type of ,VAL))) )
			(let ( (element-type (cond ((not (km-structured-list-valp val))		; NEW ADDED TEST
						    (km-int `#$(the element-type of ,VAL))))) )
			  (or (null element-type)
			      (compatible-classes :classes1 element-type :classes2 (list (second constraint))))))
										; ignore any "with ..." part, as
										; disjoint-class-sets can't handle it.
		       ((equal constraint '#$(must-be-a Thing)) val)
;		       (t (km-int `#$(,VAL & (a ,@(REST CONSTRAINT))) :target `#$(the ,SLOT of ,INSTANCE)))))  ; [5]
; REVISION: (a <x>) constraint should be applied to the (instance instance-of <x>) link, not (instance slot val) link.
; This is implemented now as a separate record-explanation-for sep in in process-km1-result.
		       (t (km-int `#$(,VAL & (a ,@(REST CONSTRAINT0)))))))	; NOTE *KEEP* source info here
    (#$mustnt-be-a (km-int `#$(not (,VAL is '(a ,@(REST CONSTRAINT0))))))
;    (<> (cond ((is-km-term (second constraint))
;	       (cond ((not (equal val (second constraint)))		; check constraint
;	      (t (km-int `#$(,VAL /= ,(SECOND CONSTRAINT))))))
    (<> (km-int `#$(,VAL /== ,(SECOND CONSTRAINT))))
    (#$excluded-values
     (let ( (excluded-values (km-int (vals-to-val (rest constraint)))) )		; [1]
       (cond
	((null excluded-values))
	((eq special-slot-type 'remove-subsumers-slot)		; #$instance-of	;val=Animal, excluded-values=(Tiger) OK
	 (not (intersection (all-superclasses0 val) excluded-values)))		;val=Tiger, excluded-values=(Animal) NOT OK
	((eq special-slot-type 'remove-subsumees-slot)	; [4]	; #$subclasses	;val=Animal, excluded-values=(Tiger) NOT OK
	 (not (intersection (all-subclasses0 val) excluded-values)))		;val=Tiger, excluded-values=(Animal) OK
	((member val excluded-values) nil)			; test it
	(t (mapcar #'(lambda (excluded-value)			; assert it
		       (add-val val '/== excluded-value))
		   excluded-values)))))
    (#$possible-values
     (let ( (possible-values (km-int (vals-to-val (rest constraint)))) )		; [3]
       (cond
	((null possible-values))				; [3] - Not necc. failure -- could fail due to looping!

;; The below is rather obtuse code to handle a special case something like:
;;			    (_Car1 has (instance-of ((possible-values Car Truck))))
	((and (eq special-slot-type 'remove-subsumers-slot) instance) ; instance /= nil
	 (cond ((member val possible-values))
	       ((singletonp possible-values)
		(km-trace 'comment "~a: Only one possible value so enforcing ~a isa ~a!~%"
			  `#$(possible-values ,@(REST CONSTRAINT)) instance (first possible-values))
		(km-int `(,instance == (#$a ,(first possible-values)))))
	       (t (let ( (unifiable-values (first-N-unifiable-values2 possible-values instance 2)) )
		    (cond ((singletonp unifiable-values)
			   (km-trace 'comment "~a: Only one consistent, possible value so enforcing ~a isa ~a!~%"
				     `#$(possible-values ,@(REST CONSTRAINT)) instance (first unifiable-values))
			   (km-int `(,instance == (#$a ,(first unifiable-values)))))
			  (unifiable-values t))))))		; if some unifiable values, constraint is satisfied
	((member special-slot-type '(remove-subsumers-slot remove-subsumees-slot))	; '#$instance-of
	 (not (disjoint-class-sets (list val) possible-values)))

	((member val possible-values))
	((singletonp possible-values)
	 (km-trace 'comment "~a: Only one possible value so enforcing ~a == ~a!~%"
		   `#$(possible-values ,@(REST CONSTRAINT)) val (first possible-values))
	 (km-int `(,val == ,(first possible-values))))
	(t (let ( (new-constraint `#$(possible-values ,@POSSIBLE-VALUES))
		  (unifiable-values (first-N-unifiable-values possible-values val 2)) )
;	     (km-format t "unifiable-values = ~a~%" unifiable-values)
	     (cond ((singletonp unifiable-values)
		    (km-trace 'comment "~a: Only one consistent, possible value so enforcing ~a == ~a!~%"
			      `#$(possible-values ,@(REST CONSTRAINT)) val (first unifiable-values))
		    (km-int `(,val == ,(first unifiable-values))))
		   ((not (null unifiable-values))
		    (or (member new-constraint (get-vals val '== :situation *global-situation*) :test #'equal)
			(km-int `#$(,VAL has (== (,NEW-CONSTRAINT))) :fail-mode 'error)))))))))		; assert it
    (#$constraint (let ((constraint-expr (subst val '#$TheValue (second constraint))))
		    (cond ((looping-on constraint-expr) t) ; Don't abort if looping!
			  (t (km-int constraint-expr)))))
;   (#$override t)
    (#$no-inheritance t)
    (t (report-error 'user-error "Unrecognized form of constraint ~a~%" constraint)))))

;;; Returns the first N possible-values which are unifiable with val.
;;; This stops after the first N are found, and thus is a bit more efficient than doing:
;;;    (remove-if-not #'(lambda (possible-value) (km-int `(,val &? ,possible-value))) possible-values)
(defun first-N-unifiable-values (possible-values val n)
  (cond ((endp possible-values) nil)
	((<= n 0) nil)
	((km-int `(,val &? ,(first possible-values)))
	 (cons (first possible-values) (first-N-unifiable-values (rest possible-values) val (1- n))))
	(t (first-N-unifiable-values (rest possible-values) val n))))

(defun first-N-unifiable-values2 (possible-values instance n)
  (cond ((endp possible-values) nil)
	((<= n 0) nil)
	((km-int `(,instance &? (#$a ,(first possible-values))))
	 (cons (first possible-values) (first-N-unifiable-values2 (rest possible-values) instance (1- n))))
	(t (first-N-unifiable-values2 (rest possible-values) instance (1- n)))))

;;; ----------------------------------------

(defun enforce-set-constraints (vals constraints &key target)
  (enforce-set-constraints0 (remove-pending-equalities vals) constraints :target target))

#| Remove pending equalities for this problem:
(a DNA-elongation) gives a wrong KM error:
     DNA1 &! DNA2
       (has-part (x y))  (has-part (a b))
   -> looping: Assuming (y &! b) to prove (y &! b)
   <-  has-part (x y b)		; NOTE: The assumption doesn't actually *do* the (y &! b), so we don't get obvious duplicates in the results
       FAIL constraint (exactly 2 DNA-strand)
|#
(defun remove-pending-equalities (vals)
  (cond ((endp vals) nil)
	(t (let ((val (first vals)))
	     (cond ((some #'(lambda (val2) (pending-equality val val2)) (rest vals))
		    (remove-pending-equalities (rest vals)))
		   (t (cons val (remove-pending-equalities (rest vals)))))))))

;;; ----------

(defun enforce-set-constraints0 (vals constraints &key target)
  (cond ((endp constraints) vals)
	((val-constraint-exprp (first constraints))		; skip these
	 (enforce-set-constraints0 vals (rest constraints) :target target))
	(t (enforce-set-constraints0 (enforce-set-constraint vals (first constraints) :target target)
				     (rest constraints) :target target))))

;;; Just do this reduced version. RETURN: the modified vals
(defun enforce-set-constraint (vals constraint0 &key target)
  (let* ((constraint (desource+decomment constraint0))
	 (slot (second target))
	 (instance (fourth target))
	 (forced-class (or (minimatch1 constraint '#$(at-most 1 ?class))
			   (minimatch1 constraint '#$(exactly 1 ?class))))
	 (vals-in-class (cond (forced-class (remove-if-not #'(lambda (val) (isa val forced-class)) vals)))) )
    (cond ((eq constraint '#$:incomplete) vals)		; ignore this flag
          ((> (length vals-in-class) 1)	; necc. 0 if no forced class
	   (cond
	    ((every #'(lambda (pair) (km-int `(,(first pair) &? ,(second pair)))) (all-adjacent-pairs vals))
	     (make-comment "Unifying values ~a (forced by constraint (at-most 1 ~a)"
			   vals-in-class forced-class)
	     (cons (km-unique-int (vals-to-&-expr vals-in-class) :fail-mode 'error)
		   (ordered-set-difference vals vals-in-class)))
	    (t (report-error 'user-error
			     `(|set-constraint| ,instance ,slot ,vals-in-class ,constraint)
;			     "set-constraint violation!~%Found ~a ~a(s), but should be (at-most 1 ~a) and they can't be unified!~%Values were: ~a. Ignoring extras...~%"
			     "set-constraint violation!~%Found ~a ~a(s), but should be (~a 1 ~a) and they can't be unified!~%Values were: ~a.~%"
			     (length vals-in-class) forced-class (cond ((minimatch1 constraint '#$(at-most 1 ?class)) '#$at-most)
								       ((minimatch1 constraint '#$(exactly 1 ?class)) '#$exactly)
								       (t '#$??))
			     forced-class vals)
	       vals)))
	  (t (enforce-set-constraint2 vals constraint :target target)))))

;;; PROBLEMS! see test-suite/outstanding/enforcement-problem.km
;;; Simplified to just do the test and report on the problems
(defun enforce-set-constraint2 (vals constraint &key target)
  (let* ((slot (second target))
	 (instance (fourth target))
	 (n (second constraint))
	 (class (third constraint))
	 (count (length (remove-if-not #'(lambda (val) (isa val class)) vals))))
    (case (first constraint)
	  (#$at-least (cond ((or (> n *max-padding-instances*)
				 (>= count n)) vals)		; avoid (at-least 3455 Gene)
			    (t (append vals (loop repeat (- n count)
						collect (km-unique-int `#$(a ,CLASS) :fail-mode 'error)))))) ; classes missing so create them!!
	  (#$exactly (cond ((= count n) vals)
			   ((> count n)	;  no, you can always unify instances to get the desired # :-(
			    (report-error 'user-error
					  `(|set-constraint| ,instance ,slot ,vals ,constraint)
			     "set-constraint violation!~%Found ~a ~a(s), but should be exactly ~a!~%Values were: ~a.~%"
			       count class n vals)
; If *error-report-silent*, then this is the continuing behavior...
			    (cond (*remove-violating-instances*
				   (remove-if #'(lambda (val)
						  (cond ((isa val class)
							 (cond (target (delete-val instance slot val))) ; Inverse may already
							 t))) ; be asserted so must delete also
					      vals))
				  (t vals)))
			   ((> n *max-padding-instances*) vals) ; avoid (at-least 3455 Gene) - (< count n) is necc. true
			   (t (append vals (loop repeat (- n count)
					       collect (km-unique-int `#$(a ,CLASS) :fail-mode 'error)))))) ; classes missing so create them!!
	  (#$at-most (cond ((<= count n) vals)
			   (t (report-error 'user-error
					    `(|set-constraint| ,instance ,slot ,vals ,constraint)
					    "set-constraint violation!~%Found ~a ~a(s), but should be at-most ~a!~%Values were: ~a.~%"
					    count class n vals)
			      (cond
			       (*remove-violating-instances*
				(remove-if #'(lambda (val)
					       (cond ((isa val class)
						      (cond (target (delete-val instance slot val))) ; Inverse may already
						      t))) ; be asserted so must delete also
					   vals))
			       (t vals)))
			   ))
	  (#$set-constraint (cond ((km-int (subst (vals-to-val vals) '#$TheValues (second constraint))) vals)
				  (t (report-error 'user-error
						   `(|set-constraint| ,instance ,slot ,vals ,constraint)
						   "set-constraint violation!~%~a failed test ~a.~%"
						   vals (second constraint))
				     vals)))
	  (#$sometimes t)
	  (#$set-filter (let* ((filter (second constraint))
			       (vals-to-keep (apply filter (list vals))) ; return modified list of vals
			       (vals-to-drop (set-difference vals vals-to-keep)))
			    (cond
			     (*remove-violating-instances*
			      (cond (target (mapc #'(lambda (val-to-drop)
						      (delete-val instance slot val-to-drop))
						  vals-to-drop)))
			      vals-to-keep)
			     (t vals))))

	  (t (report-error 'user-error "Unrecognized form of set constraint ~a~%" constraint)
	     vals))))


;;; ======================================================================
;;;		VIOLATED-SET-CONSTRAINTS
;;; This is a rather complicated bit of code, to avoid reifying all existential expressions
;;; ======================================================================
#|
RETURNS the first constraint violated (or NIL if all passed) in the form (<constraint> <data>) pair

e.g., (violated-set-constraints '((1) (2)) '#$((at-most 1 Thing))) -> ((at-most 1 Thing) (1 2))

This is a special case of constraint checking, used by lazy-unify.lisp
Checks that the number of (potentially) unified objects are below the specified maximum.
Takes as arguments: exprs1 exprs2 expr-sets1 expr-sets2, where exprs1 exprs2 are each a set of instances,
   expr-sets1 is list of expression sets (expr-set1 expr-set2 ...), and similarly for expr-sets2.
We want to estimate what (exprs1 && exprs2 && expr-set11 && expr-set12 && ... && expr-set21 && expr-set22 && ...)
  will produce.
The system creates "unifications" which is a single list of unified elements from each sets.
The result will be, say:
	unifications = ((v11 & expr111) (v12) (v13 & expr112 & expr211 & expr221) (v21 & expr121) ....)
But we drop the "&" sign from these lists for convenience, as we never actually compute the unification.
 (We only care how many objects are in the final unification).

(violated-set-constraints '#$((_Car1 _Car2) (_Car2) ( ((a Car)) ((a House) (a Dog)) ) )  '#$((at-most 1 Thing)))
unification = ((_Car1 _Car2 (a Car)) ((a House)) ((a Dog)))
[1a] 3/16/01 - Can get confused: (_Car1 _Engine1) & (_Engine2) makes KM estimate that _Engine2 unifies with _Car1, which
	means there are now two engines resulting in an (incorrect) violation of a (exactly 1 Engine) constraint.
	Let's drop the vs for now. See outstanding/set-constraints.km
[1b] 5/23/01 - but no! (test-set-constraints '(_Tangible-Entity10 _Car11 _Tangible-Entity19) '(_Tangible-Entity26) nil nil '((exactly 1 Entity)))
	Should *succeed*, as (exactly 1 Entity) will force the three vs1 to be unified together, = ok!
|#
;;; For now, we only work with the vs1 and vs2. These are necessarily atomic
(defun violated-set-constraints (expr-sets constraints0)
  (let ((constraints (remove '#$:incomplete constraints0)))
    (some #'(lambda (constraint)
	      (case (first constraint)
		(#$at-least nil)
		(#$(exactly at-most) (violated-cardinality-constraint expr-sets constraint))
;		(#$set-constraint (not (km-int (subst (vals-to-val vals) '#$TheValues (second constraint)))))
		(#$set-constraint (cond ((not (km-int (subst (vals-to-val (valsets-to-&&-exprs expr-sets)) '#$TheValues (second constraint))))
					 (list constraint (vals-to-val (valsets-to-&&-exprs expr-sets))))))
		(#$sometimes nil)
		(#$set-filter nil)
; No, constraints might include value constraints also
;		(t (report-error 'user-error "Unrecognized form of set constraint ~a~%" constraint) nil)
		))
	  constraints)))

;;; [1] NOTE: There is a special case if N = 1, namely all the elements of all the expr-sets must be unifiable together.
;;; RETURNS: (<constraint> <data>) pair
(defun violated-cardinality-constraint (expr-sets constraint)
  (cond ((null expr-sets) nil)		; quick lookahead
	((and (singletonp expr-sets)
	      (<= (length (first expr-sets)) (second constraint))) nil) ; quick lookahead
	((and (eq (third constraint) '#$Thing)
	      (<= (length (remove-duplicates (remove-if #'constraint-exprp (append-lists expr-sets)))) (second constraint)))
;	 (km-format t "list = ~a~%" (remove-duplicates (remove-if #'constraint-exprp (append-lists expr-sets))))
	 nil)		; lookahead
	(t (let* ((n (second constraint))
		  (class (third constraint)) ; Nucleus
		  (expr-sets-in-class (remove nil (mapcar #'(lambda (exprs) (extract-exprs-in-class exprs class)) expr-sets)))
		  (exprs-in-class (remove-duplicates (append-lists expr-sets-in-class) :test #'equal)))	; #'equal ok? (a Atom) (a Atom) I think so
	     (cond
	      ((<= (length exprs-in-class) (second constraint)) nil)
	      ((and (eq n 0) exprs-in-class) (list constraint exprs-in-class)) 		; NEW 8/1/11
	      (t (let ((non-unifiable-pairs (non-unifiable-pairs exprs-in-class)))
		   (cond ((< (length non-unifiable-pairs) n) nil)			; e.g., n = 2, so 1 bad pair is ok but 2 may not be
			 ((eq n 1) (list constraint (remove-duplicates (append-lists non-unifiable-pairs) :test #'equal))) ; must all be unif if n = 1
			 (t (let ((groups (group-vals-unifiably exprs-in-class non-unifiable-pairs)))
			      (cond ((> (length groups) n)
				     (list constraint (remove-duplicates (append-lists non-unifiable-pairs) :test #'equal))))))))))))))


;;; (group-vals-unifiably '(a b c d e) '((a b) (c d) (a c))) -> (a d e) (b c))
(defun group-vals-unifiably (vals non-unifiable-pairs)
  (group-vals-unifiably0 vals nil non-unifiable-pairs))

(defun group-vals-unifiably0 (vals groups-so-far non-unifiable-pairs)
  (cond
   ((endp vals) groups-so-far)
   (t (let* ((val (first vals))
	     (new-groups (add-val-to-group val groups-so-far non-unifiable-pairs)))
	(group-vals-unifiably0 (rest vals) new-groups non-unifiable-pairs)))))

(defun add-val-to-group (val groups non-unifiable-pairs)
  (cond
   ((null groups) (list (list val)))
   (t (let ((group (first groups)))
	(cond ((notany #'(lambda (group-val)
			   (or (member (list val group-val) non-unifiable-pairs :test #'equal)
			       (member (list group-val val) non-unifiable-pairs :test #'equal)))
		       group)
	       `((,val ,@group) ,@(rest groups)))
	      (t (cons group (add-val-to-group val (rest groups) non-unifiable-pairs))))))))

;;; ======================================================================
;;;		OLD APPROACH - doesn't handle (x x x (at-most 2 x))
;;; ======================================================================
#|
The old approach was abandoned from this motivating example in Biology-KB-v224.fkm:

(a DNA-elongation) gives a wrong KM error:
     DNA1 &! DNA2
       (has-part (x y))  (has-part (a b))
   -> looping: Assuming (y &! b) to prove (y &! b)
   <-  has-part (x y b)		; NOTE: The assumption doesn't actually *do* the (y &! b), so we don't get obvious duplicates in the results
       FAIL constraint (exactly 2 DNA-strand)
I think we need to relax the constraint check to allow unifiability.
|#

#|
;;; [1] NOTE: There is a special case if N = 1, namely all the elements of all the expr-sets must be unifiable together.
(defun violated-cardinality-constraint (expr-sets constraint)
  (cond ((null expr-sets) nil)		; quick lookahead
	((and (singletonp expr-sets)
	      (<= (length (first expr-sets)) (second constraint))) nil) ; quick lookahead
	((and (eq (third constraint) '#$Thing)
	      (<= (length (remove-duplicates (remove-if #'constraint-exprp (append-lists expr-sets)))) (second constraint)))
;	 (km-format t "list = ~a~%" (remove-duplicates (remove-if #'constraint-exprp (append-lists expr-sets))))
	 nil)		; lookahead
	(t (let* ((n (second constraint))
		  (class (third constraint)) ; Nucleus
		  (expr-sets-in-class (remove nil (mapcar #'(lambda (exprs) (extract-exprs-in-class exprs class)) expr-sets))))
	     (cond
	      ((<= (length (remove-duplicates (append-lists expr-sets-in-class))) (second constraint)) nil)
	      (t (let ((bad-pair (some-are-not-unifiable (append-lists expr-sets-in-class))))
		   (cond ((null bad-pair) nil)			; everything's unifiable, so don't need to go further!
			 ((eq n 1) (list constraint bad-pair))	; failure, so stop
			 (t (violated-cardinality-constraint1 	; more sophisticated computation
			     (mapcar #'list (first expr-sets-in-class)) (rest expr-sets-in-class) constraint))))))))))
|#

(defun extract-exprs-in-class (exprs class)
  (remove-if-not #'(lambda (expr)
		     (cond ((existential-exprp expr)
			    (is-subclass-of (class-in-existential-expr expr) class))
			   ((fully-evaluatedp expr)
			    (isa expr class)))) ; includes numbers, sequences, etc.
		 exprs))

;;; Return a pair of ununifiable objects, if there are any
; (defun some-are-not-unifiable (vals)
;   (find-if #'(lambda (pair) (not (simple-unifiable (first pair) (second pair)))) (all-pairs vals))) ; or (all-adjacent-pairs <vals>) for speed

(defun non-unifiable-pairs (vals)
  (remove-if #'(lambda (pair) (simple-unifiable (first pair) (second pair))) (all-pairs vals))) ; or (all-adjacent-pairs <vals>) for speed

#|
INPUTS:
   constraint = (exactly N Class) or (at-most N Class)
   expr-sets = a set of sets that are to be unified together AND are all deemed to be in Class, e.g., ((_Atom1 _Atom2) (_Atom3) (_Atom4 _Atom5 _Atom6))
   combined: We gradually construct a representation of the && of the expr-sets, = a list where each element is a LIST of the unifiable entities, e.g.,
   	((_Atom1 & _Atom3) (_Atom2))
   However, for simplicity we don't include the "&" and just represent the list:
   	((_Atom1 _Atom3) (_Atom2))
   The length of the list = the expected length of the unification of the elements.
   Initially, combined = the listification of the FIRST entry in expr-sets, i.e.,
   	((_Atom1) (_Atom2))
   We then add to it.
RETURNS: (constraint vals) where vals is a subset of the values in expr-sets which violates constraint (and will then be reported to the user)

NOTE: There is a special case if N = 1, namely all the elements of all the expr-sets must be unifiable together, see [1] above

(defun violated-cardinality-constraint1 (combined expr-sets constraint)
  (let ((n (second constraint)))
    (cond ((> (length combined) n) (list constraint (append-lists combined))) ; violated!
	  (expr-sets
	   (let* ((exprs (first expr-sets))
		  (all-pairs (permute (list combined exprs))) ;(permute '((a b c) (d e)))->((a d) (a e) (b d) (b e) (c d) (c e))
		  (scored-pairs (remove nil
					(mapcar #'(lambda (pair)
						    (sc-score-pair (first pair) (second pair)))
						all-pairs)))
		  (ordered-scored-pairs (sort scored-pairs #'> :key #'third))
		  (new-combined (select-pairings ordered-scored-pairs combined exprs)))
	     (violated-cardinality-constraint1 new-combined (rest expr-sets) constraint))))))

;;; INPUT: xs = a list of to-be-unified objects (_Atom1 & _Atom2)
;;;      	For simplicity, we represent this just as (_Atom1 _Atom2)
;;;        y = another entity, e.g., _Atom3, that we'd like to add to the list.
;;; RETURNS: either a score for how "good" the unification would be, or NIL if it can't be done.
;;;      NOTE: We don't do a full &? test, but rather just test there are no violated constraints (partitions or /==).
;;;      Thus this is an "optimistic" guestimate about the unifiability of y into xs.
(defun sc-score-pair (xs y)
  (let ((scores (mapcar #'(lambda (x) (simple-unifiable x y)) xs)))
    (cond ((member nil scores) nil)	; some x and y are incompatible
	  (t `(,xs ,y ,(apply #'max scores))))))
|#

;;; INPUT: Two s-exprs
;;; RETURNS: either a score for how "good" the unification would be, or NIL if it can't be done.
(defun simple-unifiable (x y)
  (cond ((equal x y) 100)
	((and (atom y)
	      (atom x)
	      (incompatible-instances x y))
	 nil)
	(t (let* ((x-classes (cond ((kb-objectp x) (immediate-classes x))
				   ((existential-exprp x) (listify (class-in-existential-expr x)))))
		  (y-classes (cond ((kb-objectp y) (immediate-classes y))
				   ((existential-exprp y) (listify (class-in-existential-expr y))))))
	     (cond ((and x-classes y-classes (not (compatible-classes :classes1 x-classes :classes2 y-classes))) nil)
		   ((set-equal x-classes y-classes) 60)
		   ((intersection x-classes y-classes) 30)
		   ((some #'(lambda (x-class)
			      (some #'(lambda (y-class)
					(or (is-subclass-of x-class y-class)
					    (is-subclass-of y-class x-class)))
				    y-classes))
			  x-classes)
		    10)
		   (t 5))))))

#|
;;; vs1 is actually a list of lists
;;; RETURNS: ( <proposed bindings of V1s & V2s elements> <remainder of V1s and V2s> )
;;; Match up V1s = (x) with V2s = (y z).   (x y) has a higher score for a pairing
;;; e.g., (select-pairings (((x) y 60) ((x) z 10)) ((x)) (y z) )  -> ((x y) (z))
;;; NOTE: It won't check within-slot unifications, e.g., (y & z) will not be considered.
(defun select-pairings (ordered-scored-pairs vsets1 vs2)
  (cond
   ((endp ordered-scored-pairs) (append vsets1 (mapcar #'list vs2)))
   (t (let* ((best-pair (first ordered-scored-pairs))
	     (vs1 (first  best-pair))		; (x)
	     (v2 (second best-pair)))		; y
	(cond
	 ((and (member vs1 vsets1)		; not already done
	       (member v2 vs2))
	  `((,@vs1 ,v2)
	    ,@(select-pairings (rest ordered-scored-pairs) (remove vs1 vsets1 :test #'equal :count 1) (remove v2 vs2 :test #'equal :count 1))))
	 (t (select-pairings (rest ordered-scored-pairs) vsets1 vs2)))))))
|#
;;; ======================================================================

;;; USED only once by km-slotvals-from-kb in get-slotvals.lisp
;;; INPUT: An expr-set
;;; RETURNS: The expression set with (:default <expr>) statements removed, replaced with either
;;;	     the evaluation of <expr> or NIL depending on whether the evaluation is consistent with constraints or not
(defun evaluate-and-filter-defaults (expr-set constraints curr-vals slot &key single-valuedp)
  (cond ((some #'km-defaultp expr-set)
	 (mapcan #'(lambda (expr)
		     (cond ((km-defaultp expr)
			    (let* ( (vals (km-int (second expr)))
				    (new-vals (cond ((and single-valuedp curr-vals vals
							  (not (km-int `(,(first curr-vals) &? ,(first vals)))))
						     nil)
						    (t (remove-if-not #'(lambda (val)
									  (are-consistent-with-constraints (append curr-vals (list val))
													   (dereference constraints)
													   slot))
								      vals)))) )
			      (cond ((and (tracep) (not (equal vals new-vals)))
				     (km-trace 'comment "Discarding ~a (conflicts with constraint(s) ~a)" expr constraints)))
			      new-vals))
			   (t (list expr))))
		 expr-set))
	(t expr-set)))


;;; ======================================================================
;;;		TOGGLING THE CONSTRAINTS
;;; ======================================================================

(defun sanity-checks ()
  (cond (*sanity-checks* (format t "(Checking of `sanity-check' constraints is already switched on)~%"))
	(t (format t "(Checking of `sanity-check' constraints switched on)~%")
	   (km-setq '*sanity-checks* t)))
  '#$(t))

(defun no-sanity-checks ()
  (cond ((not *sanity-checks*) (format t "(Checking of `sanity-check' constraints is already switched off)~%"))
	(t (format t "(Checking of `sanity-check' constraints switched off)~%")
	   (km-setq '*sanity-checks* nil)))
  '#$(t))


;;; -------------------- for Shaken

;;; (pair-filter '#$((:pair 1 *foot) (:pair 2 *foot) (:pair 1 *yard) (:pair 2 *yard)))
;;; -> ((:|pair| 1 |*foot|) (:|pair| 1 |*yard|))
;;; Retain just first item
(defun pair-filter (vals &optional selected-so-far)
  (cond ((endp vals) nil)
	(t (let* ( (pair (first vals))
		   (units (arg2of pair)) )
	     (cond ((or (not (km-pairp pair))
			(notany #'(lambda (selected-pair)		; not selected a pair in this unit yet
				    (eq (arg2of selected-pair) units))
				selected-so-far))
		    (cons pair (pair-filter (rest vals) (cons pair selected-so-far))))
		   (t (pair-filter (rest vals) selected-so-far)))))))

