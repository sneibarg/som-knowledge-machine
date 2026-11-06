
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: subsumes.lisp
;;; Author: Peter Clark
;;; Purpose: Checking subsumption. This is slightly tricky to do properly.
;;; In this implementation, no unification is performed.

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

#|
Note we want to distinguish between
 a. "The car owned by a person." (the car with (owner ((a person))))
 b. "The car owned by person23." (the car with (owner ( _person23)))

We could evaluate (a person) to create a Skolem, and then do unification
with a subsumption flag in, but this doesn't work -- case a. and b. are
indistinguishable, but we'd want unification with _person24 (say) to succeed
in case a. and fail in b.

Handler for (the X with SVs) in interpreter.lisp:
-------------------------------------------------
  1. call subsumes (a X with SVs) to return an answer.
  2. If no answer returned, call (a X with SVs) to create it.

The base algorithm:
-------------------
;;; where subsumer-expr is form '(a Class with SlotsVals)
(defun is0 (subsumee-instance subsumer-expr)
1. find an object O of type Class (person)
2. for each slot S on person
    a. compute vals Vs of O.S
      for each expr in the value of person.S
	 IF expr is of form "(a ?class)" or "(a ?class with &rest)"
	 THEN foreach V in Vs
		call (subsumes expr V) until success (removing V from Vs?)
	 ELSE i. evaluate expr to find OVs
	      ii. check OVs is a subset of Vs (and if so remove OVs from Vs?)
		  (Note we're *not* allowing unification to occur)
3. If success, then return Subsumee-Instance
|#

;;; > (find-subsumees-on-object-stack '(a Car with (color (Red)))) -> list of instances
(defun find-subsumees-on-object-stack (existential-expr)
  (let ((candidates (find-candidates existential-expr)))
    (remove-if-not #'(lambda (candidate-instance)
		       (is0 candidate-instance existential-expr))
		   candidates)))

;;; > (find-subsumees+bindings '(a Car with (color (Red)))) -> list of instances + bindings
(defun find-subsumees+bindings (existential-expr candidates &key bindings)
  (remove nil
	  (mapcar #'(lambda (candidate-instance)
		      (let ((new-bindings (is0 candidate-instance existential-expr :bindings bindings)))
			(cond (new-bindings (list candidate-instance new-bindings)))))
		  candidates)))

;;; ------------------------------
#|
Finding all candidate instances which the existential expression might be referring to.
There are two ways of doing this:
	(a Car with
	   (owned-by (Porter))
	   (color (Brown))
	   (age (10))
  	   (parts ((a Steering-wheel with (color (Red))))))
  1. follow inverse links (Porter owns Car), (Brown color-of), (10 age-of)
     However, this is incomplete for two reasons:
	(i) the implicit (instance-of (Car)) relation isn't searched -- but we
		can add it in.
	(ii) it will miss some items starting with non-symbols, eg. (10 age-of).
  2. The answer(s) must be in the intersection of the answers returned, subject to:
	- we better also add (all-instance-of Car) to the set
	- if no instances are returned by a particular inversing, then we'll
		ignore it (assuming either it was a non-symbolic frame, or
		the evaluator has somehow failed to cache the answer even though
		it's there).
     INCOMPLETENESS: Suppose (Brown color-of) *does* return some values, but
	  not including this Car (eg. this Car is an embedded unit? We'll
	  fail then. Depends on how complete/efficient we want this.
 Now we just do this simple version below:
|#
(defun find-candidates (existential-expr)
  (let*
    ( (class+slotsvals (breakup-existential-expr existential-expr :fail-mode 'error))  ; [1]
      (class (first class+slotsvals))
      (slotsvals (second class+slotsvals)) )
    (mapc #'(lambda (slotvals)         	      	  ; this will force some evaluation
	      (find-candidates2 class slotvals))  ; of relevant frames
	  slotsvals)
;;; (all-instances class)))
;;; NEW: Only instances on obj-stack are possible candidates, so obj-stack defines the context
    (remove-if-not #'(lambda (instance) (isa instance class)) (obj-stack))))

;;; STRIPPED VERSION:
;;; [1] kb-objectp test to avoid (the part-number-of of 1)
;;; PURPOSE: to force some evaluation of relevant frames
;;; RETURNS: Irrelevant and discarded
(defun find-candidates2 (class slotvals)
  (let* ( (slot (first slotvals))
 	  (invslot (invert-slot slot))
	  (vexprs (second slotvals)) )
     (mapc #'(lambda (vexpr)
	       (cond ((existential-exprp vexpr)
		      (mapc #'(lambda (val)
				(cond ((kb-objectp val)
				       (km-int `(#$the ,class ,invslot #$of ,val)))))	 ; [1]
			    (find-subsumees-on-object-stack vexpr)))
		     (t (let ( (kb-vals (remove-if-not #'kb-objectp (km-int vexpr))) )	; [1]
			  (cond (kb-vals (km-int `(#$the ,class ,invslot #$of ,(vals-to-val kb-vals)))))))))  ; [2]
	   vexprs)))

#|
 ======================================================================
		SUBSUMPTION TESTING
 ======================================================================

This below table gives the rules for transforming different forms of the expression
into the BASE IMPLEMENTATION for "is0":

SUBSUMES:
	('(every X) subsumes '(every Y))	== ('(a Y) is '(a X))
	('(every X) subsumes {I1,..,In})	== (allof {I1,..,In} must ('(every X) covers It))
	({I1,..,In} subsumes '(every Y))	== ERROR
	({I1,..,In} subsumes {J1,..,Jn})	== ({I1,..,In} is-superset-of {J1,..,Jn})
COVERS:
	('(every X) covers '(a Y))    ==    ('(a Y) is '(a X))
	('(every X) covers    I  )    ==    (I is '(a X))
	({I1,..,In} covers '(a Y))    ==    (has-value (oneof {I1,..,In} where (It is '(a Y))))
	({I1,..,In} covers    I  )    ==    ({I1,..,In} includes I)
IS:
	('(a Y) is '(a X))	 ==     gensym a YI, (YI is '(a X)), delete YI
	('(a Y) is   I   )	 ==     ERROR
	(  I    is '(a X))	 == 	*****BASE IMPLEMENTATION***** : (is0 I '(a X))
	(  I1   is   I2  )	 ==     (I1 = I2)

We also have to be careful: With (Animal subsumes Dog), we must be sure that the
set (Animal) is recognized as a class description, not a set of instances. To do
this, we convert (say) Dog to '(every Dog).
|#

(defun subsumes (xs ys)
  (let ( (x-desc (vals-to-class-description xs))
	 (y-desc (vals-to-class-description ys)) )
    (cond ((and x-desc y-desc) 				        ; ('(every X) subsumes '(every Y)) == ('(a Y) is '(a X))
	   (is (every-to-a y-desc) (every-to-a x-desc)))
	  (x-desc 						; ('(every X) subsumes {I1,..,In}) == (allof {I1,..,In}
	   (km-int `#$(allof ,(VALS-TO-VAL YS) must (,X-DESC covers It))))    ;           must ('(every X) covers It))
	  (y-desc						; ({I1,..,In} subsumes '(every Y)) == ERROR
	   (report-error 'user-error "Doing (~a subsumes ~a)~%Can't test if a set subsumes an expression!~%" xs ys))
	  (t 							; ({I1,..,In} subsumes {J1,..,Jn}) == ({I1,..,In} is-superset-of {J1,..,Jn})
	   (km-int `#$(,(VALS-TO-VAL XS) is-superset-of ,(VALS-TO-VAL YS)))))))

(defun covers (xs y)
  (let ( (x-desc (vals-to-class-description xs))
	 (y-desc (cond ((and (quoted-expressionp y) (listp (unquote y)) (instance-descriptionp y :fail-mode 'error)) y))) )		; instance-descriptionp will report error if necc.
    (cond ((and x-desc y-desc)					; ('(every X) covers '(a Y))    ==    ('(a Y) is '(a X))
	   (km-int `#$(,Y-DESC is ,(EVERY-TO-A X-DESC))))
	  (x-desc						; ('(every X) covers    I  )    ==    (I is '(a X))
	   (km-int `#$(,Y is ,(EVERY-TO-A X-DESC))))
	  (y-desc						; ({I1,..,In} covers '(a Y))    ==    (has-value (oneof {I1,..,In}
	   (km-int `#$(has-value (oneof ,(VALS-TO-VAL XS) where (It is ,Y-DESC)))))   ;  where (It is '(a Y)))
	  (t 			       				; ({I1,..,In} covers    I  )    ==    ({I1,..,In} includes I)
	   (km-int `#$(,(VALS-TO-VAL XS) includes ,Y))))))

;;; [1]: Hmmm....We can't always guarantee KM will clean up after itself, as the computation [1a] may create additional
;;; instances which *aren't* deleted by the tidy-up [1b]. Could use a subsituation??
(defun is (x y)
  (cond
   ((equal y ''#$(a Class))				; SPECIAL CASE - for metaclasses:  '(every Dog) is '(a Class)
    (cond ((or (class-descriptionp x) (symbolp x)))	; succeed
	  (t (report-error 'user-error "Doing (~a is ~a)~%~a doesn't appear to be a class or class description.~%" x y x))))
   (t (let ( (x-desc (cond ((and (quoted-expressionp x) (listp (unquote x)) (instance-descriptionp x :fail-mode 'error)) x)))
	     (y-desc (cond ((and (quoted-expressionp y) (listp (unquote y)) (instance-descriptionp y :fail-mode 'error)) y))) )
	(cond ((and x-desc y-desc)					; ('(a X) is '(a Y))	 ==     gensym a XI, (XI is '(a Y)), delete XI
	       (description-subsumes-description x-desc y-desc))
	      (x-desc						; ('(a X) is   I   )	 ==     ERROR
	       (report-error 'user-error "Doing (~a is ~a)~%Can't test if an expression is `subsumed' by an instance!~%" x y))
	      (y-desc						; (  I    is '(a Y))	 == 	*****BASE IMPLEMENTATION*****
	       (is0 x (unquote y-desc)))
	      (t (km-int `#$(,X = ,Y))))))))		; (  I1   is   I2  )	 ==     (I1 = I2)

;;; ----------------------------------------
;;; Rewrite this to me more efficient - delete-frame is horrible for a large KB
;;; ----------------------------------------

#| [1] NB Not set it to NIL, in case this is recursive, to avoid:
 logging on, checkpoint C1
   logging on (already on), checkpoint C2
   backtrack to C2, logging off (urgh!)
 backtrack to C1, but some logging has been missed!
|#

(defparameter *remove-temporary-via-backtracking* t)

(defun description-subsumes-description (x-desc y-desc)
  (cond
   (*remove-temporary-via-backtracking*
    (let ( (old-internal-logging *internal-logging*)
	   (checkpoint-id (gensym)) )
      (setq *internal-logging* t)
      (set-checkpoint checkpoint-id)
      (prog1
	  (let ( (tmp-i (km-unique-int (unquote x-desc) :fail-mode 'error)) )
	    (km-int `#$(,TMP-I is ,Y-DESC)))
	(undo checkpoint-id)		; undo, whatever
	(setq *internal-logging* old-internal-logging))))	; [1]
   (t (let ( (tmp-i (km-unique-int (unquote x-desc) :fail-mode 'error)) )
	(prog1
	    (km-int `#$(,TMP-I is ,Y-DESC)) ; [1a]
	  (delete-frame tmp-i))))))			; VERY inefficient with a large KB

;;; ----------------------------------------

; [1] Causes problems with metaclasses!
(defun vals-to-class-description (classes)
  (cond ((and (singletonp classes)
	      (kb-objectp (first classes)))
; [1]	      (not (is-an-instance (first classes))))
	 `'(#$every ,(first classes)))					; (Dog) -> '(every Dog)
	((and (singletonp classes)
	      (descriptionp (first classes)))
	 (cond ((class-descriptionp (first classes))
		(let* ( (class+slotsvals (class-description-to-class+slotsvals (first classes)))
			(class (first class+slotsvals))
			(slotsvals (second class+slotsvals)) )
		  `'(#$every ,class #$with ,@slotsvals)))
	       (t (report-error 'user-error "Subsumption with ~a:~%Don't know how to do subsumption with this kind of expression!~%"
				(first classes)))))))

;;; '(every Cat) -> '(a Cat)
;(defun every-to-a (expr) `'(#$a ,@(rest (unquote expr))))
(defun every-to-a (expr)
  (let* ( (class+slotsvals (class-description-to-class+slotsvals expr))
	  (class (first class+slotsvals))
	  (slotsvals (second class+slotsvals)) )
    (cond (slotsvals `'(#$a ,class #$with ,@slotsvals))
	  (t `'(#$a ,class)))))

;;; ======================================================================
;;;	BASE IMPLEMENTATION FOR SUBSUMPTION TESTING: COMPARE AN INSTANCE WITH A DESCRIPTION
;;; ======================================================================

#|
NEW: RETURNS: binding list
[1] bind-self done for queries like:
CL-USER> (is0 '#$_rectangle0
	      '#$(a rectangle with (length ((Self width)))
				   (width ((Self length)))))

Later: CORRECTION! bind-self must be done *before* calling is0,
	as expr may be an embedded expression (thus Self refers to the
	embedding frame).
[2] NB if no value in subsumer, then it *doesn't* subsume everything!!
NOTE: expr is UNQUOTED here, to allow easy recursive calling of is0

[3] del-list
      expr     (:triple  Self   position (a Position))		    (a Position) is a single value
      instance (:triple _Light1 position (the position of _Light1)) is going to return a *list* of values for the third argument
|#
(defun is0 (instance expr &key (bindings *null-bindings*))
  (cond ((and (km-structured-list-valp instance)
	      (km-structured-list-valp expr)
	      (= (length (desource instance)) (length (desource expr)))
	      (eql (first instance) (first expr)))
	 (let ( (d-instance (desource instance))
		(d-expr (desource expr)) )
	   (cond ((km-triplep d-instance)
		  (let* ((bindings2 (is0  (second d-instance) (second d-expr) :bindings bindings))
			 (bindings3 (cond
				     (bindings2
				      (is0 (third d-instance) (third d-expr) :bindings bindings2))))
			 (bindings4 (cond
				     (bindings3
				      (some #'(lambda (val) ; See [3] above
						(is0 val (fourth d-expr) :bindings bindings3))
					    (val-to-vals (fourth d-instance)))))))
		    bindings4))
		 (t (is0s (rest (transpose (list d-instance d-expr)))  ; ((:seq :seq) (i1 e1) (i2 e2) ... )
			  :bindings bindings)))))

; Below [1], bind-self *may* appear redundant. However, expr
; *may* contain Self, if it came from a top-level query eg.
; 	KM> ((a Person with (owns (Self))) is (a Person with (owns (Self))))
;     (cond
;      ((not (contains-self-keyword expr))
;	(km-format t "ERROR! Don't know how what `Self' refers to in the expression~%")
;	(km-format t "ERROR! ~a~%" expr))

	 (t (let ( (class+slotsvals (bind-self (breakup-existential-expr expr) instance)) )   ; [1]
	      (cond (class+slotsvals				;;; 1. An INDEFINITE expression
		     (let ((class (first class+slotsvals))		;;;    (so do subsumption)
			   (slotsvals (second class+slotsvals)) )
		       (and (isa instance class)
			    (are-slotsvals slotsvals) ; syntax check
			    (slotsvals-subsume slotsvals instance :bindings bindings))))
		    ((constraint-exprp expr)
		     (cond ((satisfies-constraints (list instance) (list expr) nil) ; nil = dummy slot name. This only
			    bindings)))                      ; occurs for things like (is0 (:seq 1 2) (:seq (<> 1) 2))
;;;		    (t (let ( (definite-val (km-unique-int expr :fail-mode 'error)) )  ;;; 2. a DEFINITE expression
;;; Why 'error above??
		    (t (let ( (definite-val (km-unique-int expr)) )  ;;; 2. a DEFINITE expression
			 (cond ((null definite-val) nil)	; [2]		    ;;;    (so do equality)
			       ((equal definite-val instance) bindings)))))))))

;;; Perhaps rather slow?
;;; Returns 't' in the keyword 'Self' occurs in expr, nil otherwise.
(defun contains-self-keyword (expr)
  (cond ((null expr) nil)
	((eq expr '#$Self))
	((and (listp expr)
	      (not (sourcep expr)))		; NEW: May contain Self, but that's ok
	 (some #'contains-self-keyword expr))))

;;; ----------

(defun is0s (pairs &key (bindings *null-bindings*))
  (cond ((null pairs) bindings)
	(t (let* ((pair (first pairs))
		  (bindings2 (is0 (first pair) (second pair) :bindings bindings)))
	     (cond (bindings2 (is0s (rest pairs) :bindings bindings2)))))))

(defun slotsvals-subsume (slotsvals instance &key (bindings *null-bindings*))
  (cond ((endp slotsvals) bindings)
	(t (let* ((slotvals (first slotsvals))
		  (bindings2 (slotvals-subsume slotvals instance :bindings bindings)))
	     (cond (bindings2 (slotsvals-subsume (rest slotsvals) instance :bindings bindings2)))))))

#|
(slotvals-subsume <subsumer> <subsumee>
[1] is a quick, common lookahead, for calls like:
	(slotvals-subsume '#$(connects ((the Engine parts of _Car23))) '#$_Car23)
where the connects of _Car23 is exactly ((the Engine parts of _Car23)).
[2] Don't count constraints! eg. Want (<> 20) to subsume () !
    Thus, we abort if (the foo of Self) - NIL, on the assumption that (the foo of Self) will return at least one item (?).
	This assumption isn't valid! So simplify this to just count existentials.
    The only case this doesn't hold is for the special `tag' slot. And in any case, see-constraints have been already removed by the
	KM call at [4b]!
    But: Put it back. Reason is we want to stop this:
	KM> (_Car23 is '(a Car with (color ((the favorite-color of (the owner of Self))))))

	KM> (every Nice-Car has-definition
		  (instance-of (Car))
		  (color ((the favorite-color of (the owner of Self)))))

	KM> (a Car)
	CLASSIFY: _Car23 is a Nice-Car!

	This slightly violates the semantics of the KB (strictly null attribute
	values should be ignored), but we assume that the rule is there for a
	reason and must return at least one value.
    3/17/09: CHANGED to simple removal of constraints: remove-constraints is valid only for fully evaluated
	expressions (see that function), but here we do NOT have fully evaluated expressions.
	Specifically: (remove-constraints '#$((?x == (a Point)))) -> (?x (a Point)), has length 2, so
           will thus (undesirably) fail to match (_Point23). Note that the error here is in the use of
	   remove-constraints with this expression, as it is NOT fully evaluated.

[4a] Do a find-vals rather than a (km-int ...) call, as we *do* want to preserve constraints here in the
     special case of tags.
[5] Why ignore situation-specific slots? I'm confused why I put this constraint in. Let's remove it.
|#
(defun slotvals-subsume (slotvals instance &key (bindings *null-bindings*))
  (let* ( (slot (first slotvals))
          (ser-exprs (second slotvals)) )
    (cond
     ((some #'(lambda (situation)							; [1]
		(equal ser-exprs (get-vals instance slot :situation situation)))
	    (cons (curr-situation) (append (all-supersituations (curr-situation)) (visible-theories))))
      bindings)
;     ((not (situation-specificp slot))							; otherwise fail it out
; [5]
     (t (let ((see-vals (cond ((ignore-slot-due-to-situations-mode slot)
				  (km-trace 'comment "Subsumption test: Ignoring attempt to compute (the ~a of ~a) in the global~%    situation, as slot `~a' is a fluent (so can only take on situation-specific values)." slot instance slot))
				 (t (km-int `#$(the ,SLOT of ,INSTANCE))))) )		; [4b]
;	    (cond ((<= (length (remove-if-not #'existential-exprp ser-exprs)) (length see-vals)); quick look-ahead [2]
;	    (cond ((<= (length (remove-constraints ser-exprs)) (length see-vals))	; quick look-ahead check [2]
	    (cond ((<= (length (remove-if #'constraint-exprp ser-exprs)) (length see-vals)) ; quick look-ahead check [2]
		   (cond ((eq slot '#$instance-of) ; special case
			  (cond ((classes-subsume-classes ser-exprs see-vals) bindings))) ; assume no evaln needed
			 (t (let ((constraints (find-constraints-in-exprs ser-exprs))
				  (incompletep (or (member '#$:incomplete (get-vals instance slot))
						   (member '#$:incomplete (get-vals instance slot :situation *global-situation*)))))
			      (and (satisfies-constraints see-vals constraints slot :incompletep incompletep) ; [3]
				   (vals-subsume (cond ((single-valued-slotp slot)
							(&-expr-to-vals (first ser-exprs)))  ; eg. ((a Car) & (must-be-a Dog))
						       (t ser-exprs))
						 see-vals
						 :bindings bindings))))))))))))

#|
GIVEN: some expressions, and some values
RETURN t if *every* expression subsumes some (different) value in values.
Notes:
[1]: if expr includes, say, (a car), then consider it to subsume the first
instance of car in the subsumee.
[2]: Don't remove ser-vals from see-vals, as subsumer may have several
exprs which evaluate to the *same* instance:
eg. in (expr1 expr2), expr1 evals to (x1 x2) and expr2 evaluates (x2 x3)
But if we remove (x1 x2) from see-vals (x1 x2 x3 x4) we get (x3 x4),
and now (subsetp '(x2 x3) '(x3 x4)) undesirably fails, even though x2
is known to be in the full set see-vals.
NOTE: (vals-subsume '(?x) '(_X1)), ?x unbound: -> bind ?x to _X1
      (vals-subsume '(?x) '(_X1)), ?x   bound: -> check ?x = _X1
      (vals-subsume '((?x == (a Car))) '(_X1)), ?x   bound: -> check ?x = _X1 AND _X1 is (a Car)
|#
(defun vals-subsume (ser-exprs see-vals &key (bindings *null-bindings*) current-var)
  (cond
   ((endp ser-exprs) bindings)			; success!!
   ((equal ser-exprs see-vals) bindings)		; quick success - don't need to recurse
   (t (let ( (ser-expr (first ser-exprs)) )
	(cond ((or (existential-exprp ser-expr)
		   (km-structured-list-valp ser-expr))	; DON'T evaluate structured vals, preserve existentials in them
	       (let* ((see-val+new-bindings (first (find-subsumees+bindings ser-expr see-vals :bindings bindings))) ; [1]
		      (see-val (first see-val+new-bindings))
		      (new-bindings (second see-val+new-bindings)))
		 (cond (see-val
			(vals-subsume (rest ser-exprs)
				      (remove see-val see-vals :test #'equal)
				      :bindings (cond (current-var (add-binding current-var see-val new-bindings))
						      (t new-bindings)))))))
	      ((km-varp ser-expr)
	       (let ((binding (val-of ser-expr bindings)))
		 (cond (binding
			(cond ((member binding see-vals :test #'equal)
			       (vals-subsume (rest ser-exprs) (remove binding see-vals) :bindings bindings))))
		       (see-vals
			(vals-subsume (rest ser-exprs) (rest see-vals)  ; bind FIRST var only - no search :-(
				      :bindings (add-binding ser-expr (first see-vals) bindings))))))
	      ((and (listp ser-expr)
		    (km-varp (first ser-expr)))
	       (cond ((minimatch ser-expr '(?var == ?expr))
		      (let* ((var (first ser-expr))
			     (expr (third ser-expr))
			     (var-binding (val-of var bindings)))
			(cond (var-binding
			       (and (member var-binding see-vals)
				    (vals-subsume (list expr) (list var-binding))
				    (vals-subsume (rest ser-exprs) (remove var-binding see-vals) :bindings bindings)))
			      (t (vals-subsume (cons expr (rest ser-exprs)) see-vals
					       :bindings bindings :current-var var)))))
		     (t (report-error 'user-error
			  "Bad use of a variable in subsumption expression ~a~%Expression must be of the form <var> or (<var> == <expr>)" ser-expr))))
	      (t (let ( (ser-vals (km-int ser-expr)) )
		   (cond ((subsetp ser-vals see-vals :test #'equal)
			  (let ((new-bindings
				 (cond
				  (current-var
				   (cond ((null ser-vals)
					  (report-error 'nodebugger-error
						       "~a == ~a == NIL in subsumption expression; ignoring ~a...~%"
						       current-var ser-expr current-var))
					 (t (cond ((>= (length ser-vals) 2)
						   (report-error 'nodebugger-error
						      "~a == ~a == ~a (multiple values!) in subsumption expression~%Just setting ~a == ~a (the first value)...~%"
						       current-var ser-expr ser-vals current-var (first ser-vals))))
					    (add-binding current-var (first ser-vals) bindings))))
				  (t bindings))))
			  (vals-subsume (rest ser-exprs) see-vals :bindings new-bindings))))))))))) ; [2]

;;; ======================================================================
;;;		UTILS
;;; ======================================================================

;;; If expr is an existential expr, this returns a list (<class> <slotsvals>) of
;;; the existential expr's structure.
;;; (breakup-existential-expr '(a car with (age (old)))) ->  (car ((age (old))))
(defun breakup-existential-expr (expr0 &key (fail-mode 'fail))
 (let ( (expr (desource+decomment-top-level expr0)) )
  (cond ((and (listp expr)
	      (member (first expr) '#$(a some))
	      (>= (length expr) 2))
	 (cond ((pairp expr) (list (second expr) nil))
	       ((eq (third expr) '#$with) (list (second expr) (rest (rest (rest expr)))))
	       ((and (eq (third expr) '#$called) (= (length expr) 4)) (list (second expr) `((#$called (,(FOURTH EXPR))))))
	       ((and (eq (third expr) '#$uniquely-called) (= (length expr) 4)) (list (second expr) `((#$uniquely-called (,(FOURTH EXPR))))))
	       ((and (eq (third expr) '#$called) (eq (fifth expr) '#$with))
		(list (second expr) (cons `(#$called (,(FOURTH EXPR))) (rest (rest (rest (rest (rest expr))))))))
	       ((and (eq (third expr) '#$uniquely-called) (eq (fifth expr) '#$with))
		(list (second expr) (cons `(#$uniquely-called (,(FOURTH EXPR))) (rest (rest (rest (rest (rest expr))))))))
	       ((eq fail-mode 'error)
		(report-error 'user-error "Bad expression in subsumption testing ~a~%(Should be one of (a ?class) or (a ?class with &rest)).~%" expr))))
	((eq fail-mode 'error)
	 (report-error 'user-error "Bad expression in subsumption testing ~a~%(Should be one of (a ?class) or (a ?class with &rest)).~%" expr)))))

;;; No error checking here
(defun class-in-existential-expr (existential-expr)
  (second existential-expr))

;;; ======================================================================
;;; Syntactic sugar:
;;; Can say	(the (Self parts Wing parts Engine))	; the engine of a wing
;;; as well as (and equivalently)
;;;	        (the Engine with (parts-of ((a Wing with (parts-of (Self))))))
;;; ======================================================================

#|
> (path-to-existential-expr '(airplane01 parts wing))
(a wing with (parts-of (airplane01)))
> (path-to-existential-expr '(airplane01 parts wing parts edp))
(a edp with (parts-of ((a wing with (parts-of (airplane01))))))
> (path-to-existential-expr '(airplane01 parts wing parts))
(a thing with (parts-of ((a wing with (parts-of (airplane01))))))
|#
(defun path-to-existential-expr (path &optional (prep '#$a))
  (path-to-existential-expr2 (rest path) (first path) prep))

(defun path-to-existential-expr2 (path embedded-unit prep)
  (cond ((endp path) embedded-unit)
	(t  (let* ( (slot (first path))
		    (class (cond ((eq (second path) '*) '#$Thing)
				 ((second path))
				 (t '#$Thing)))
		    (rest-rest-path (rest (rest path)))
		    (preposition (cond (rest-rest-path '#$a) (t prep)))
		    (new-embedded-unit `(,preposition ,class with
						      (,(invert-slot slot) (,embedded-unit)))) )
	      (path-to-existential-expr2 (rest (rest path)) new-embedded-unit prep)))))

;;; ======================================================================
;;;		REMOVE SUBSUMING EXPRESSIONS
;;;	This is called by (compute-new-slotsvals old-slotsvals old-slotsvals) in frame-io.lisp
;;; ======================================================================
#|
remove-subsuming-exprs:
GIVEN:
   "exprs"     - a set of existential exprs (plus some other exprs)
   "instances" - a set of instances (plus some other exprs)

 Returns three values:
	   - the existential exprs (plus other exprs) not subsuming any instances
	   - the instances (plus other exprs) not subsumed by any existential expr
	   - the instances which were subsumed

CL-USER> (remove-subsuming-exprs '#$((a Cat) (a Door))
				 '#$(_Door178 (a Elephant) _Bumper176))
((a Cat))
((a Elephant) _Bumper176)
(_Door178)
[1] an instance can only be subsumed by *one* expr
[2] route this query through the KM interpreter, so the user can trace it if necessary
    BUT: 9.8.99 is very confusing to the user! Hide it instead.

NOTE!! This routine should have NO SIDE EFFECTS, beyond evaluating definite paths already present.

Apr 99: What we'd also like is:
CL-USER> (remove-subsuming-exprs '#$((a Cat) (a Door) (a Elephant))
				 '#$(_Door178 (a Elephant with (size (Big))) _Bumper176))
  CURRENT IMPLEMENTATION				DESIRED
((a Cat) (a Elephant))			 	((a Cat))				  ; non-subsumers
((a Elephant with size (Big)) _Bumper176)	(_Bumper176)				  ; non-subsumed
(_Door178)					((a Elephant with (size (Big))) _Door178) ; subsumed

[3] is more aggressive, it will cause a "hidden" instance to be actually created for purposes of testing, then discarded

[4] This extra check to ensure (a Big-Engine) "subsumes" (_Engine23). This is modifying "subsuming" to mean
    "subsumes including allowing coercion". Note that (_Engine23) and (_Engine24) still *shouldn't* result in
    any removals, ie. we're *not* doing unification.
   eg. consider (Red color-of _Engine23) then (Red color-of _Engine24) ; don't want to unify the Engines.

[4b] NOTE We have to exclude subsumption checks which include reference to Self, because the answer to the
     subsumption check depends on the instance in question!
- PC This can only come with instances entered from the user, not from lazy-unifiable-expr-sets (where bind-self has
  PC necessarily already been conducted).

[5] Clean up the junk, so as not to pollute the object stack.

[6] Incorrect behaviour:
 ('(a Car) is '(a Car with (age ((the foo of Self)))))  -> NIL	; correct
but
 (every Car has (age ((a Thing))))
 ('(a Car) is '(a Car with (age ((the foo of Self)))))  -> t    ; incorrect!
This is because KM treats this as equivalent to
 ((a Car) is '(a Car with (age ((the foo of Self)))))
which is wrong!!!

[7a] It looks like we should record explanation here, but we don't need to as &+ takes care of it.
[7b] As far as I can tell this branch NEVER gets taken with &+, as Self will always be removed, allow-coercion is always t, and &+ is stronger than is.
	(So if &+ fails, `is' will too, necessarily)
|#
(defun remove-subsuming-exprs (exprs instances &key allow-coercion target eagerlyp)
 (cond ((and (tracep) (not (tracesubsumesp)))
	(let ((*trace* nil))
	  (remove-subsuming-exprs0 exprs instances :allow-coercion allow-coercion :target target :eagerlyp eagerlyp)))
       (t (remove-subsuming-exprs0 exprs instances :allow-coercion allow-coercion :target target :eagerlyp eagerlyp))))

(defun remove-subsuming-exprs0 (exprs instances &key allow-coercion target eagerlyp)
  (cond
   ((or (null exprs) (null instances)) (values exprs instances nil))
   (t (let*
	  ( (subsumed-instance
	     (cond ((or (existential-exprp (first exprs))
;			(km-triplep (first exprs)))
			(km-structured-list-valp (first exprs)))
		    (find-if #'(lambda (instance)
				 (cond
				  ((is-an-instance instance)		; NB includes (:args foo) and (:triple a b c)
				   (or
;;; PC CAN I safely get rid of this expensive and
;;; PC confusing test? -> ...turns out for big KBs, it's actually cheaper to do this test!
;				       (km-int `#$(,INSTANCE is ',(FIRST EXPRS)))
				       (and allow-coercion ; [4]
#| hmm...|#				    (or (existential-exprp (first exprs))
						(km-structured-list-valp (first exprs)))
					    (not (contains-self-keyword (first exprs)))	; [4b]
					    (km-int `(,instance ,(cond (eagerlyp '&+!) (t '&+)) ,(first exprs))
						    :target target)
					; NOTE: no record-explanation here [7a]
					    )))

				  ((and (existential-exprp instance)
					(not (contains-self-keyword (first exprs))))		; [6]
;				   (km-format t "**HERE!!**~%")
				   (km-int `#$(',INSTANCE is ',(FIRST EXPRS)))))) ; Test - if passed, can drop instance
			     ; NOTE: no record-explanation here [7b]
			     instances))))
	    (instances0 (cond (subsumed-instance (remove subsumed-instance instances :test #'equal :count 1))
			      (t instances))) )
	(multiple-value-bind
	 (unused-exprs unused-instances subsumed-instances)
	 (remove-subsuming-exprs0 (rest exprs) instances0 :allow-coercion allow-coercion :target target :eagerlyp eagerlyp)
	 (cond (subsumed-instance
		(cond ((and target *record-explanations*)
		       (record-explanation-for target subsumed-instance (first exprs))))
		(values unused-exprs unused-instances (cons subsumed-instance subsumed-instances)))
	       (t (values (cons (first exprs) unused-exprs) unused-instances subsumed-instances))))))))

;;; Quick lookahead for _Engine23 (a Engine) : the immediate-classes of _Engine23 must subsume or be subsumed by Engine.
;;; If this test fails, then we needn't proceed further.
;;; expr is necessarily of the form (a <class>), or (a <class> with ...)
;(defun classes-subsumep-test (instance expr)
;  (let ( (i-classes (immediate-classes instance))
;	 (e-classes (list (second expr))) )
;    (or (classes-subsume-classes e-classes i-classes)
;	(classes-subsume-classes i-classes e-classes))))

;(defun classes-subsumep-test (i-classes e-classes)
;  (or (equal i-classes e-classes)				; for efficiency
;      (classes-subsume-classes e-classes i-classes)
;      (classes-subsume-classes i-classes e-classes)))

;;; ======================================================================
;;; Compute most general specialization(s) of a concept description
;;; Used for KM> (the-class-of ...) expressions.
;;; Not used for now.
;;; ======================================================================

#|
The class has to be input as an instance expression.
mgs returns the most general class(es) subsumed by that expression.
The algorithm searches down the taxonomy (general-to-specific) from the
class provided, until it hits candidates. Instances are not searched.

The algorithm is similar to finding subsumed instances, except the
candidates are classes, and we instant-ify them.

CL-USER> (mgs '#$(a Physobj with (produces (*Electricity))))
(Power-Supply)

;;; Return most general class(es) subsumed by existential-expr.
(defun mgs (existential-expr)
  (let*
    ( (class+slotsvals (breakup-existential-expr existential-expr :fail-mode 'error))
      (class (first class+slotsvals)) )
    (cond (class (remove-duplicates (mgs2 existential-expr class))))))

;;; Return most general subclass(es) of class subsumed by existential-expr.
(defun mgs2 (existential-expr class)
  (mapcan #'(lambda (subclass)					; WAS my-mapcan - #'mapcan safe here!
	      (cond ((is0 (km-unique-int `#$(a ,SUBCLASS) :fail-mode 'error) existential-expr) (list subclass))
		    (t (mgs2 existential-expr subclass))))
  (km-int `#$(the subclasses of ,CLASS))))
|#

;;; ======================================================================

(defun valset-subsumes-valset (valset1 valset2)
  (cond
   ((endp valset1))
   ((null valset2) nil)			; some valset2 without correlates in valset1
   (t (let ( (val1 (first valset1)) )
	(cond ((member val1 valset2 :test #'equal)
	       (valset-subsumes-valset (rest valset1) (remove val1 valset2 :test #'equal :count 1)))
	      ((existential-exprp val1)
	       (let ( (val2 (find-if #'(lambda (val)
					 (cond ((is-an-instance val) (is0 val val1))		; takes an instance and an (unquoted) expr
					       ((existential-exprp val) (is `',val `',val1))))
				     valset2)) )
		 (cond (val2 (valset-subsumes-valset (rest valset1) (remove val2 valset2 :test #'equal :count 1)))))))))))

#|
;;; More efficient but less thorough, expecting ordering to be preserved.
;;; val2 is more specific than val1
(defun valset-subsumes-valset (valset1 valset2)
  (cond
   ((endp valset1))
   ((null valset2) nil)			; some valset2 without correlates in valset1
   (t (let ( (val1 (first valset1))
	     (val2 (first valset2)) )
	(cond ((equal val1 val2)
	       (valset-subsumes-valset (rest valset1) (rest valset2)))
	      ((existential-exprp val1)
	       (let ( (successp (cond ((is-an-instance val2) (is0 val2 val1))		; takes an instance and an (unquoted) expr
				      ((existential-exprp val2) (is `',val2 `',val1)))) )
		 (cond (successp (valset-subsumes-valset (rest valset1) (rest valset2)))))))))))
|#
