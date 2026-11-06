
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: get-slotvals.lisp
;;; Author: Peter Clark
;;; Purpose: Basic searching for the value of a slot

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; ----------
;;; Control use of inheritance...
;(defparameter *use-inheritance* t)		; moved to header.lisp
;(defparameter *use-prototypes* t)		; moved to header.lisp

(defun use-inheritance ()
  (and *use-inheritance*
       (not (am-in-prototype-mode))))	; no inheritance within prototype mode

(defun use-prototypes ()
  (and *use-prototypes*
       (not (am-in-prototype-mode))))	; no inheritance within prototype mode

;;; ----------

#|
The length and ugliness of the below code is mainly due to the desire to
put in good tracing facilities for the user, rather than the get-slotvals
procedure being intrinsically complicated.

There are six sources of information for finding a slot's value:

  0. PROTOTYPES: special form of representation
  1. PROJECTION: from the previous situation
  2. SUBSLOTS: find values in the slot's subslots.
  3. SUPERSITUATIONS: Import value(s) from the current situation's supersituations
  4. LOCAL VALUES: currently on the slot
  5. INHERITANCE: inherit rules from the instance's classes.

There are two caveats:
  1. We want to make an intermediate save of the results of 1-4 before adding in 5,
	to avoid a special case of looping during subsumption checks.
  2. If the slot is single-valued, then the projected value (1) should not be
	automatically combined in. Instead, (2-5) should first be computed, then
 	if (1) is consistent with the combination of (2-5), it should be then unified
	in, otherwise discarded.
     The procedure which handles this special case of projection is maybe-project-value.

----------------------------------------

The procedure was rewritten in April 99 to show more clearly to the user what KM
was doing during the trace, although it makes the actual source code less clear (perhaps?).
|#

;;; ======================================================================

(defun km-slotvals-from-kb (instance0 slot &key fail-mode &aux (n 0))	; n for tracing purposes
 (declare (ignore fail-mode))

;;; New pre-classify...
; Neah, not really more efficient...
;  (classify instance0 :slot-of-interest slot)
								; PRELIMINARIES
  (let* ((single-valuedp (single-valued-slotp slot))		; (i) get the slot type
	 (multivaluedp (not single-valuedp))
	 (combine-values-by-appendingp (combine-values-by-appending-slotp slot))

;;; WAS 3 1/2, but move here because prototypes may override inheritance, including subslots.
;;; They may also contribute extra slot values and constraints
;;; ---------- 0 1/2. MERGE IN RELEVANT PROTOTYPES ----------

	  (_clones-dummy (cond ((and *are-some-prototypes*
				     (not (member slot *slots-not-to-clone-for*))
				     (use-prototypes)
				     (not (protoinstancep instance0)))			; NEW: Don't clone a prototype onto another prototype!
				(unify-in-prototypes instance0 slot))))

#|
	  (_clones-dummy (cond ((am-in-theoryp)
				(not (frame-for instance))
				(pull-in-frame instance)
				(mark-frame-as-done instance))))		; so it's never pulled in a second time.
		Now it's pulled in, own-rule-sets will collect the data locally, not in *Global
|#

;;; ---------- 0 3/4. COLLECT ALL THE RULE DATA NEEDED ----------

;;; NOTE: These basic parameters are computed *after* adding in prototypes, in case the prototypes extended
;;; some of data (specifically, own rules and constraints).
#|
[1] Special case:
	(every Transcribe has
	  (subevent ((a Copy with
			(next-event ((if <test> then (the Copy subevent of Self) else ...)))))))

;;; Here's the problem we want to avoid...
[_Situation1] KM> (the subevent of (a Transcribe))
(_Copy2)
[_Situation1] KM> (next-situation)
[_Situation2] KM> (the next-event of _Copy2)
NIL

Similarly, projecting from prev situation doesn't work, as we want to re-evaluate the next-event rule.
Hence we reify _Copy2 in the *Global situation. But we can only do this if subevent is a non-fluent ([2]) ?? - Do I really need this constraint?
I'm restricting the generality of my reification "solution" here. I need a good model of destruction for this to be okay.
Consider:
	(every Water has
	  (parts ((a Hydrogen with (bound-to ((the Oxygen parts of Self))))
		  (a Oxygen with (bound-to ((the Hydrogen parts of Self)))))))
If the Hydrogen and Oxygen can be removed as parts of the Water, then we must also be allowed to break
their bindings. Hmm...But we shouldn't be able to break the "parts" relation, though? I suppose we could
"switch" one Hydrogen for another, without violating the axiom, and then the bound-to relationship no
longer needs to hold for the old Hydrogen part. But that is rather strange.

[2] came up as Ken Barker wanted to be able to say things like:
	(every Person has (owns ((a Car))))
but not insist that it's the *same* car uniformly throughout their life. So we make owns a fluent.
Now:
	(every Person has (owns ((a Car with (parts ((a Engine)))))))
Suppose Fred owns _Car1 with _Engine1 in _Situation1. Now, in Situation2, there's no guarantee that
Fred still owns _Car1, and hence no guarantee that the constraint _Car1 parts _Engine1 still needs
to be enforced (?).
|#
	  (instance (dereference instance0))
	  (_check-prototype (cond ((and (protoinstancep instance)
	  			        (not (am-in-prototype-mode)))
			          (report-error 'user-error
				  "Attempt to query a protoinstance ~a when not in prototype mode!~%         Doing (the ~a of ~a)~%"
				  instance slot instance))))
	  (target `(#$the ,slot #$of ,instance))
	  (own-rule-sets (own-rule-sets instance slot :retain-commentsp t))
	  (own-constraints (mapcan #'find-constraints-in-exprs own-rule-sets))     ; from instance in curr-situation AND its supersituations

	  (inherited-rule-sets-x			; [1]
	   (cond ((use-inheritance)
		  (cond ((and (not own-rule-sets)	; avoid doing this multiple times: If the rule's already fired, don't need to re-refer to
			      (am-in-local-situation) 					; the Skolem object
			      (not (fluentp slot)))	; [2]
			 (let ( (global-inherited-rule-sets (inherited-rule-sets instance slot :retain-commentsp t))
				(local-inherited-rule-sets (inherited-rule-sets instance slot :retain-commentsp t :climb-situation-hierarchyp nil)) )
			   (append local-inherited-rule-sets (reify-existentials-in-rule-sets global-inherited-rule-sets))))
			(t (inherited-rule-sets instance slot :retain-commentsp t))))))  ; 2D search up classes and sitns

	  (inherited-rule-sets
	  	(cond (combine-values-by-appendingp
		       (let ((xx (append-lists inherited-rule-sets-x)))
		         (cond (xx (list xx)))))
		      (t inherited-rule-sets-x)))

	  (inherited-rule-sets-all 	; for constraints with inherits-with-overrides, need ALL constraints still!
	      (cond ((and (use-inheritance)
	                  (not (inherit-with-overrides-slotp slot)))
		     inherited-rule-sets)
		    (t (inherited-rule-sets instance slot :retain-commentsp t
		                            :ignore-inherit-with-overrides-restriction t))))
	  (inherited-constraints (mapcan #'find-constraints-in-exprs inherited-rule-sets-all))   ; from classes

	  (constraints (append inherited-constraints own-constraints))
	  (no-inheritancep (and *use-no-inheritance-flag* (member '#$(no-inheritance) constraints :test #'equal)))

;;; ---------- 1. PROJECTION ----------
;;; [1] NB subslots of prev-situation used for hypothetical reasoning

	  (try-projectionp (and (am-in-local-situation)
				(projectable slot instance)
				(prev-situation (curr-situation) instance)))
  	  (projected-vals0 (cond (try-projectionp
				  (cond ((tracep)
					 (setq n (1+ n))
					 (km-trace 'comment "(~a) Look in previous situation" n)))
				  (km-slotvals-via-projection instance slot))))
	  (projected-vals (cond ((and constraints projected-vals0)
	  			    (cond ((and (tracep) (not (traceunifyp)))
				           (let ((*trace* nil))
					     (filter-using-constraints projected-vals0 constraints slot)))
;				           (prog2 (suspend-trace)
;					   (filter-using-constraints projected-vals0 constraints slot)
;					   (unsuspend-trace)))
					  (t (km-trace 'comment "(~ab) Test projected values ~a against constraints ~a" n projected-vals0 constraints)
					     (filter-using-constraints projected-vals0 constraints slot))))
				(t projected-vals0)))

;;; [1] explanations for SINGLE-valued slots recorded later
	  (_project1-dummy (cond ((and (tracep)
				       try-projectionp
				       (not (equal projected-vals0 projected-vals))
				       (km-trace 'comment "    Discarding projected values ~a (conflicts with constraints ~a)"
						 (set-difference projected-vals0 projected-vals) constraints)))))
	 (_project2-dummy (cond ((and projected-vals
	                              multivaluedp)		; projection may fail later for single-valued slots (see maybe-project-val below)
				  (let ( (prev-situation (prev-situation (curr-situation) instance)) )
  				           (mapc #'(lambda (projected-val)
					      (record-explanation-for target projected-val `(#$projected-from ,prev-situation)))
					  projected-vals)	; [1]
				    (make-comment "Projected (the ~a of ~a) = ~a from ~a to ~a"
							     slot instance projected-vals prev-situation (curr-situation))))))

;;; ---------- 2. SUBSLOTS ----------

	  (subslots (immediate-subslots slot))
	  (subslot-vals (cond (subslots
			       (cond (no-inheritancep
				      (km-trace 'comment "(Ignore subslots, as there is a `(no-inheritance)' constraint on this slot)"))
				     (t (cond ((tracep)
					       (setq n (1+ n))
					       (km-trace 'comment "(~a) Look in subslot(s)" n)))
#|Correct|#		       	        (km-int (vals-to-val
				     	      (mapcar #'(lambda (subslot) `#$(the ,SUBSLOT of ,INSTANCE0 (comm ,*SUBSLOT-COMMENT-TAG* Self ,SUBSLOT))) subslots))
				    	     :target target))))))

;;; ---------- 3. SUPERSITUATIONS ----------

#|
[1] For non-fluents, although we ensure that values of slot will be stored in
*Global (by put-slotvals in frame-io.lisp), we must also ensure that any direct *side effects*
during the computation are *also* stored in *Global. This is because all the expr sets
necessarily came from *Global in the first place, but we (below) skip doing the computation
in *Global by default for non-fluents.
[Note we don't *only* do the computation in *Global, as the local situation alone may have the
 extra information we need to compute the slot's values.]
The only side-effect I can think of is *instance creation* (with the side-effect of asserting
an instance-of link). So we check for the presence of this in the exprs (which necessarily
all come from *Global, as the slot is a non fluent).
Note indirect side-effects will be handled automatically by a recursive call to KM.
|#
;;; [2] If the slot's a fluent, then we should apply the rules in the global situation to
;;;     make sure the global situation gets updated.
;;;     If it isn't, then we don't need to bother as the result will be posted back to
;;;     the global situation anyway. We collect the "global values" and "global rules"
;;;     later on and apply them locally here. *EXCEPT* for Events -- where we might not
;;;     apply the global rules locally (if the action's not been carried out yet).
;;;   QN: What about unactualized actions, where we want to test preconditions? We may
;;;       want to apply global rules to local data to find the action's slot-values, but
;;;	  we block this later at [**]. So we'll miss some info.
;;;     For Events, although their slots are non-fluents, we still might want to collect
;;; blocked, so in this special case we must look up

#|
11/13/03: This bit of code is now redundant. Reasoning in a situation will NOT include switching to the parent
situation, as (for example) the parent situation might conclude opposite things given the closed-world
assumption. We'd already prevented this switching for *global-situation* (see code below), we now
extend it to ALL parent situations.

	  (supersituations0 (immediate-supersituations (curr-situation)))
	  (supersituations (cond (supersituations0
				  (remove *global-situation* supersituations0))
				 (t supersituations0)))
	  (supersituation-vals (cond ((and supersituations
					   (or (fluentp slot)	; If the slot isn't a fluent, then supersituations won't contribute anything
					       (contains-some-existential-exprs inherited-rule-sets)
					       (contains-some-existential-exprs own-rule-sets)))
				      (cond ((tracep)
					     (setq n (1+ n))
					     (km-trace 'comment "(~a) Look in supersituation(s)" n)))
; not used any more		      (remove-fluent-instances
				       (km-int (val-sets-to-expr
						(mapcar #'(lambda (sitn)
							    `#$((in-situation ,SITN (the ,SLOT of ,INSTANCE0))))
							supersituations)
						:combine-values-by-appendingp combine-values-by-appendingp
						:single-valuedp single-valuedp)
					 ))))
|#
	  (supersituation-vals nil)		; disabled now

;;; ---------- 4. LOCAL VALUES ----------

	  (local-vals (cond (own-rule-sets
			      (cond ((tracep)				 ;     val, eg. from lazy unification)
				     (setq n (1+ n))
;				     (km-format t "own-rule-sets = ~a~%" own-rule-sets)
				     (km-trace 'comment "(~a) Local value(s): ~a" n
					  (val-sets-to-expr own-rule-sets :single-valuedp single-valuedp))))
			      (cond ((and (singletonp own-rule-sets)			 ; (a) no evaluation necessary
					  (singletonp (first own-rule-sets))		; just ONE set of ONE item
					  (atom (first (first own-rule-sets)))
					  (neq (first (first own-rule-sets)) '#$:incomplete)
					  (eql (dereference (first (first own-rule-sets)))
					      (first (first own-rule-sets))))
				      (first own-rule-sets))
				    (t 				 ; (b) some evaluation necesary (eg. path in local slot)
				    (km-int (val-sets-to-expr own-rule-sets
				    		:combine-values-by-appendingp combine-values-by-appendingp
				    		:single-valuedp single-valuedp)
					    :target target))))))

;;; Need to get these before the intermediate save, which may clobber them!
	  (local-constraints (let ( (local-situation (target-situation (curr-situation) instance slot)) )
			       (find-constraints-in-exprs (bind-self (get-vals instance slot :situation local-situation) instance))))

;;; ---------- (1 or 2)-4. INTERMEDIATE COMBINE AND SAVE OF VALS (but not rules) ----------

#| SPECIAL CASE: Storing intermediate result.
   Now we store the intermediate result, in case when applying the rules we need to see
   what we've got so far. [Case in point: _Engine23 from supersituation, (a Engine with
   (connects ((the parts of ...)))) from classes, and if we fail to show (a Engine.. )
   subsumes _Engine23 due to subsumption check, we still want to assert _Engine23].

[1] projecting a single-valued slot is done *later*

|#

	  (n-first-source (cond ((and try-projectionp single-valuedp) 2) (t 1)))   ; [1]
;	  (n-sources (length
;		      (remove nil
;			      (list try-projectionp subslots supersituations own-rule-sets inherited-rule-sets))))
	  (n-sources n)			; why bother computing them? Some may be nil, but that's fine.
	  (val-sets (remove-duplicates
		     (remove nil `(,(cond (multivaluedp projected-vals))  ; val-sets *EXCLUDES* inherited-rule-sets
				   ,subslot-vals
				   ,supersituation-vals
				   ,local-vals))
;				   ,@cloned-valsets))		; now merged in at set 3 1/2
		     :test #'equal))

;	  (_dummy4 (km-format t "DEBUG: val-sets = ~a~%" val-sets))

#|
POSSIBLY WANT CONSTRAINT CHECKING HERE TOO (TO AVOID INTERMEDIATE INCORRECT SAVE)
7/11/02: No kidding. Without this, it causes a problem when an (at-most 1 <M>) constraint should force unification
of the two values. But instead they get asserted as two values, which later can generate an
error. Let's patch this one, but JUST to check for forced unifications.
|#

	  (vals
	   (cond
	    ((null val-sets) nil)		  	             ; NO val sets found
	    (t (let ( (singletonp-constraints (remove-if-not #'(lambda (constraint)
								 (and (listp constraint)	 ; ignore :incomplete keyword
								      (member (first constraint) '#$(at-most exactly))
								      (= (second constraint) 1)))
							     constraints)) )
		 (cond ((singletonp val-sets)			             ; ONE val set found
			(cond ((not (dont-cache-values-slotp slot))
			(let ( (vals0 (enforce-set-constraints
					(remove '#$:incomplete (first val-sets)) singletonp-constraints :target target)) )
				 (put-vals instance slot vals0)
				 vals0))
			      (t (first val-sets))))
		       (t (cond ((not (= n-first-source n-sources))
				 (km-trace 'comment "(~a-~a) CombineX ~a-~a together"
					   n-first-source n-sources n-first-source n-sources)))
			  (let ( (vals0 (enforce-set-constraints
			  			(km-int (val-sets-to-expr val-sets
				  				:combine-values-by-appendingp combine-values-by-appendingp
						  		:single-valuedp single-valuedp)
							:target target)
						 singletonp-constraints :target target)) )
					 (cond ((not (dont-cache-values-slotp slot))
				   (put-vals instance slot vals0))) 	          ; <== the intermediate save!!!
			    vals0)))))))

;;; ---------- (1 or 2)-4 & 5. FOLD IN RULES ----------

;;; Execute inherited rule sets
;;; [1] NOTE: local-vals = evaluation of own-rule-sets EXCEPT that :default entries are SKIPPED
;;;     So we'll pick them up again here as if they were inherited
             (inherited-rule-sets00
	      (cond (*are-some-defaults*
		      (mapcar #'(lambda (expr-set)
		                      (evaluate-and-filter-defaults expr-set constraints vals slot
				                                   :single-valuedp single-valuedp))
;			      inherited-rule-sets))
;	  	              (append own-rule-sets inherited-rule-sets)))	; [1]
                              (append (remove nil
                              	       (mapcar #'(lambda (own-rules) ; [1]
						  (find-exprs own-rules :expr-type 'default :plurality 'plural))
					      own-rule-sets))
				      inherited-rule-sets)))
                    (t inherited-rule-sets)))

;          (_d0 (km-format t "~%instance = ~a, slot = ~a~%" instance slot))
;          (_d1 (km-format t "inherited-rule-sets = ~a~%" inherited-rule-sets))
;	  (_d2 (km-format t "inherited-rule-sets00 = ~a~%" inherited-rule-sets00))
;	  (_d3 (km-format t "vals = ~a~%" vals))
;	  (_d4 (km-format t "local-vals = ~a~%" local-vals))
;	  (_d5 (km-format t "own-rule-sets = ~a~%" own-rule-sets))
;	  (_d6 (km-format t "constraints = ~a~%" constraints))
	  (all-vals00
	   (cond ((not (use-inheritance)) (km-trace 'comment "(No inherited rules (Inheritance is turned off))") vals)
		 (inherited-rule-sets00
		  (cond (no-inheritancep (km-trace 'comment "(Ignore inherited rules, as there is a `(no-inheritance)' constraint on this slot)")
					 vals)
; 8/29/07 - inherit-with-overrides change in semantics - now ALWAYS inherit, even if there's a local value
; NEW: Turn this back on for simple cases
			((and vals (simple-inherit-with-overrides-slotp slot))
			 (km-trace 'comment "(Ignore rules, as there are local values and the slot is a simple-inherit-with-overrides slot)")
			 vals)
			(t 				;		(NB inherited-constraints are necessarily in inherited-rule-sets!)
			 (cond ((tracep)
				(setq n (1+ n))
				(cond ((inherit-with-overrides-slotp slot)
				       (km-trace 'comment "(~a) Lowest rules, from inheritance with over-rides: ~a"
				       			n (val-sets-to-expr inherited-rule-sets00
							:single-valuedp single-valuedp)))
				      (t (km-trace 'comment "(~a) From inheritance: ~a" n (val-sets-to-expr inherited-rule-sets00 :single-valuedp single-valuedp))))))
			 (cond (vals (km-trace 'comment "(~a-~a) CombineY ~a-~a together" n-first-source n n-first-source n)))
; 8/29/07 - inherit-with-overrides change in semantics - discard inherited info only if clashes with any local value
			 (cond
			 ((and vals (inherit-with-overrides-slotp slot))
;			  (km-format t "DEBUG: ~a ~a (~a &? ~a)~%" instance slot vals inherited-rule-sets00)
			    (cond (single-valuedp
;                             (km-format t "constraints = ~a~%" constraints)
	 		      (let ((loc-vals (km-int (vals-to-&-expr vals) :target target)))
			            (km-trace 'comment "See if inherited info is consistent with local vals...")
			            (cond ((km-int `(,loc-vals &?
 				                  ,(val-sets-to-expr inherited-rule-sets00 :single-valuedp t)))
			    		   (km-trace 'comment "...yes! Inherited info is consistent with local vals. Unifying it in...")
					   (km-int `(,loc-vals &
					          ,(val-sets-to-expr inherited-rule-sets00 :single-valuedp t))
						  :target target))
					  (t (km-trace 'comment "...no, inherited info isn't consistent with local info, so dropping inherited info.")
					     loc-vals))))   ; drop inherited value if inconsistent with local
				 (multivaluedp
			          (km-trace 'comment "See if inherited info is consistent with local vals...")
				  (let* ((loc-vals (km-int (val-sets-to-expr (list vals)) :target target))
				         (locgen-vals (km-int (val-sets-to-expr (cons loc-vals inherited-rule-sets00))
 				                          :target target)))
				    (cond ((satisfies-constraints locgen-vals constraints slot)
			    		   (km-trace 'comment "...yes! Inherited info is consistent with local vals. Unifying it in...")
 				            locgen-vals)
					  (t (km-trace 'comment "...no, inherited info isn't consistent with local info, so dropping inherited info.")
					     loc-vals))))))
			       (t (km-int (val-sets-to-expr (cons vals inherited-rule-sets00)
				                         :single-valuedp single-valuedp) :target target)))
			 )))
		 (t vals)))

;;; If the rules are recursive, reiterate (just once more)
	 (all-vals0
	  (cond ((and all-vals00 inherited-rule-sets00 (use-inheritance) (not no-inheritancep) (not (dont-cache-values-slotp slot)))
		 (let ( (recursive-rulesets (remove-if-not #'(lambda (ruleset)
							       (recursive-ruleset instance slot ruleset))
							   inherited-rule-sets00)) )
		   (cond
		    (recursive-rulesets
		     (km-trace 'comment
			       "Recursive ruleset(s) ~a encountered~%...retrying them now some other values have been computed!" recursive-rulesets)
		     (put-vals instance slot all-vals00)
		     (km-int (val-sets-to-expr (cons all-vals00 inherited-rule-sets00) :single-valuedp single-valuedp)
			 :target target))
		    (t all-vals00))))
		(t all-vals00)))

;;; ---------- 1-5. CONDITIONAL PROJECTION OF SINGLE-VALUED SLOT'S VALUE ----------

	  (all-vals1
	     (cond (multivaluedp
		    all-vals0)		; multivalued case: already handled
		   (t (let ( (projected-val (maybe-project-value projected-vals 		; single-valued case: combine only if compatible
								 all-vals0 slot instance n)) )
			(cond (projected-val
			       (record-explanation-for target projected-val `(#$projected-from ,(prev-situation (curr-situation) instance)))
			       (list projected-val))	; EITHER all-vals0 = nil OR all-vals0 & projected-val unified together
			      (t all-vals0))))))			; projection failed - all-vals0 dominated.

;; No! Constraint-checking done in && procedure
;; Later: Yes! Do it here! && misses constraint-checking for non-&& cases
;;;
;; NOTE: all-vals1 can be nil; we might coerce new vals to appear!
;; LATER: 1/22/08: how can we coerce new vals to appear??
;;;		   Maybe I was thinking of when *max-padding-instances* > 0?? Let's add that in as an extra condition.
           (all-vals2 (cond ((and constraints
	                          (or all-vals1 (> *max-padding-instances* 0))		; NEW 1/22/08
				  )
	                     (cond ((and (tracep) (not (traceconstraintsp)))
			            (let ((*trace* nil))
				      (enforce-constraints all-vals1 constraints :target target)))
				   (t (km-trace 'comment "(~ab) Test values against constraints ~a" n constraints)
				      (enforce-constraints all-vals1 constraints :target target))))
			  (t all-vals1)))

	  (all-vals (cond ((remove-subsumers-slotp slot) (remove-subsumers all-vals2))
			  ((remove-subsumees-slotp slot) (remove-subsumees all-vals2))
			  (t all-vals2)))

	  (all-vals-and-constraints
	          (cond (local-constraints
			 (cond (single-valuedp (val-to-vals (vals-to-&-expr (append all-vals local-constraints))))
			       (t (append all-vals local-constraints))))
			(t all-vals))) )

	(declare (ignore _check-prototype _project1-dummy _project2-dummy _clones-dummy))

    (cond ((not (dont-cache-values-slotp slot))
           (put-vals instance slot all-vals-and-constraints)		; store result, even if NIL [2]
	   ; NOTE: process-km1-results will record the explanation for vals, but NOT for constraints, so let's do that here
	   (cond (*record-explanations*
;	   (km-format t "target = ~a, vals = ~a, local-constraints = ~a~%" target
;			   (mapcar #'desource+decomment local-constraints) local-constraints)
		  (mapc #'(lambda (local-constraint)	; local-constraint includes source info
		             (let ((val (desource+decomment local-constraint)))
			       (cond ((not (equal val local-constraint))	; i.e., local-constraint has source info
			              (record-explanation-for target val local-constraint))))) ; so SKIP (constraint ...)
			local-constraints)))))						; exprs (they're unannotated)

;  Why was classify removed in earlier versions?
;    (classify instance)
; Remove it again. Only at instance creation, and addition of facts via has, do we reclassify

;   (km-format t "Now! all-vals = ~a~%" all-vals)
    (check-slot instance slot all-vals)				; optional error-checking

;   (cond ((am-in-local-situation)
;	   (un-done instance :slot slot :situation (curr-situation))))	; remove flags in all future situations, if there are any
; BETTER:
    (let ( (target-situation (target-situation (curr-situation) instance slot all-vals)) )
      (cond ((and (neq target-situation *global-situation*)
		  (not (equal all-vals-and-constraints (get-vals instance slot :situation target-situation))))
	     (un-done instance :slot slot :situation (curr-situation)))))	; remove flags in all future situations, if there are any

    (cond ((not (dont-cache-values-slotp slot)) (note-done instance slot)))    ; flag instance.slot done in curr situation

    all-vals))

;;; ======================================================================
;;; 			END OF km-slotvals-from-kb!!!
;;; ======================================================================

;;; (recursive-ruleset '#$_Car23 '#$parts '#$(_Engine3 (the parts of (the parts of _Car23))))
;;; -> t
;;; This is using cheap tricks to check for recursive rules! If it accidentally makes a
;;; mistake it's not an error, just an inefficiency.
(defun recursive-ruleset (instance slot ruleset)
  (search `#$(,SLOT of ,INSTANCE) (flatten ruleset)))

;;; ======================================================================
;;;		TEMPORAL PROJECTION CODE
;;; ======================================================================

#|
Look up the slotvals from the previous situation (if any).
Assume test "(and (am-in-local-situation) (projectable slot instance))" has already been passed.
[1] 9/8/00 - We must ensure that EVENTS have non-inertial slot values, even if the user's failed to specify that these
		 slots are non-inertial fluents.
	To ensure this, BOTH (Event slot Instance) and (Instance invslot Event) triples CANNOT be projected.
	[2] in projectable() removes the former, and [1] below removes the latter.
|#

(defun km-slotvals-via-projection (instance slot)
  (let ((prev-situation (cond (*project-cached-values-only* (prev-situation-with-vals (curr-situation) instance slot))
			      (t (prev-situation (curr-situation) instance)))))
    (cond (prev-situation
	   (km-int `#$(in-situation ,PREV-SITUATION (the ,SLOT of ,INSTANCE))))
	  ((tracep) (km-trace 'comment "    (Can't compute what ~a's previous situation is)" (curr-situation))))))

;;; For single-valued slots only. Only project a value if it unifies with the local value.
;;; Returns a singleton list of the resulting (possibly unified) value.
(defun maybe-project-value (projected-values local-values slot instance n-sources)
  (cond
   ((null projected-values) nil)
   ((equal projected-values local-values) (first projected-values))		; NB assume projected-values is a singleton list
   (t (let ( (prev-situation (prev-situation (curr-situation) instance))
	     (projected-value (first projected-values))
	     (local-value (first local-values)) )
	(cond
	  ((>= (length projected-values) 2)
	   (km-format t "ERROR! Projected multiple values ~a for the single-valued slot `~a' on instance ~a!~%"
		      projected-values slot instance)
	   (km-format t "ERROR! Discarding all but the first value (~a)...~%" (first projected-values))))
	(cond
	  ((>= (length local-values) 2)
	   (km-format t "ERROR! Found multiple values ~a for the single-valued slot `~a' on instance ~a!~%"
		      local-values slot instance)
	   (km-format t "ERROR! Discarding all but the first value (~a)...~%" (first local-values))))
	(cond ((null local-value)
	       (km-trace 'comment "(1-~a) Projecting (the ~a of ~a) = (~a) from ~a" n-sources slot instance projected-value prev-situation)
	       (make-comment "Projected (the ~a of ~a) = (~a) from ~a to ~a"
					slot instance projected-value prev-situation (curr-situation))
	       projected-value)
	      (t (let ( (unified (lazy-unify projected-value local-value)) )
		   (cond (unified
			  (km-trace 'comment "(1-~a) Projecting and unifying (the ~a of ~a) = (~a) from ~a"
				 n-sources slot instance projected-value prev-situation)
			  (make-comment "Projected (the ~a of ~a) = (~a) from ~a to ~a"
						   slot instance projected-value prev-situation (curr-situation))
			  unified)		; return projected-value if can unify...
			 (t (km-trace 'comment "(1-~a) Discarding projected value (the ~a of ~a) = (~a) (conflicts with new value (~a))"
				   n-sources slot instance projected-value local-value))))))))))

;;; If a slot has no value in a situation, and it's projectable, then assume the
;;; value in the previous situation still applies.
;;; Note that KM doesn't distinguish "unknown" vs. "no value". By default,
;;; no conclusion is taken to mean "unknown", unless the slot is labeled as
;;; having property "complete", in which case it is taken to mean "no value",
;;; and hence shouldn't be projected.
(defun projectable (slot instance)
  (declare (ignore instance))
  (inertial-fluentp slot))

;;; ========================================

;;; See comment under "3/4. COLLECT ALL THE RULE DATA NEEDED" above
(defun reify-existentials-in-rule-sets (rule-sets)
  (mapcar #'reify-existentials-in-rule-set rule-sets))

;;; ((a Car) (the age of Fred)) -> (_Car23 (the age of Fred))
(defun reify-existentials-in-rule-set (rule-set)
  (mapcar #'reify-existentials-in-expr rule-set))

(defun reify-existentials-in-expr (expr)
  (cond ((and (existential-exprp expr)
	      (some #'(lambda (slotvals)
			(fluentp (slot-in slotvals)))
		    (second (breakup-existential-expr expr))))
	 (km-unique-int `#$(in-situation *Global ,EXPR) :fail-mode 'error))
	(t expr)))

