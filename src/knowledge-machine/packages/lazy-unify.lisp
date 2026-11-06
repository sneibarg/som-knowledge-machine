
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: lazy-unify.lisp
;;; Author: Peter Clark
;;; Date: Sept 1994, revised (debugged!) Jan 1995, rewritten 1996.
;;; Purpose: How do you unify two complex graphs which essentially connect
;;; 	to the entire KB? This clever solution is based on delayed (lazy)
;;;	evaluation of the unification.

; (in-package :km)
(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

; Note: &+! isn't a primitive unification operator, it's decomposed in interpreter.lisp into &+? plus &!
; Also: &+ is a strange operator as (unlike &) it's by default allowed to fail.
(defun equality-assertion-operator (x) (member x '(& &+ &+! &! ==)))
(defun full-equality-assertion-operator (x) (member x '(& &! ==)))
(defun val-unification-operator (x)    (member x '(& &+ &+! &! == &+? &?)))
(defun set-unification-operator (x)    (member x '(&& &&! ===)))
(defun unification-operator (x)        (member x '(& &? &! && &&! &+ &+! &+? == ===)))
; OLD
; (defun unification-operator (x)        (member x '(& &? &! && &&! &+ &+? == ===)))

;;; Experimental modifications for HALO project
(defvar *less-aggressive-constraint-checking* nil)
(defvar *overriding-in-prototypes* t)	; experimental new bit of code
(defvar *trace-merge-prototype-vals* nil)	; for debugging

#|
MAIN ENTRY POINTS
=================
1. TESTING UNIFIABILITY:
try-lazy-unify: Use for &?

2. DOING UNIFICATION:
lazy-unify-&-expr:
	-> lazy-unify-exprs, the main procedure for & and &+
	-> lazy-unify-expr-sets, the main procedure for &&
  Note, lazy-unify-&-expr *MUST* succeed, otherwise it's an error, except for &+ which is allowed
	to quietly return NIL (bit horrible but ok)

NOTE: & and &! *must* succeed, and will generate an error if it fails.
HOWEVER: &+ and &+! are *allowed* to fail. If they does so, it has no side-effects.
	 [ To avoid side-effects for &+!, the handler in interpreter.lisp does &+? then &! ]

Also note lazy-unify is *NOT* a main entry point.
LAZY-UNIFY always takes ATOMIC atoms, not (:triple ...) etc.

TRY-LAZY-UNIFY2: Is a susidiary of TRY-LAZY-UNIFY and LAZY-UNIFY. Returns binding information,
  which is discarded by try-lazy-unify but used by lazy-unify.

(lazy-unify '_Person1 '_Professor1)
Returns NIL if they won't unify. Does a quick check on slot-val compatibility,
so that IF there's a single-valued slot AND there's a value on each instance
AND those values are atomic AND they are unifiable THEN the unification fails.

In addition, we add a classes-subsumep mode:
  If it's T (used for &&) then the classes of one instance must *subsume* the classes of another.
	Thus cat & dog won't unify.
  If it's NIL (used for &) then the classes are assumed mergable, eg. pet & fish will unify
	to (superclasses (pet fish)).

eagerlyp: if true, then do eager rather than lazy unification, ie. don't leave any & or && residues on frames,
	  just atomic values.
	  HOWEVER: If lazy-unify fails and :eagerlyp = t, then there may be bad sub-unifications left :-(
|#
(defparameter *see-unifications* nil)

;;; NOTE: instances are NOT structured values -- structures will have already been broken up by lazy-unify-exprs.
;;; [1] Make sure that (_X == 1) will result in _X being added to *kb-objects* list. This is critical if we want
;;;     to reset the KB and thus destroy the binding for _X!
;;; NOTE: instancename1 OR instancename2 can be structured-list-vals, but NOT both
(defun lazy-unify (instancename1 instancename2 &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
 (let* ((instance1 (dereference instancename1))		; Might be redundant to deref, but just in case!
	(instance2 (dereference instancename2))
	(unification (lazy-unify0 instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp
				  :fail-mode fail-mode)) )
    (cond ((and unification
;		*see-unifications*
		(not (equal instance1 instance2))
		(not (null instance1))
		(not (null instance2)))
;		(not (is-most-recent-deferred-unification instance1 instance2)))
	   (make-comment "(~a ~a ~a) unified to be ~a" instancename1
			 (cond ((and eagerlyp classes-subsumep) '&+!)
			       (eagerlyp '&!) (classes-subsumep '&+) (t '&))
		       instancename2 unification)
	   ))
    (cond ((and (kb-objectp instancename1) (not (known-frame instancename1))) (km-add-to-kb-object-list instancename1)))  ; [1]
    (cond ((and (kb-objectp instancename2) (not (known-frame instancename2))) (km-add-to-kb-object-list instancename2)))
    (cond ((and (null unification)
		(eq fail-mode 'error))
	   (report-error 'user-error "Unification (~a ~a ~a) failed!~%" instance1
			 (cond ((and eagerlyp classes-subsumep) '&+!)
			       (eagerlyp '&!) (classes-subsumep '&+) (t '&)) instance2)))
    unification))

;;; [1] NOTE failure to unify an element means the whole unification should fail
(defun lazy-unify0 (instancename1 instancename2 &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
; (let ( (instance1 (dereference instancename1))		; Might be redundant to deref, but just in case!
;	(instance2 (dereference instancename2)) )		; DONE EARLIER NOW
  (let ( (instance1 instancename1)
	 (instance2 instancename2) )
  (cond
   ((equal instance1 instance2) instance1)	; already unified
   ((null instance1) instance2)
   ((null instance2) instance1)
#|
   ((need-to-defer-unification instance1 instance2 :skip-last-item-in-goal-stack t) ; avoid reflexively seeing yourself
;    (km-trace 'comment "(~a ~a ~a): Deferring unification: ~a is already undergoing unification higher up in the goal stack!" instance1
    (let* ((instance+goal (need-to-defer-unification instance1 instance2 :skip-last-item-in-goal-stack t))
	   (instance (first instance+goal))
	   (goal (second instance+goal))
	   (unification (first goal))
	   (i1+i2 (list (first unification) (third unification)))
	   (other-instance (delistify (remove instance i1+i2))))
      (km-format t "(~a ~a ~a): Deferring unification: ~a is already undergoing unification with ~a higher up in the goal stack!~%" instance1
		 (cond ((and eagerlyp classes-subsumep) '&+!)
		       (eagerlyp '&!) (classes-subsumep '&+) (t '&))
		 instance2 instance other-instance))
;    (show-goal-stack)
;    (break)
    (let ((unification-operator (cond ((and eagerlyp classes-subsumep) '&+!)
				      (eagerlyp '&!) (classes-subsumep '&+) (t '&))))
      (pushnew (list instance1 unification-operator instance2) *deferred-unifications* :test #'equal))
    instance1)
    |#
   (t (lazy-unify2 instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp
		   :fail-mode fail-mode)))))

#|
(defun is-most-recent-deferred-unification (instance1 instance2)
  (let ((most-recent-deferred-unification (first *deferred-unifications*)))
    (or (and (eq instance1 (first most-recent-deferred-unification)) (eq instance2 (third most-recent-deferred-unification)))
	(and (eq instance2 (first most-recent-deferred-unification)) (eq instance1 (third most-recent-deferred-unification))))))

;;; If trying (X & Z), but (X & Y) is higher up in the stack, then defer (X & Z) until (X & Y) is complete
(defun need-to-defer-unification (instance1 instance2 &key skip-last-item-in-goal-stack)
  (cond (skip-last-item-in-goal-stack
	   (or (and instance1 (assoc instance1 (rest (rest *instances-being-unified*))))
	       (and instance2 (assoc instance2 (rest (rest *instances-being-unified*))))))
	(t (or (and instance1 (assoc instance1 *instances-being-unified*))
	       (and instance2 (assoc instance2 *instances-being-unified*))))))
|#
#|
OLD AND VERY INEFFICIENT
;;; If trying (X & Z), but (X & Y) is higher up in the stack, then defer (X & Z) until (X & Y) is complete
(defun need-to-defer-unification (instance1 instance2 &key skip-last-item-in-goal-stack)
;  (km-format t "(pending-equality-pairs) = ~a~%" (pending-equality-pairs))
  (some #'(lambda (pair)
	    (cond ((and (member instance1 pair) (not (member instance2 pair))) instance1)
		  ((and (member instance2 pair) (not (member instance1 pair))) instance2)))
	(cond (skip-last-item-in-goal-stack (rest (pending-equality-pairs)))
	      (t (pending-equality-pairs)))))

;;; These are NOT dereferenced
(defun pending-equality-pairs ()
  (remove-duplicates
   (mapcar #'(lambda (goal)
	       (let ((original-expr (third goal)))
		 (cond ((and (listp original-expr)
			     (= (length original-expr) 3)
			     (equality-assertion-operator (second original-expr)))
			(list (first original-expr) (third original-expr))))))
	   (goal-stack))		; strip last equality which is *actually* being done, rather than pending
   :test #'equal))
|#

;;; ----------------------------------------

#|
[3] This is where the result is finally stored in memory
[4] There's a subtle special case here. Fluent instances are NOT projected, so if we have (*MyCar owner _SomePerson3) in S0,
then ask for (*MyCar owner) in S1, we get NIL, and then (*MyCar owner) is flagged as DONE in S1. Fine so far.
But suppose later _SomePerson3 becomes a non-fluent instance, by doing (_SomePerson3 & *Pete) - now it SHOULD be
projected to S1, which would require removing the DONE flag on (*MyCar owner) in S1. But of course this unification
will not remove the DONE flag on all the things which are in some relationship to _SomePerson3.
We can probably make it do that though with a (very) special purpose line of code in lazy-unify.lisp!
[5] maybe-project-values i1 i2; i1 has a non-projected value in prev situation; i2 has the same value in curr situation.
    So i1 and i2 can unify, but we don't need to perform an un-done on i1.
|#
(defun lazy-unify2 (instance1 instance2 &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
  (multiple-value-bind
      (unified-name sitn+svs-pairs binding-list) ; binding-list is just a singleton e.g., ((i1 . i2)), from unify-names
      (try-lazy-unify2 instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp
		       :fail-mode fail-mode) ; (1) TRY IT...
  (let ( (change-made nil) )
   (cond (unified-name			; (2) DO IT!
;	  (cond (*deferred-unifications*
;		 (km-format t "Doing (~a & ~a), with *deferred-unifications* = ~a~%" instance1 instance2 *deferred-unifications*)))
	  (mapc #'(lambda (binding)				; 1.4.00 Try this here (rather than later, see below)
		    (km-bind (first binding) (second binding)))
		binding-list)
	  (cond ((kb-objectp unified-name)   ; don't do stuff for numbers & strings!
		 (let ( (curr-situation (curr-situation)) )
		   (mapc #'(lambda (sitn+svs)
			     (change-to-situation (first sitn+svs))
			     (cond ((or change-made
					(equal (second sitn+svs) (get-slotsvals unified-name))
					(and (prev-situation (curr-situation) unified-name)
					     (null (get-slotsvals unified-name))
					     (subsetp (second sitn+svs)
						      (get-slotsvals unified-name :situation (prev-situation (curr-situation) unified-name))
						      :test #'equal))))
				   (t (setq change-made t)))
			     (put-slotsvals unified-name (second sitn+svs)))     	; [3]
			 sitn+svs-pairs)
		   (change-to-situation curr-situation))))
	  (cond ((isa unified-name '#$Situation)
		 (setq change-made t)
		 (cond ((and (isa instance1 '#$Situation) (isa instance2 '#$Situation))
			(make-comment "Unifying situations ~a & ~a" instance1 instance2)))
		 (copy-situation-contents instance1 unified-name)
		 (copy-situation-contents instance2 unified-name)))
	  (cond ((and (kb-objectp unified-name)
		      change-made)			; NEW 9/10/02
		 (un-done unified-name)   ; all vals to be recomputed now - now in put-slotsvals; Later: no!
		 (cond ((x-or (fluent-instancep instance1) (fluent-instancep instance2))		; [4] A very unusual case
;			(km-format t "Dealing with very unusual special case of un-done")
			(let ( (fluent-instance (cond ((fluent-instancep instance1) instance1) (t instance2))) )
;			  (km-format t "Scanning situations....")
			  (mapc #'(lambda (situation)
				    (mapc #'(lambda (slotvals)
					      (let ( (invslot (invert-slot (slot-in slotvals))) )
						(mapc #'(lambda (val)
							  (cond ((kb-objectp val) (un-done val :slot invslot :situation situation)
;								 (format t ".")
								 )))
						      (vals-in slotvals))))
					  (get-slotsvals fluent-instance :situation situation)))
				(all-situations-and-theories))
;			  (km-format t "..done!~%")
;			  (terpri)
			  )))
		 (classify unified-name)  ; reclassify
		 ))
	  unified-name)))))

;;; --------------------

#|
try-lazy-unify: Is a main entry point into lazy unification.
Purpose is to simply CHECK whether unification is possible for instances, which might include structured
values. DISCARDS any binding information thus collected.

RETURNS: any non-nil value for success, NIL for failure.

NOTE: It is not allowed to call try-lazy-unify with :eagerlyp t, as this would leave side-effects
after the unification test. I've disabled this keyword even as an option.
|#
(defun try-lazy-unify (instancename1 instancename2 &key classes-subsumep #|eagerlyp|# (check-constraintsp t))
 (let ((instance1 (dereference instancename1))		; Might be redundant to deref, but just in case!
       (instance2 (dereference instancename2)))
  (cond
   ((km-equal instance1 instance2) instance1)	; already unified
   ((null instance1) instance2)
   ((null instance2) instance1)
   ((and (km-triplep instance1) (km-triplep instance2)) 		; See [*] below
;    (km-format t "ERROR! Attempt to unify triples ~a and ~a!~%" instance1 instance2)
    nil)		; no, fail quietly. KM might try this, and the result should just be an append [Why?]
;  ((and (km-triplep instance1) (km-triplep instance2))
;    (and (try-lazy-unify2 (second instance1) (second instance2) :classes-subsumep classes-subsumep :eagerlyp eagerlyp)
;	 (try-lazy-unify2 (third instance1) (third instance2) :classes-subsumep classes-subsumep :eagerlyp eagerlyp)
;	 (cond ((or (constraint-exprp (fourth instance1)) (constraint-exprp (fourth instance2)))
;		(equal (fourth instance1) (fourth instance2)))
;	       (t (try-lazy-unify (fourth instance1) (fourth instance2) :classes-subsumep classes-subsumep :eagerlyp eagerlyp)))))
   ((km-setp instance1))				; structured-lists call try-lazy-unify recursively. Here account for (:seq 1 (:set 2 3))
   ((km-setp instance2))				; type structures
   ((or (km-structured-list-valp instance1)
	(km-structured-list-valp instance2))
    (let ((d-instance1 (desource instance1))		; (:seq 1 2 (@ Car)) -> (:seq 1 2)
	  (d-instance2 (desource instance2)) )
      (cond ((or (not (km-structured-list-valp d-instance1))	; revised, so (_Car1 &? (:pair 1 2)) quietly fails
		 (not (km-structured-list-valp d-instance2)))
	     (unify-names d-instance1 d-instance2 :classes-subsumep classes-subsumep :fail-mode 'fail)) ; failure allowed for try-lazy-unify of course

;            ((not (km-structured-list-valp d-instance1))
;	     (report-error 'user-error "Attempt to unify an atomic object ~a with a sequence-like object ~a!" instance1 instance2)
;	     (try-lazy-unify (list (first d-instance2) d-instance1) d-instance2 ; x & (:args x y)
;			   :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp))
;	    ((not (km-structured-list-valp d-instance2))
;	     (report-error 'user-error "Attempt to unify a sequence-like object ~a with an atomic object ~a!" instance1 instance2)
;	     (try-lazy-unify d-instance1 (list (first d-instance1) d-instance2) ; (:args x y) & x
;			     :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp))

	    ((and (eq (first d-instance1) (first d-instance2))
		  (neq (first d-instance1) '#$:triple))			;; Why did I exclude :triples??? Similarly above at [*]
	   (every #'(lambda (pair)
		      (try-lazy-unify (first pair) (second pair)
				      :classes-subsumep classes-subsumep #|:eagerlyp eagerlyp|# :check-constraintsp check-constraintsp))
		  (rest (transpose (list d-instance1 d-instance2))))))))	; ((:seq :seq) (i1 e1) (i2 e2) ... )
   (t (try-lazy-unify2 instance1 instance2 :classes-subsumep classes-subsumep #|:eagerlyp eagerlyp|# :check-constraintsp check-constraintsp :fail-mode 'fail)))))

#|
try-lazy-unify2: This function has no side effects.
Returns three values:
	1. the instancename of the unification
	2. a list of (situation slotsvals) pairs, of the unified structure for each situation
	3. a list of (instance1 instance2) variable binding pairs
OR nil if the unification fails.

[1] HLO-3916 - (cml::abox-get-individual '|Synthesis-Of-mRNA-In-Eukaryote|)
    unify-names (which checks incompatible-instances) succeeds, but then through the process of
    finding slot-values result in discovery (assertion) that the two instances are not equal. Thus we need
    to *repeat* the check on incompatible-instances again here, to cover this case.
|#
(defun try-lazy-unify2 (instance1 instance2 &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
  (cond ((and (eq fail-mode 'fail) eagerlyp) (report-error 'program-error "try-lazy-unify2: :fail-mode 'fail and :eagerlyp t can't both be set at the same time!")))
  (multiple-value-bind
      (unified-name bindings)
      (unify-names instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode)
    (cond (unified-name
;	   (km-format t "computing sitn-svs-pairs...")
	   (let ( (sitn-svs-pairs (unified-svs instance1 instance2
					       :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp :fail-mode fail-mode)) )
;	     (km-format t "..done!~%")
	     (cond ((and (neq sitn-svs-pairs 'fail)
			 (unify-names instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode))  ; [1]
		    (setq *statistics-unifications* (1+ *statistics-unifications*))
		    (values unified-name sitn-svs-pairs bindings))))))))

;;; ----------------------------------------

;;; Returns a list of (situation unified-svs) pairs for unifying i1 and i2
;;;      OR 'fail, if a problem was encountered
;;; PEC: 9/6/00 - this is inefficient, and confusing for debugging: KM should abort immediately a 'fail is encountered,
;;; 	rather than continuing on to the bitter end.
;;; OLD VERSION:
;(defun unified-svs (i1 i2 &key (situations (all-active-situations)) classes-subsumep eagerlyp)
;  (let ( (sitn-svs-pairs (mapcar #'(lambda (situation)
;				     (unified-svs-in-situation i1 i2 situation :classes-subsumep classes-subsumep :eagerlyp eagerlyp))
;				 situations)) )
;    (cond ((not (member 'fail sitn-svs-pairs)) sitn-svs-pairs)
;	  (t 'fail))))

;;; NEW VERSION - abort immediately a 'fail is encountered
(defun unified-svs (i1 i2 &key (situations (all-situations-and-theories)) classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
  (cond ((endp situations) nil)
	(t (let ( (sitn-svs-pair (unified-svs-in-situation i1 i2 (first situations)
							   :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp :fail-mode fail-mode)) )
	     (cond ((eq sitn-svs-pair 'fail) 'fail)
		   (t (let ( (sitn-svs-pairs (unified-svs i1 i2 :situations (rest situations)
							  :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp :fail-mode fail-mode)) )
			(cond ((eq sitn-svs-pairs 'fail) 'fail)
			      (sitn-svs-pair (cons sitn-svs-pair sitn-svs-pairs))	; NEW: May be nil
			      (t sitn-svs-pairs)))))))))

;;; [1] This is critical, as lazy-unify-slotsvals drags in constraints from whatever the current situation is!
;;; [2] change-to-situation doesn't make-comments.
;;; [3] There must be *some* data on both objects. Note, we still check slot values if only ONE instance has values providing the OTHER
;;;		instance has at least some slot-values somewhere (including other slots).
(defun unified-svs-in-situation (i1 i2 situation &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
  (let ( (curr-situation (curr-situation))
	 (slotsvals1 (get-slotsvals i1 :situation situation))    ; (don't need bind-self as frames are instances
	 (slotsvals2 (get-slotsvals i2 :situation situation))    ; (don't need bind-self as frames are instances
	 )
;   (km-format t "CALLING (unified-svs-in-situation ~a ~a ~a slotsvals1=~a, slotsvals2=~a)~%"
;	       i1 i2 situation slotsvals1 slotsvals2)

    (cond ((and (x-or slotsvals1 slotsvals2)
		(eq situation *global-situation*))		; only in *GLOBAL* situation can we skip. In local, maybe global X + local Y values which conflict
	   (list situation (or slotsvals1 slotsvals2)))		; See GLOBAL+LOCAL in test-suite/unification.km
	  ((or slotsvals1 slotsvals2)								; [3]
	   (cond ((neq situation curr-situation) (change-to-situation situation)))			; [1], [2]
	   (multiple-value-bind
	    (successp unified-svs)
	    (lazy-unify-slotsvals i1 i2
				  slotsvals1 slotsvals2
				  :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp :fail-mode fail-mode)
	    (cond ((neq situation curr-situation) (change-to-situation curr-situation)))		; [1]
	    (cond (successp (list situation unified-svs))
		  (t 'fail)))))))

;;; ----------------------------------------

;;; Returns (i) unified value (ii) extra binding list elements
;;; In the case of two anonymous instances A and B, then B points to A, ie. get B->A,
;;; not A->B. Three items of code depend on this ordering:
;;;    1. (load-kb ...), so that a statement like (_X2 == _X1) binds _X1
;;;       to point to _X2, and not vice-versa. (The writer prints the master
;;;	  object first, then the bound synonym second).
;;;	  Apr 01: Redundant now, the writer does dereferencing and no "==" writing.
;;;    2. [overall-expr-for-slot, global-expr-for-slot, and local-expr-for-slot] now called
;;;	  inherited-rule-sets, local-rule-sets,
;;;	  in frame-io.lisp assumes this binding order (see that
;;;	  file for notes), putting *Global instances before situation-specific
;;;	  ones.
;;;    3. get-unified-all puts local instances before inherited expressions,
;;;	  so that the local instance names persist.
;;; [1] I don't know why, but I enforced the classes-subsumep constraint *always* for
;;;     non-kb-objects. This means (100 & (a Coordinate)) fails, which I don't think it should.
;;;     Apr 03: Relax this. The anonymous instance must either be blank, or have only an acceptable class definition
;;; [7] Michael Wessel only wants to check locked classes for heuristic unification (when :classes-subsumep t), not for forced unification.
(defun unify-names (instance1 instance2 &key classes-subsumep eagerlyp (fail-mode 'fail))
; (let ((fail-mode (cond (eagerlyp 'error) (t 'fail))))
  (cond
   ((eq  instance1 instance2) (values instance1 nil)) 			; (*car2 & *car2)
   ((incompatible-instances instance1 instance2)
    (cond ((eq fail-mode 'error)
	   (report-error 'user-error "Unification (~a ~a ~a) failed!~%       Problem was: ~a~%" instance1
			 (cond ((and eagerlyp classes-subsumep) '&+!)
			       (eagerlyp '&!) (classes-subsumep '&+) (t '&)) instance2
			       (incompatible-instances instance1 instance2))))	; returns description of problem
    nil)
   ((and (not (kb-objectp instance1))					; ("a" & _string23) [1]
	 (anonymous-instancep instance2))
    (cond ((immediate-classes-subsume-immediate-classes instance2 instance1)
	   (values instance1 (list (list instance2 instance1))))))
   ((and (not (kb-objectp instance2))					; (_string23 & "a") [1]
	 (anonymous-instancep instance1))
    (cond ((immediate-classes-subsume-immediate-classes instance1 instance2)
	   (values instance2 (list (list instance1 instance2))))))
					    ;;; else, if it's not of the above special
					    ;;; cases, check they are unifiable (based on classes)
; Now in incompatible instances check below
;  ((and (named-instancep instance1) (named-instancep instance2)) nil)	; (*f & *g), ("a" & "b") FAILS
   (t (multiple-value-bind
	  (compatiblep violated-partitions locked-violations)
	  (compatible-classes :instance1 instance1 :instance2 instance2 :classes-subsumep classes-subsumep
			      :check-locked-classes-p classes-subsumep) ; [7]
					; two KB objects, >= 1 anonymous
					; then create binding list as needed.
	(cond				; (X & Y): special cases where Y takes precidence:
	 (compatiblep
	  (cond ((or (named-instancep instance2) ; (_person12 & *fred)	return *fred
		     (and (fluent-instancep instance1) ; (_someCar12 & _Car2)  return _Car2
			  (anonymous-instancep instance2))
		     (and (not (named-instancep instance1)) ; EXCLUDE  *Fred & _Person3 -> _Person3
			  (immediate-classes-subsume-immediate-classes instance1 instance2 :properp t))) ; 4/17/01: daring!!!!!
		 (values instance2 (list (list instance1 instance2))))
		(t (values instance1 (list (list instance2 instance1)))))) ; ELSE (X & Y) return X
	 ((eq fail-mode 'error)
	  (cond (violated-partitions
		 (report-error 'user-error "Unification (~a ~a ~a) failed! The classes were found to be incompatible.~%Partition(s) ~a was violated:~%~{~a~}"
			       instance1
			       (cond ((and eagerlyp classes-subsumep) '&+!)
				     (eagerlyp '&!) (classes-subsumep '&+) (t '&))
			       instance2
			       (delistify violated-partitions)
			       (mapcar #'write-frame violated-partitions)))
		(locked-violations
		 (report-error 'user-error "Unification (~a ~a ~a) failed! The unification would replace the locked class ~a with ~a. (not allowed!)~%"
			       instance1
			       (cond ((and eagerlyp classes-subsumep) '&+!)
				     (eagerlyp '&!) (classes-subsumep '&+) (t '&))
			       instance2
			       (first locked-violations)
			       (second locked-violations)))
		(t (report-error 'user-error "Unification (~a ~a ~a) failed! The classes were found to be incompatible.~%"
				 instance1
				 (cond ((and eagerlyp classes-subsumep) '&+!)
				       (eagerlyp '&!) (classes-subsumep '&+) (t '&))
				 instance2)))))))))

;;; (immediate-classes-subsume-immediate-classes '123 '_number3)   -> t    because _number3 isa number
;;; (immediate-classes-subsume-immediate-classes '_Car1 '_Vehicle3)   -> t
;;; [1] tests equality but only works if there are no redundant classes in the class lists.
;;; [2] is a little bit less efficient but WILL handle redundant classes in the class lists.
(defun immediate-classes-subsume-immediate-classes (instance1 instance2 &key properp)
  (let ( (immediate-classes1 (immediate-classes instance1))
	 (immediate-classes2 (immediate-classes instance2)) )
    (and (classes-subsume-classes immediate-classes1 immediate-classes2)
	 (or (not properp)
	     (cond ((remove-subsumers-slotp '#$instance-of)
		    (not (set-equal immediate-classes1 immediate-classes2)))			; [1]
		   (t (not (classes-subsume-classes immediate-classes2 immediate-classes1))))))))  ; [2]

#|
Check /== constraints. Note does *NOT* check Partitions, use compatible-classes for that.
RETURNS: A string describing the problem
 [1] :test #'equal, to allow for  "cat" and _Animal-Name1 where (_Animal-Name1 (/== ("cat")))
 [2] IF there is some equality constraints, AND the check-slotvals-constraints FAILS for them,
	THEN the instances are incompatible
 [3] I guess I'm assuming people will assert inequalities via KM> (x /== y), rather than such
     statements being put on frames themselves. But really, we should do (km-int `#$(the /== of ,INSTANCE1)) to
     be safe (/== is also assumed to be an atomic values only slot).
     Let's leave it as a direct get-vals, for efficiency for now!
|#
(defun incompatible-instances (instance1 instance2)
  (cond ; ((not (atomp instance1))
	;  (report-error 'program-error "non-atom ~a passed to incompatible-instances!~%" instance1))
        ((equal instance1 instance2) nil)
        ((and (named-instancep instance1)
	      (named-instancep instance2)	; (*f & *g) FAILS
	      (neq instance1 instance2)
	      (cond ((and (stringp instance1) (stringp instance2)) "These are different strings!")
		    ((and (numberp instance1) (numberp instance2)) "These are different numbers!")
		    (t "These are different objects!"))
	      ))
	((classp instance1)
	 (cond ((not (isa instance2 '#$Class)) (km-format nil "~a is a class, but ~a isn't" instance1 instance2))))
	((classp instance2)
	 (cond ((not (isa instance1 '#$Class)) (km-format nil "~a is a class, but ~a isn't" instance2 instance1))))
	(*are-some-constraints*
	 (let* ((instance1-neqs0 (cond ((and (kb-objectp instance1)
					   (some #'(lambda (neq-slot) (get-vals instance1 neq-slot)) *neq-slots*))
				      (my-mapcan #'(lambda (neq-slot) (km-int `#$(the ,NEQ-SLOT of ,INSTANCE1))) *neq-slots*))))
	       (instance2-neqs0 (cond ((and (kb-objectp instance2)
					  (some #'(lambda (neq-slot) (get-vals instance2 neq-slot)) *neq-slots*))
				      (my-mapcan #'(lambda (neq-slot) (km-int `#$(the ,NEQ-SLOT of ,INSTANCE2))) *neq-slots*))))
	       (instance1-neqs (cond ((member instance1 instance1-neqs0)
				      (report-error 'user-warning "Error in the KB: ~a declared as not equal to ~a. Ignoring that declaration...~%" instance1 instance1)
				      (remove instance1 instance1-neqs0))
				     (t instance1-neqs0)))
	       (instance2-neqs (cond ((member instance2 instance2-neqs0)
				      (report-error 'user-warning "Error in the KB: ~a declared as not equal to ~a. Ignoring that declaration...~%" instance2 instance2)
				      (remove instance2 instance2-neqs0))
				     (t instance2-neqs0)))
	       )
	   (cond
	    ((member instance2 instance1-neqs :test #'equal)
	     (km-format nil "~a has a constraint /== ~a on it." instance1 instance2))
	    ((some #'(lambda (instance1-neq) (pending-equality instance2 instance1-neq)) instance1-neqs)	; HLO-4132
	     (let ((instance1-neq (find-if #'(lambda (instance1-neq) (pending-equality instance2 instance1-neq)) instance1-neqs)))
	       (km-format nil "~a has a constraint /== ~a on it, and (~a & ~a) is pending (higher up the goal stack)"
			  instance1 instance1-neq instance1-neq instance2)))
	    ((member instance1 instance2-neqs :test #'equal)
	     (km-format nil "~a has a constraint /== ~a on it." instance2 instance1))
	    ((some #'(lambda (instance2-neq) (pending-equality instance1 instance2-neq)) instance2-neqs)	; HLO-4132
	     (let ((instance2-neq (find-if #'(lambda (instance2-neq) (pending-equality instance1 instance2-neq)) instance2-neqs)))
	       (km-format nil "~a has a constraint /== ~a on it, and (~a & ~a) is pending (higher up the goal stack)"
			  instance2 instance2-neq instance2-neq instance1)))
	    ((and (numberp instance1)
		  (kb-objectp instance2)
		  (some #'(lambda (n) (and (numberp n) (<= instance1 n)))  (km-int `#$(the > of ,INSTANCE2))))
	     (km-format nil "~a has a constraint > ~a on it." instance2 (km-int `#$(the > of ,INSTANCE2))))
	    ((and (numberp instance1)
		  (kb-objectp instance2)
		  (some #'(lambda (n) (and (numberp n) (>= instance1 n)))  (km-int `#$(the < of ,INSTANCE2))))
	     (km-format nil "~a has a constraint < ~a on it." instance2 (km-int `#$(the < of ,INSTANCE2))))
	    ((and (numberp instance2)
		  (kb-objectp instance1)
		  (some #'(lambda (n) (and (numberp n) (<= instance2 n)))  (km-int `#$(the > of ,INSTANCE1))))
	     (km-format nil "~a has a constraint > ~a on it." instance1 (km-int `#$(the > of ,INSTANCE1))))
	    ((and (numberp instance2)
		  (kb-objectp instance1)
		  (some #'(lambda (n) (and (numberp n) (>= instance2 n)))  (km-int `#$(the < of ,INSTANCE1))))
	     (km-format nil "~a has a constraint < ~a on it." instance1 (km-int `#$(the < of ,INSTANCE1))))
	    ((let ((instance1-eq (cond ((kb-objectp instance1)
					(get-vals instance1 '== :situation *global-situation*))))
		   (instance2-eq (cond ((kb-objectp instance2)
					(get-vals instance2 '== :situation *global-situation*)))))
	       (cond ((and (or instance1-eq instance2-eq)
			   (not (check-slotvals-constraints '== instance1 instance2 instance1-eq instance2-eq))) ; [2]
		      (km-format nil "Some equality constraint violation (~a == ~a, ~a == ~a)"
				 instance1 instance1-eq instance2 instance2-eq)))))
	    )))))

;;; ======================================================================
;;;		UNIFICATION OF SLOTSVALS
;;; ======================================================================
#|
Unification with constraint checking:

_Person1			_Person2
--------			--------
  pets: Dog			  pets: Dog	(must-be-a Animal)
	---				---
 	  color: Red			  color: Blue

&&: Must check the first-level slots, that the values satisfy the
    constraints. The search for constraints is global, and if any are found
    then the search for values is global also.
    If there are no constraints, then && is guaranteed to succeed and so
    doesn't need to be computed.

&: As well as checking the first-level slot constraints, lazy-unify-vals does a
   &? check, which recursively checks that the second-level slot constraints
   are satisfied (eg. if color is single-valued, that Red and Blue are
   unifiable). Note that a second-level check isn't needed with &&.

[1] As well as explicit constraints, there are also partition constraints which
    must be checked for &, which means we must do an aggressive (the slot of X)
    for & operations, regardless of whether constraints are found or not.

Note we only check/perform unification for slots which explicitly occur on either
i1 or i2. All other slots are ignored.

lazy-unify-slotsvals
--------------------
Returns two values
 - t or nil, depending on whether unification was successful
   (If nil, then the unified slotsvals are partial and can be discarded)
 - the unified slotsvals
This was extended in Aug 99 to include constraint checking, so that the procedure
will fail if there's a constraint violation (even if only one instance actually has
a slot value).

[1] It's only with eagerlyp that lazy-unify-vals will evaluate the unification and squish out the constraints (thus they need to be reinstalled)

If :fail-mode is 'fail, then the calling procedure is *TESTING* unification, not actually *DOING* it.

eagerlyp   fail-mode
  nil        fail 	    test, no side effects. When used for &+, unification will follow if successful.
[  t         fail  ]        not allowed (will leave side effects)
  nil        error 	    Used for &.  No side effects; forced unification will follow anyway in the calling procedure if *on-error* = 'continue
   t         error	    side effects; forced unification will follow anyway in the calling procedure if *on-error* = 'continue

If :eagerlyp = t, then there are side effects down in the details when unifying prototypes. So :error-mode better be 'error in tihs case.
|#
(defun lazy-unify-slotsvals (i1 i2 svs1 svs2 &key cs1 cs2 classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
  (cond
   ((and (endp svs1)
	 (endp svs2)))	; ie. return (values t nil)
   (t (let* ( (test-p (eq fail-mode 'fail))     ; if :fail-mode 'fail, then it's just a test so it's ok to not complete it
	      (sv1  (first svs1))
	      (slot (or (slot-in sv1) 		; work through svs1 first. When done,
			(slot-in (first svs2))))	; work through remaining svs2.
	      (exprs1 (vals-in sv1))
	      (sv2 (assoc slot svs2))
	      (exprs2 (vals-in sv2))
	      (rest-svs2 (remove-if #'(lambda (a-sv2)
					(eq slot (slot-in a-sv2)))
				    svs2)) )
	(cond ((and (null exprs1) (null exprs2)) ; vals both null, so drop the slot
	       (lazy-unify-slotsvals i1 i2 (rest svs1) rest-svs2 :cs1 cs1 :cs2 cs2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp
				     :check-constraintsp check-constraintsp :fail-mode fail-mode))
	      ((or (not check-constraintsp)

;;; SPECIAL CASE FOR UNIFYING PROTOTYPES:
;;; If unifying prototypes (signified by eagerlyp) AND inherit-with-overrides AND no anonymous instances
;;; THEN existing value (= from more specific prototype clone) takes precedence
;;; See test-suite/prototypes4.km and RELEASE-NOTES for KM 2.1.10.
;;; The goal of the below is to SKIP the constraint check, and have lazy-unify-vals handle any conflicting values
;;; there instead.
;;; [10] with looping, eagerly unifying prototypes may still leave a residual & structure in the result, even though
;;;      KM is evaluating eagerly.
;;; [11] We *could* add this as an extra constraint in, but seems like we don't need it.
		   (and ; eagerlyp [10]
			*overriding-in-prototypes*
			(inherit-with-overrides-slotp slot)
;			(not (format t "exprs1 = ~a, exprs2 = ~a~%" exprs1 exprs2))
;			(notany #'kb-objectp exprs1)
;			(notany #'kb-objectp exprs2)
			(notany #'anonymous-instancep exprs1)	; 2/12/13
			(notany #'anonymous-instancep exprs2)
;			(every #'fully-evaluatedp vs1) ; [11] DON'T drop expr2 for eg. (_Val22 & (if <..> then ...))
;			(every #'fully-evaluatedp vs2)
			)
		   (check-slotvals-constraints slot i1 i2 exprs1 exprs2 :cs1 cs1 :cs2 cs2
					       :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode)
		   (not test-p)		; if constraints violated, but it's a forced unification, then keep going regardless
		   )
	       (multiple-value-bind
		   (unified-vals successp1)
		   (lazy-unify-vals slot i1 i2 exprs1 exprs2
				    :cs1 cs1 :cs2 cs2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp)
		 (cond (successp1			;; else fail (return NIL)
			(multiple-value-bind
			 (successp unified-rest)
			 (lazy-unify-slotsvals i1 i2 (rest svs1) rest-svs2 :cs1 cs1 :cs2 cs2
					       :classes-subsumep classes-subsumep :eagerlyp eagerlyp :check-constraintsp check-constraintsp
					       :fail-mode fail-mode)
			 (values successp (cond (unified-vals
						 (cons (list slot unified-vals) unified-rest))
						(t unified-rest)))))))))))))

#|
======================================================================
	check-slotvals-constraints
======================================================================
This function has no side-effects. It's purpose is to check the unified slot values are consistent with
constraints. This requires KM doing a bit of work, both to find the constraints and find the slot values
themselves in some cases.

[2] suppose unify Group1 in S1 and S2. We are currently in S1, but Group1 only has location in S2.
while svs2 contains that location information, doing another query will get rid of it, so vs2 = nil, and hence the
unification is nil.
[2] ALSO for unifiable-with-slotsvals test
[3] We also allow this to be called with i1, i2 = NIL. This occurs
    when we want to just merge two structures together (from merge-slotsvals), or merge
    a structure with an instance (from unifiable/unify-with-existential-expr)
    IF WE DO THIS, THOUGH, then we *must* supply the class for the missing instance,
    so we can still gather the inherited constraints for the structure. This is done
    via cs1 and cs2.
BUT: we also have a problem. If we are dealing with a structure (i2 = nil), then we don't just
     need the inherited constraints, we also need the inherited slot-values, as these may
     clash with constraints on/inherited by i1.
     And suppose these inherited expressions refer to Self? We've no Self to evaluate them for!

	(a Person with			   &? (a Person-With-Favorite-Color-Red with
	  (likes ((<> *Red))))			   (likes ((the favorite-color of Self))))
								^^ need to evaluate this path!
SOLUTION might be to collect expr sets.
[6] What if EXPR contains Self? Simplest: Ignore them. This means the constraints will not be
tested, but we won't "lose things" in the KB. Better would be to add a tmp-i creation and
deletion again (sigh) to be thorough.
[5] What if EXPR contains an existential? Don't want to litter the KB with temporary instances!!
So ignore them again.

[4] We *only* want to pull in generalizations if we are checking constraints!
This is a compromise between always getting just the local values, and always pulling in the inherited values.
Version2 causes looping with unifying prototypes (see test-suite/outstanding/protobug.km), it's generally a dangerous and
expensive thing to do inheritance as part of unification computation.
[7] Note, we have to use (collect-constraints-on-instance i1...), rather than look in exprs1, because there may
    be constraints on i1 in a supersituation.
[8] exprs1, exprs2 are dereferenced, but the rule sets may not be.
[9] (_Color3 has 					(*Green)
	(== ((possible-values *Red *Blue))))
[10] Darn, need to keep these in so that:
   (a Partition with (members (Thymine Adenine Guanine Cytosine)))
   ((a Bond with (holds ((a Guanine)))) &? (a Bond with (holds ((exactly 2 Thing) (a Adenine) (a Thymine))))) <- should fail
[11] Given: (check-slotvals-constraints parts _Car23 nil (_Engine23) nil :cs1 nil :cs2 Car)
            don't waste time checking the constraints on the "parts" slot. Note this may pull in additional
	    (here already implied) facts via inherited-rule-sets-on-classes.
[12] 8/18/05 - added (not (inherit-with-overrides-slotp slot)). If the slot is inherit-with-overrides, then clashes
     in the parent classes in general should not be a problem (although one can imagine pathological cases where they are)
     [13] 7/24/08 - No, skipping a full call to KM fails with prototypes. For HLO-2225, we end up with

9          (_HI-Substance2474 &? _Bronsted-Lowry-Acid2578): Checking constraints on the electrolyte-status slot...
10         -> (the electrolyte-status of _HI-Substance2474)
10         <- FAIL!                      "(the electrolyte-status of _HI-Substance2474)"
10         -> (the electrolyte-status of _Bronsted-Lowry-Acid2578)
10         <- (_Electrolyte-Status-Value2568) "(the electrolyte-status of _Bronsted-Lowry-A...

In a different variant of this, &? should fail because HI-Substance has a different (incompatible) electrolyte-status
to the BL-Acid, acquired through prototype unification. But without the full call to KM, we don't trigger the
prototype unification, so HI-Substance has no electrolyte-status, then unifies with BL-Acid acquiring the wrong
status.
|#
;(defun check-slotvals-constraints (slot i1 i2 exprs1 exprs2 &key cs1 cs2 eagerlyp)
;  (cond (*backtrack-after-testing-unification*
;	 (setq *internal-logging* t)
;	 (let ( (checkpoint-id (gensym)) )
;	   (set-checkpoint checkpoint-id)
;	   (prog1
;	       (check-slotvals-constraints0 slot i1 i2 exprs1 exprs2 :cs1 cs1 :cs2 cs2 :eagerlyp eagerlyp)
;	     (undo checkpoint-id)		; undo, whatever
;	     (setq *internal-logging* nil))))
;	(t (check-slotvals-constraints0 slot i1 i2 exprs1 exprs2 :cs1 cs1 :cs2 cs2 :eagerlyp eagerlyp))))

(defun check-slotvals-constraints (slot i1 i2 exprs1 exprs2 &key cs1 cs2 classes-subsumep eagerlyp (fail-mode 'fail))
  (cond ((eq (dereference i1) (dereference i2)) 	; note, a subcall might unify these, including making some
	 t)						; note-dones, which will mess up if we continue
	(t (check-slotvals-constraints0 slot i1 i2 exprs1 exprs2 :cs1 cs1 :cs2 cs2
					:classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode))))

;;; NOTE: :eagerlyp argument used solely for formatting error messages (write &+!/&! rather than &+/&)
(defun check-slotvals-constraints0 (slot i1 i2 exprs1 exprs2 &key cs1 cs2 classes-subsumep eagerlyp (fail-mode 'fail))
;  (declare (ignore classes-subsumep eagerlyp))
  (cond ((and eagerlyp (eq fail-mode 'fail))
	 (report-error 'program-error "Calling check-slotvals-constraints0 with :eagerlyp t and :fail-mode 'fail (not allowed!)~%")))
;(let ((fail-mode (cond (eagerlyp 'error) (t 'fail))))
 (or
; (eq slot '/==)			; don't check constraints on /== slot, it's done earlier in unify-names
  (member slot *neq-slots*)		; don't check constraints on /== slot, it's done earlier in unify-names
; (eq slot '#$instance-of)
  (ignore-slot-due-to-situations-mode slot)
  (and i1 (null i2) (null exprs2) (every #'(lambda (c2) (isa i1 c2)) cs2))	; [11]
  (and i2 (null i1) (null exprs1) (every #'(lambda (c1) (isa i2 c1)) cs1))	; [11]
  (let*
    ((no-inheritance-flagp (or (and i1 (member '#$(no-inheritance) (find-constraints-in-exprs exprs1) :test #'equal))
			       (and i2 (member '#$(no-inheritance) (find-constraints-in-exprs exprs2) :test #'equal))))
     (use-inheritance (and (use-inheritance)
			   (not no-inheritance-flagp)
			   (not (inherit-with-overrides-slotp slot)))) ; [12]
     (cs1-expr-sets
      (cond (cs1 (remove-if #'contains-self-keyword ; [6]
			    (cons exprs1 (cond (use-inheritance
						(inherited-rule-sets-on-classes cs1 slot :retain-commentsp t))))))
	    (t (cons exprs1 (append (supersituation-own-rule-sets i1 slot :retain-commentsp t)
				    (cond (use-inheritance
					   (inherited-rule-sets i1 slot :retain-commentsp t)))))))) ; NB deref already done
     (cs2-expr-sets
      (cond (cs2 (remove-if #'contains-self-keyword
			    (cons exprs2 (cond (use-inheritance
						(inherited-rule-sets-on-classes cs2 slot :retain-commentsp t))))))
	    (t (cons exprs2 (append (supersituation-own-rule-sets i2 slot :retain-commentsp t)
				    (cond (use-inheritance
					   (inherited-rule-sets i2 slot :retain-commentsp t))))))))

;;; cs1-expr-sets-all is SOLELY for the purpose of finding constraints. These *are* inherited, even for
;;; inherits-with-overrides slots.
     (cs1-expr-sets-all
      (cond (use-inheritance cs1-expr-sets)
	    (cs1 (remove-if #'contains-self-keyword ; [6]
			    (cons exprs1 (inherited-rule-sets-on-classes cs1 slot :retain-commentsp t
									 :ignore-inherit-with-overrides-restriction t))))
	    (t (cons exprs1 (append (supersituation-own-rule-sets i1 slot :retain-commentsp t)
				    (inherited-rule-sets i1 slot :retain-commentsp t
							 :ignore-inherit-with-overrides-restriction t))))))
     (cs2-expr-sets-all
      (cond (use-inheritance cs2-expr-sets)
	    (cs2 (remove-if #'contains-self-keyword
			    (cons exprs2 (inherited-rule-sets-on-classes cs2 slot :retain-commentsp t
	         							 :ignore-inherit-with-overrides-restriction t))))
	    (t (cons exprs2 (append (supersituation-own-rule-sets i2 slot :retain-commentsp t)
				    (inherited-rule-sets i2 slot :retain-commentsp t
     							 :ignore-inherit-with-overrides-restriction t))))))

#|
OLD    (constraints (remove-duplicates
		    (append (cond (i1 (collect-constraints-on-instance i1 slot)) ; [3], [7]
				  (cs1 (mapcan #'find-constraints-in-exprs cs1-expr-sets))
				  (t (report-error 'program-error "Missing both instance1 and class1 in lazy-unify-slotsvals!~%")))
			    (cond (i2 (collect-constraints-on-instance i2 slot))
				  (cs2 (mapcan #'find-constraints-in-exprs cs2-expr-sets))
				  (t (report-error 'program-error "Missing both instance2 and class2 in lazy-unify-slotsvals!~%"))))
		    :test #'equal)) )
|#
; 1/22/10 Note: desource, otherwise two functionally identical constraints will look different (sources now include the
; destination instance, as well as the originating class)
#|NEW|# (constraints1 (desource (mapcan #'find-constraints-in-exprs cs1-expr-sets-all)))
	(constraints2 (desource (mapcan #'find-constraints-in-exprs cs2-expr-sets-all)))

;;; These are to TEST
        (constraints (cond ((and ; (am-in-local-situation) NOT ANY MORE! -> ; in global situation, lazy-unify-vals will catch this. For locals,
				 (single-valued-slotp slot))		; need to do a bit more work, see age (23) age (24) example
			    (remove-duplicates (cons '#$(exactly 1 Thing) ; in test-suite/constraints.km for a case where we need this work.
						     (append constraints1 constraints2)) :test #'equal :from-end t))
			   (t (remove-duplicates (append constraints1 constraints2) :test #'equal :from-end t)))))

;    (km-format t "cs1-expr-sets = ~a~%" cs1-expr-sets)
;    (km-format t "cs2-expr-sets = ~a~%" cs2-expr-sets)
;    (km-format t "constraints1 = ~a~%constraints2 = ~a~%constraints = ~a~%" constraints1 constraints2 constraints)

;   (cond ((and (not constraints0)				; no constraints...
;		(or (multivalued-slotp slot)
;		    (null exprs1)   ; [1] for single-valued, may be partition constraints
;		    (null exprs2)  ;  to check if there are *both* exprs1 and exprs2. Here I'm
;				    ; not looking for & checking inferred values (incompleteness)
;		(not eagerlyp)))
; rewrite this a bit more simply:
    (cond ((and (not constraints)
;		(not eagerlyp)
		))
	  (t (cond ((am-in-local-situation-or-theory)		; RATHER VERBOSE SET OF CHOSING TRACING INFO!
		    (cond ((and i1 i2) (km-trace 'comment "(~a &? ~a): Checking constraints on the ~a slot in ~a..." i1 i2 slot (curr-situation))) ; [4]
			  (i1 (km-trace 'comment "(~a &? (a ~a with (~a ~a) ...): Checking constraints on the ~a slot in ~a..."
					i1 (delistify cs2) slot exprs2 slot (curr-situation))) ; [4]
			  (i2 (km-trace 'comment "(~a &? (a ~a with (~a ~a) ...): Checking constraints on the ~a slot in ~a..."
					i2 (delistify cs1) slot exprs1 slot (curr-situation)))	; [4]
			  (t (km-trace 'comment "((a ~a with (~a ~a) ...) &? (a ~a with (~a ~a) ...):~%     Checking constraints on the ~a slot in ~a..."
				       (delistify cs1) slot exprs1 (delistify cs2) slot exprs2 slot (curr-situation)))))
		   (t (cond ((and i1 i2) (km-trace 'comment "(~a &? ~a): Checking constraints on the ~a slot..." i1 i2 slot))	; [4]
			    (i1 (km-trace 'comment "(~a &? (a ~a with (~a ~a) ...): Checking constraints on the ~a slot..."
					  i1 (delistify cs2) slot exprs2 slot)) ; [4]
			    (i2 (km-trace 'comment "(~a &? (a ~a with (~a ~a) ...): Checking constraints on the ~a slot..."
					  i2 (delistify cs1) slot exprs1 slot))	; [4]
			    (t (km-trace 'comment "((a ~a with (~a ~a) ...) &? (a ~a with (~a ~a) ...):~%     Checking constraints on the ~a slot..."
					 (delistify cs1) slot exprs1 (delistify cs2) slot exprs2 slot)))))
;	     (km-format t "i1 = ~a, slot = ~a, cs1-expr-sets = ~a~%" i1 slot cs1-expr-sets)
;	     (km-format t "i2 = ~a, slot = ~a, cs2-expr-sets = ~a~%" i2 slot cs2-expr-sets)


;;; ---------- X-START ----------
;;: Was deleted, but now I think we put it back to avoid all the heartache of evaluating expressions on (a ...) expressions
;;; NOTE: [11] we do a (km-int ...) on the val-sets, but *NOT* a call to (km-int `(the ,SLOT of ,I1)), because we *don't* want
;;; to invoke projection. This caused a crippling bug (see end of test-suite/johns-location.km).


	     (let* ( (vs1 (cond ((member slot '(== < >)) (cond (i1 (list i1))))		; [9]
				(i1 (cond (*less-aggressive-constraint-checking* (remove-if-not #'fully-evaluatedp
								 (get-vals i1 slot :situation (target-situation (curr-situation) i1 slot))))
				          ((already-done i1 slot)
					   (remove-constraints (get-vals i1 slot :situation (target-situation (curr-situation) i1 slot))))
					  (cs1-expr-sets (km-int-with-trace `#$(the ,SLOT of ,I1) (val-sets-to-expr cs1-expr-sets))) ; [11]
					  (t (let ((*am-classifying* nil)) ; or else it'll be chaos?
					       (km-int `#$(the ,SLOT of ,I1) :target `#$(the ,SLOT of ,I1)))))) ; [13]
				(*less-aggressive-constraint-checking* (remove-if-not #'fully-evaluatedp exprs1))
				;;; No, this gives a very confusing trace:
				;;; (km-int-with-trace '#$(the holds of (a Bond with (holds ((a Adenine) (a Thymine))))) NIL)
				;;;      2  -> (the holds of (a Bond with (holds ((exactly 2 Thing) (a Adenine) (a Thymine)))))
				;;;	 2  <- NIL
;				(t (km-int-with-trace `#$(the ,SLOT of (a ,(VALS-TO-VAL CS1) with (,SLOT ,EXPRS1)))
;						      (val-sets-to-expr (remove-if #'contains-some-existential-exprs cs1-expr-sets)) ; [5]
				(t (let ((exprs-to-evaluate (remove-if #'contains-some-existential-exprs cs1-expr-sets)))
				     (cond (exprs-to-evaluate (km-int-with-trace `#$(the ,SLOT of (a ,(VALS-TO-VAL CS1) with (,SLOT ,EXPRS-TO-EVALUATE)))
										 (val-sets-to-expr exprs-to-evaluate))))
				      ))))
		     (vs2 (cond ((member slot '(== < >)) (cond (i2 (list i2))))		; [9]
				(i2 (cond (*less-aggressive-constraint-checking* (remove-if-not #'fully-evaluatedp
								 (get-vals i2 slot :situation (target-situation (curr-situation) i2 slot))))
				          ((already-done i2 slot)
					   (remove-constraints (get-vals i2 slot :situation (target-situation (curr-situation) i2 slot))))
					  (cs2-expr-sets (km-int-with-trace `#$(the ,SLOT of ,I2) (val-sets-to-expr cs2-expr-sets))) ; [11]
					  (t (let ((*am-classifying* nil)) ; or else it'll be chaos?
					       (km-int `#$(the ,SLOT of ,I2) :target `#$(the ,SLOT of ,I2)))))) ; [13]
				(*less-aggressive-constraint-checking* (remove-if-not #'fully-evaluatedp exprs2))
;				(t (km-int-with-trace `#$(the ,SLOT of (a ,(VALS-TO-VAL CS2) with (,SLOT ,EXPRS2)))
;						      (val-sets-to-expr (remove-if #'contains-some-existential-exprs cs2-expr-sets))
				(t (let ((exprs-to-evaluate (remove-if #'contains-some-existential-exprs cs2-expr-sets)))
				     (cond (exprs-to-evaluate (km-int-with-trace `#$(the ,SLOT of (a ,(VALS-TO-VAL CS2) with (,SLOT ,EXPRS-TO-EVALUATE)))
										 (val-sets-to-expr exprs-to-evaluate))))
				      ))))
;		     (_d (km-format t "vs1 = ~a, vs2 = ~a~%" vs1 vs2))
		     )

;;; ---------- X-END ----------


;;; ---------- Y-START ----------
;;; Simpler version - but computationally more expensive!
;
;	     (let* ( (vs1 (cond ((eq slot '==) (cond (i1 (list i1))))		; [9]
;				(t (cond (i1 (km-trace 'comment "Computing (the ~a of ~a), for constraint checking..." slot i1))
;					 (t (km-trace 'comment "Computing the ~a of the first expression, for constraint checking..." slot)))
;				   (km-int (val-sets-to-expr cs1-expr-sets)))))
;		     (vs2 (cond ((eq slot '==) (cond (i2 (list i2))))		; [9]
;				(t (cond (i2 (km-trace 'comment "Computing (the ~a of ~a), for constraint checking..." slot i2))
;					 (t (km-trace 'comment "Computing the ~a of the second expression, for constraint checking..." slot)))
;				   (km-int (val-sets-to-expr cs2-expr-sets)))))
;;		     (_d (km-format t "vs1 = ~a, vs2 = ~a~%" vs1 vs2))
;		     )
;;; ---------- Y-END ----------

;;; -- start --

;;;	       (cond ((and i1 vs1) (add-vals i1 slot vs1)))		; put the answers back
;;;	       (cond ((and i2 vs2) (add-vals i2 slot vs2)))
;;;
;;; Above, No! This is a disasterous typo'/conceputual error in the patch -
;;; Originally, in some circumstances, I did (km-int `#$(the ,SLOT of ,I1)) to compute vs1. But this was
;;; overly agressive, invoking projection, inheritance etc.
;;; To tame this down, I just evaluate the expressions on the slot. But I should put-vals, not add-vals
;;; back, and if I do that, I need to make sure I do all the book-keeping necessary (in particular
;;; deleting the old expressions, and folding constraints back in. Any other things I've forgotten??
;;; Let's try this instead:

;;; 5/28/02 - It's not clear why I need to do put-vals at all; it seems that anything I put-vals here gets
;;; clobbered anyway by the parent put-vals at the end of lazy-unify. So let's experimentally try removing this
;;; whole section of code (?).
#|
BUG:
KM> (reset-kb)
KM> (every Car has (parts ((a Engine) (mustnt-be-a Furry-Dice))))
KM> (a Car)
(_Car1)
KM> (a Car with (parts ((a Foosball))))
(_Car2)
KM> (_Car1 & _Car2)
(_Car1)
KM> (showme _Car1)
(_Car1 has
  (instance-of (Car))
  (parts ((a Foosball))))		; the evaluated Foosball has been overwritten...
KM> (showme Foosball)
(Foosball has
  (instances (_Foosball4)))		; but the Skolem instance is still lying around!
KM> (showme _Foosball4)
(_Foosball4 has
  (instance-of (Foosball))
  (parts-of (_Car1)))			; part-of of _Car1...
KM> (the parts of _Car1)
(_Foosball6 _Engine7)			; but not one of _Car1's parts!
|#
#|
;;; OLD (pre-caching) version - revert back to doing this
;	       (format t "i1=~a, vs1=~a~%" i1 vs1)
	       (cond ((and i1 vs1 (not (dont-cache-values-slotp slot)))
		      (let*
; BUG!			  ( (constraints1 (find-constraints-in-exprs cs1-expr-sets))
; unnecessarily many	  ( (constraints1 (my-mapcan #'find-constraints-in-exprs cs1-expr-sets))
; done earlier		  ( (constraints1 (find-constraints-in-exprs exprs1))
			  ( (constraints1-to-put (find-constraints-in-exprs exprs1))
			    (vs1+constraints1 (cond (constraints1-to-put
						     (cond ((single-valued-slotp slot)
							    (val-to-vals (vals-to-&-expr (append vs1 constraints1-to-put))))
							   (t (append vs1 constraints1-to-put))))
						    (t vs1))) )
;			(km-format t "constraints1-to-put = ~a~%" constraints1-to-put)
			(put-vals i1 slot vs1+constraints1))))	; NB no note-done, as didn't use inheritance
;	       (format t "i2=~a, vs2=~a~%" i2 vs2)
	       (cond ((and i2 vs2 (not (dont-cache-values-slotp slot)))
		      (let*
; BUG!			  ( (constraints2 (find-constraints-in-exprs cs2-expr-sets))
; unnecessarily many	  ( (constraints2 (my-mapcan #'find-constraints-in-exprs cs2-expr-sets))
; done earlier		  ( (constraints2 (find-constraints-in-exprs exprs2))
			  ( (constraints2-to-put (find-constraints-in-exprs exprs2))
			    (vs2+constraints2 (cond (constraints2-to-put
						    (cond ((single-valued-slotp slot)
							   (val-to-vals (vals-to-&-expr (append vs2 constraints2-to-put))))
							  (t (append vs2 constraints2-to-put))))
						    (t vs2))) )
;			(km-format t "constraints2-to-put = ~a~%" constraints2-to-put)
			(put-vals i2 slot vs2+constraints2))))	; NB no note-done, as didn't use inheritance
|#

;;; REVISED 11/29/00
;;; REMOVED 5/10/01 - cache no longer used - return to old version above.
;	       (cond ((and i1 vs1) (put-vals-in-cache i1 slot vs1)))	; constraints left in the non-cache
;	       (cond ((and i2 vs2) (put-vals-in-cache i2 slot vs2)))	; constraints left in the non-cache

;;; -- end --

;	       (km-format t "constraints1 = ~a~%" constraints1)
;	       (km-format t "constraints2 = ~a~%" constraints2)
;	       (km-format t "constraints = ~a~%" constraints)
;	       (cond
;	        ((and (are-consistent-with-constraints vs1 (set-difference constraints2 constraints1 :test #'equal) slot)
;		      (are-consistent-with-constraints vs2 (set-difference constraints1 constraints2 :test #'equal) slot)
;		      (test-set-constraints vs1 vs2
;	       (km-format t "vs1 = ~a~%" vs1)
;	       (km-format t "vs2 = ~a~%" vs2)
;	       (km-format t "cs1-expr-sets = ~a~%" cs1-expr-sets)
;              (km-format t "cs2-expr-sets = ~a~%" cs2-expr-sets)
	       (let* ((expr-sets (remove nil
			          `(,vs1 ,vs2 ,@(cond ((not i1) cs1-expr-sets))     ; to get the existentials in cs1-expr-sets if ignored earlier at [5]
				  	      ,@(cond ((not i2) cs2-expr-sets)))))  ; to get the existentials in cs1-expr-sets if ignored earlier at [5]
		      (constraint-violation		; (constraint+vals)
	       	       (or (violated-constraints vs1 (set-difference constraints2 constraints1 :test #'equal) slot :mode 'consistent)
		           (violated-constraints vs2 (set-difference constraints1 constraints2 :test #'equal) slot :mode 'consistent)
			   (violated-set-constraints expr-sets constraints))))
;		(km-format t "expr-sets = ~a~%" expr-sets)
	        (cond
		 ((not constraint-violation))	; continue
                 (t (let* ((i1-str (or i1 `(#$a ,@cs1 #$with (,slot ,exprs1))))
			   (i2-str (or i2 `(#$a ,@cs2 #$with (,slot ,exprs2))))
			   (violated-constraint (first constraint-violation)) ; e.g., (at-most 1 Cell)
			   (violating-vals (second constraint-violation))
			   (i1-self-inconsistency (cond ((set-constraint-exprp violated-constraint)
			   				 (violated-set-constraints (remove nil `(,vs1 ,@(cond ((not i1) cs1-expr-sets))))
										   constraints1))))
			   (i2-self-inconsistency (cond ((set-constraint-exprp violated-constraint)
							 (violated-set-constraints (remove nil `(,vs2 ,@(cond ((not i2) cs2-expr-sets))))
							                           constraints2))))
			   )
		      (cond
		       (i1-self-inconsistency
			(cond (i1 (report-error 'user-warning "Self-inconsistent instance encountered! (found when testing the unifiability of ~a and ~a)!
      (~a has (~a ~a))~%" i1 i2-str i1 slot (append (remove nil vs1) (list violated-constraint)))))
			(cond (i1 (km-trace 'comment "Instances ~a and ~a won't unify:
   ~a is a self-inconsistent object, so won't unify with anything!
   Self-inconsistency is:
      (~a has (~a ~a))~%" i1 i2-str i1 i1 slot (append (remove nil vs1) (list violated-constraint))))
			      (t (km-trace 'comment "Instances ~a and ~a won't unify:
   ~a is a self-inconsistent object, so won't unify with anything!~%"
					   `(#$a ,@cs1 #$with (,slot (,@exprs1 ,violated-constraint)))
					   i2-str
					   `(#$a ,@cs1 #$with (,slot (,@exprs1 ,violated-constraint)))))))
		       (i2-self-inconsistency
			(cond (i2 (report-error 'user-warning "Self-inconsistent instance encountered! (found when testing the unifiability of ~a and ~a)!
      (~a has (~a ~a))~%" i1-str i2 i2 slot (append (remove nil vs2) (list violated-constraint)))))
			(cond (i2 (km-trace 'comment "Instances ~a and ~a won't unify:
   ~a is a self-inconsistent object, so won't unify with anything!
   Self-inconsistency is:
      (~a has (~a ~a))~%" i1-str i2 i2 i2 slot (append (remove nil vs2) (list violated-constraint))))
			      (t (km-trace 'comment "Instances ~a and ~a won't unify:
   ~a is a self-inconsistent object, so won't unify with anything!~%"
					   i1-str
					   `(#$a ,@cs2 #$with (,slot (,@exprs2 ,violated-constraint)))
					   `(#$a ,@cs2 #$with (,slot (,@exprs1 ,violated-constraint)))))))
		       (t (case fail-mode
		     ;;; Note: :fail-mode fail does *not* imply a KB error, this is just a tracing message
			    (fail (km-trace 'comment "Instances ~a and ~a won't unify~%   Constraint ~a violated by value(s) ~a on slot '~a'.~%"
					    i1-str i2-str violated-constraint violating-vals slot))
			    (error (report-error 'user-error "Unification (~a ~a ~a) failed!~%  Constraint ~a violated by value(s) ~a on slot '~a'.
  To debug: Do (showme ~a) and (showme ~a) and check the values on the '~a' slot.~%"
					   i1-str
					   (cond ((and eagerlyp classes-subsumep) '&+!)
						 (eagerlyp '&!) (classes-subsumep '&+) (t '&))
					   i2-str
					   violated-constraint violating-vals slot i1-str i2-str slot))))))
			)))))))))


;;; ======================================================================
;;;		LAZY-UNIFY-VALS
;;; ======================================================================

#|
lazy-unify-vals: One of the vs1 or vs2 may be nil, **but not both**
INPUT: vs1, vs2 may include arbitrary KM expressions, including constraint expressions
       i2 MAY be NIL, with cs2 instantiated instead, if called by unify-with-slotsvals2. For now, I'm just going
	to ignore pulling constraints with eagerlyp for that situation.
RETURNS TWO values
  (i) The unified structure (NB may be NIL with eagerlyp option), denoting the unified vals
 (ii) A t/nil flag depending on whether the unification was successful or not

**NOTE** If eagerlyp = t, then the unification *must* succeed. But if not, it is allowed to fail.
	i.e., (i1 &+? i2), (i1 &? i2), and (i1 & i2) all use this (for failure in the last case, it's reported after this procedure exits)
        but   (i1 &+! i2) is never called here, as the interpreter calls (i1 &+? i2) followed by (i1 &! i2).

11/17/00: This *doesn't* catch single-valued slot constraints, when v1 is local and given, but v2 is
	  to be inherited and clashes with v1.
 	  SOLUTION: Move the single-valued-slotp test to check-slotvals-constraints.
		(age has  (instance-of (Slot)) (cardinality (N-to-1)))
		(_Person1 has (age (23))))
		(new-situation)
		(_Person2 has (age (24)))
		(_Person1 &? _Person2)		will incorrectly succeed in KM 1.4.1.6 and earlier

(_v1) (_v2) -> ((_v1 & _v2))
((a cat)) ((a hat)) -> (((a cat) & ((a hat)))
[1]: and-append returns a (singleton) LIST of expressions, but we just want to pass a SINGLE expression to KM.
[2] If this unification fails, it doesn't mean a KB error, it just means that the two parent instances can't be unified.
    The failure is passed up to lazy-unify-slotsvals above, and the unification aborted. lazy-unify-slotsvals returns successp NIL.
[3]: KM necessarily returns either NIL or a singleton list here.
[4]: In the special case of ((<> foo) &! (<> bar)), an answer of NIL from evaluating the expression *doesn't* constitute failure of the
	unification.
[5]: Not an error, but would like to tidy this up: ((<> foo) &&! (<> bar)) should be reduced to ((<> foo) (<> bar))
[6]: If classes-subsumep is TRUE, then we are doing SET unification.
     Thus, we should FAIL if we are forced to coerce vs1 and vs2 to unify, ie. if
	- slot is a single-valued
	- vs1 and vs2 do not satisfy the classes-subsumep test
[7]  USER(49): (lazy-unify-vals '#$has-part '(1 2) '(2) :classes-subsumep t)
	        (((1 2) && (2)))
     This causes structures to grow every time unification happens - urgh! Do a subbagp test (below).
[8] Ignore worrying about values from multiple prototypes, for now!
[9]
  -> (the Plasma-membrane has-part of (the Diploid-cell object of (a Nuclear-Division))) [called in *Global]
   -> (the has-part of (the Diploid-cell object of (a Nuclear-Division))) [called in *Global]
    -> (the has-part of _Diploid-cell4237)             [called in *Global]
     -> (unify-with-clone-of _Diploid-cell270)         [called in *Global]
      -> (_Diploid-cell4237 &! _Diploid-cell4391)      [called in |all situations|]
       -> (the has-part of _Diploid-cell4237)          [called in *Global]
        -> ((_Plasma-membrane4187...) && (_Plasma-membrane4347...))
 (lazy-unify-vals |is-part-of| |_Plasma-membrane4187| |_Plasma-membrane4347|
                        (|_Diploid-cell4237| |_Living-Entity4192| |_Living-Entity4191| |_Living-Entity4190| |_Living-Entity4189|)
                        (|_Diploid-cell4237| |_Living-Entity4355| |_Living-Entity4354| |_Living-Entity4353| |_Living-Entity4352|)
         :classes-subsumep t
         :eagerlyp nil)
 *Note* Here that although we are unifying in a clone, the recursion has left :eagerlyp nil. However, here we *do* want
 to heuristically unify the Living-Entities, as they both originated from the same prototype.
|#
(defun lazy-unify-vals (slot i1 i2 vs1 vs2 &key cs1 cs2 classes-subsumep eagerlyp)
 ; (declare (ignore cs1 cs2))
  (cond  ((null vs2) (values vs1 t))	; NB With more aggressive constraint checking, we won't just deal with local values but
	((null vs1) (values vs2 t))	;    compute global values, to check there's no constraint violation. = too expensive??
	((km-equal vs1 vs2) (values vs1 t))
	((subbagp vs1 vs2 :test #'equal) (values vs2 t))
	((subbagp vs2 vs1 :test #'equal) (values vs1 t))
	((remove-subsumers-slotp slot) (values (remove-subsumers (append vs1 vs2)) t)) ; eg. instance-of, superclasses
	((remove-subsumees-slotp slot) (values (remove-subsumees (append vs1 vs2)) t)) ; eg. subclasses

; BELOW: But with prototype instances we DO want unification (HLO-2366 - problem!) (see test-suite/hlo2366.km)
; 	((combine-values-by-appending-slotp slot) (values (remove-dup-instances (append vs1 vs2)) t))
; We can restrict this so that only if vs2 are (non-cloned) atomic instances -- vs2 are the things being ADDED
; to vs1, hence the asymmetry -- then we append, otherwise we DO unification so that protoinstances ARE unified
; (HLO-2366)
 	((or (member slot *built-in-combine-values-by-appending-slots*) ;*built-in-atomic-vals-only-slots* MUSTN'T be &&ed
					; AND same for the other built-in-combine-values-by-appending-slots* too, namely
					; > < /== == add-list del-list pcs-list ncs-list prototype-scope
	     (member slot *neq-slots*)	; treat user-defined neq slots as additional built-in-combine-values-by-appending-slots
	     (and (combine-values-by-appending-slotp slot)
; NEAH...	  (not eagerlyp)	; for prototype unification we *DO* want to &&, hlo2366.  [4]
;;; [4] above: Note for the calls EXPLICITLY merging parts of prototypes, we don't do combine-values-by-appending.
;;;	       But any subgoals, we DO do combine-values-by-appending. The way to tell the difference is
;;;	       if :eagerlyp=t, then it's a direct part of the prototype merging (a somewhat hacky and indirect soln :-().
;;; ***ALSO** See [5] below for another part.
;;;
;;; BELOW:
;;; IF   the thing being unified in is completely a prototype [i.e., all Skolems are clones]
;;; THEN SKIP the append, and do a normal unification
;;; 11/2/09 - NO, this causes an error!!! See test-suite/combine-values-by-appending2.km for a description
;		  (let ((skolems (remove-if-not #'anonymous-instancep (flatten vs2))))
;		    (or (null skolems)			 ; not prototype if no Skolems
;			(notevery #'isa-clone skolems))) ; not prototype if some non-clone Skolem exists
		  ))

#|
	 (km-format t "eagerlyp = ~a~%" eagerlyp)
	 (km-format t "*partially-included-prototype* = ~a~%" *partially-included-prototype*)
	 (km-format t "(member *partially-included-prototype*  ; [10]
					(mapcar #'(lambda (protoinstance)
						    (get-unique-val protoinstance '#$prototype-participant-of))
						(append (get-vals i1 '#$cloned-from)
							(get-vals i2 '#$cloned-from)))) = ~a~%"
				(member *partially-included-prototype*  ; [10]
					(mapcar #'(lambda (protoinstance)
						    (get-unique-val protoinstance '#$prototype-participant-of))
						(append (get-vals i1 '#$cloned-from)
						(get-vals i2 '#$cloned-from)))))
|#
	 (let ((new-vals (cond  ; [8] No, still doesn't work. See comments at merge-prototype-vals below
			  ((and eagerlyp ; doing prototype unification
			        i1 i2
				; [10] if unifying in a (clone of a) prototype that is already partially included
				;      in the instance graph, then consider &&'ing the prototype vals
				*partially-included-prototype*
				(member *partially-included-prototype*  ; [10]
					(mapcar #'(lambda (protoinstance)
						    (get-unique-val protoinstance '#$prototype-participant-of))
						(append (get-vals i1 '#$cloned-from)
							(get-vals i2 '#$cloned-from))))
				(not (member slot *built-in-combine-values-by-appending-slots*))
				(not (member slot *neq-slots*)) ; treat user-defined neq slots as additional built-in-combine-values-by-appending-slots
				(not (dont-merge-prototype-vals-for slot i1 i2 vs1 vs2))
				)
			   (remove-dup-instances (merge-prototype-vals slot i1 i2 vs1 vs2)))
			  (t (remove-dup-instances (append vs1 vs2))))))
	   (values new-vals t)))		; optimized access methods assume atomic values only.

;;; SPECIAL CASE FOR UNIFYING PROTOTYPES:
;;; If unifying prototypes (signified by eagerlyp) [ AND clash (check-slotvals-constraints failed) <- NO! See below ]
;;; AND inherit-with-overrides AND no anonymous instances, THEN existing value (= from more specific prototype clone)
;;; takes precedence.
;;; [10] with looping, eagerly unifying prototypes may still leave a residual & structure in the result, even though
;;;      KM is evaluating eagerly.
;;; [11] We *could* add this as an extra constraint in, but seems like we don't need it.
	((and				; eagerlyp  [10]
	      *overriding-in-prototypes*
;	      (not (format t "vs1 = ~a, vs2 = ~a~%" vs1 vs2))
	      (inherit-with-overrides-slotp slot)
;	      (notany #'kb-objectp vs1)
;	      (notany #'kb-objectp vs2)
	      (notany #'anonymous-instancep vs1)	; 2/12/13
	      (notany #'anonymous-instancep vs2)

;	      (every #'fully-evaluatedp vs1)   ; [11] DON'T drop expr2 for eg. (_Val22 & (if <..> then ...))
;	      (every #'fully-evaluatedp vs2)
; No, let vs1 ALWAYS take precedence, even if no clash
;	      (not (check-slotvals-constraints slot i1 i2 vs1 vs2 :cs1 cs1 :cs2 cs2 :eagerlyp eagerlyp))
	      )
	 (let ((vs1-vals (remove-constraints vs1))
	       (vs2-vals (remove-constraints vs2))
	       (vs1-constraints (find-constraints-in-exprs vs1)))
	   (make-comment "Prototype unification: Dropping value ~a on slot ~a (~a overrides it)"
			 (delistify vs2-vals) slot (delistify vs1-vals))
	   (values (append (km-int (vals-to-val vs1)) vs1-constraints)
		   t)))

	((single-valued-slotp slot)
	 (cond ((or (not (singletonp vs1))
		    (not (singletonp vs2)))
		(report-error 'user-warning
			 "A single-valued slot has multiple values!~%Doing unification (~a & ~a)
Continuing, assuming all these values should be unified together...~%" vs1 vs2))) ; But incompleteness - we only check unifiability on the first slot...
	 (let ((unifiablep
		(cond ((and (ignore-slot-due-to-situations-mode slot) ; **IF** these conditions hold....
			    (not (and (atom (first vs1))
				      (atom (first vs2))))))
		      (*less-aggressive-constraint-checking* t)
		      (classes-subsumep
		       (km-trace 'comment "Checking unifiability of values on the ~a slot of ~a and ~a" slot i1 i2)
		       (km-int `(,(first vs1) &+? ,(first vs2)) ; [2], [6]
; Neah, not really a target for &? tests
			       :target (cond (i2 `(#$the ,slot #$of (,i1 &+/&+? ,i2)))	; i2 may be nil, see doc above
					     (t `(#$the ,slot #$of ,i1)))
					     ))
		      (t (km-trace 'comment "Checking unifiability of values on the ~a slot of ~a and ~a" slot i1 i2)
			 (km-int `(,(first vs1) &? ,(first vs2)) ; [2], [6]
; Neah, not really a target for &? tests
				 :target (cond (i2 `(#$the ,slot #$of (,i1 &/&? ,i2)))
					       (t `(#$the ,slot #$of ,i1)))
					       )))))
	   (cond
	    (unifiablep
	     (cond (eagerlyp
		       (km-trace 'comment "Eagerly unifying values on the ~a slot of ~a and ~a" slot i1 i2)
		       (let ((new-vals
			      (km-int (vals-to-val
				       (and-append (list (first vs1)) '&! (list (first vs2)))) ; eagerly -> do it!  [1],[3]
				      :target (cond (i2 `(#$the ,slot #$of (,i1 &! ,i2)))
						    (t `(#$the ,slot #$of ,i1))
						    )))) ; [4]
			 (values
			  (val-to-vals (vals-to-&-expr (remove-duplicates (append new-vals
										  (find-constraints-in-exprs vs1)
										  (find-constraints-in-exprs vs2))
									  :test #'equal)))
			  t)))
		   (t (values
			  (val-to-vals (vals-to-&-expr (remove-duplicates (append (un-andify vs1) (un-andify vs2)) :test #'equal)))
			  t)))))))
					; THEN lazy unify them
;;	(eagerlyp (and-append vs1 '&&! vs2))						; [5]
#|NEW|#	(eagerlyp	; NOTE: if :eagerlyp = t, then it's a FORCED unification
 	   	  (let* ((vs1-vals (remove-constraints vs1)) ; see note [7] under lazy-unify-expr-sets
			 (vs2-vals (remove-constraints vs2))
			 (local-vs1-constraints (find-constraints-in-exprs vs1))
			 (local-vs2-constraints (find-constraints-in-exprs vs2)))

		    (cond ((null vs1-vals) (values (append vs2-vals local-vs1-constraints local-vs2-constraints) t))
			  ((null vs2-vals) (values (append vs1-vals local-vs1-constraints local-vs2-constraints) t))
#| Now redundant [inaccessible] because of test earlier, see HLO-2366 notes above.
			  ((and (combine-values-by-appending-slotp slot)
				;;; If one of the vs1-vals or vs2-vals is anonymous-instance-free, then && them.
				;;; In other words, only append them if they BOTH have anonymous instances.
				;;; See test-suite/hlo2366.km.
				;;; It's a bit hacky here to get around this special case.
				(some #'anonymous-instancep (flatten vs1-vals))
				(some #'anonymous-instancep (flatten vs2-vals)))
			   (values (append (km-int (vals-to-val (append vs1 vs2))) ; NOTE just simple appending
			   		local-vs1-constraints local-vs2-constraints)
				   t))
|#			  (t ; Else if we are merging values we better APPLY the constraints now (as eagerlyp = t)
			   (let* ((inherited-vs1-expr-sets
				   (cond (i1 (inherited-rule-sets i1 slot :retain-commentsp t
								  :ignore-inherit-with-overrides-restriction t))))
				  (inherited-vs2-expr-sets
				   (cond (i2 (inherited-rule-sets i2 slot :retain-commentsp t
								  :ignore-inherit-with-overrides-restriction t))))
				  (inherited-vs1-constraints (mapcan #'find-constraints-in-exprs inherited-vs1-expr-sets))
				  (inherited-vs2-constraints (mapcan #'find-constraints-in-exprs inherited-vs2-expr-sets))
				  (all-vs1-constraints (append local-vs1-constraints inherited-vs1-constraints))
				  (all-vs2-constraints (append local-vs2-constraints inherited-vs2-constraints))
				  (all-constraints (remove-duplicates (append all-vs1-constraints all-vs2-constraints)
								      :test #'equal)))
			     (km-trace 'comment "Eagerly unifying values on the ~a slot of ~a and ~a" slot i1 i2)
			     (let ((vs12 (km-int (vals-to-val (and-append vs1 '&&! vs2))
						 :target (cond (i2 `(#$the ,slot #$of (,i1 &! ,i2)))
							       (t `(#$the ,slot #$of ,i1))
							       )))) ; [4]
			       (cond
				((not all-constraints) (values vs12 t))
				((are-consistent-with-constraints vs12 all-constraints slot)
				 (let ((post-constraint-enforcement-values
					(enforce-constraints vs12 all-constraints
							     :target `#$(the ,SLOT of ,I1)))) ; I1 not used in enf-c
				   (values (append post-constraint-enforcement-values
						   (remove-duplicates
						    (append local-vs1-constraints local-vs2-constraints)
						    :test #'equal))
					   t)))
				(t	; failure not allowed for :eagerlyp, so report error
				 (let ((violated-constraint
					(violated-constraints vs12 all-constraints slot :mode 'consistent)))
				   (report-error 'user-error
						 "Unification (~a ~a ~a) failed on slot ~a with combined values
~a:
Constraint ~a was violated by value(s) ~a.~%"
						 (or i1 `(#$a ,@cs1 #$with (,slot ,vs1)))
						 (cond ((and eagerlyp classes-subsumep) '&+!)
						       (eagerlyp '&!) (classes-subsumep '&+) (t '&))
						 (or i2 `(#$a ,@cs2 #$with (,slot ,vs2)))
						 slot vs12
					       (first violated-constraint) (second violated-constraint))))
				)))))))
;       (t (and-append vs1 '&& vs2))))
         (t (values (valsets-to-&&-exprs (remove-duplicates (append (&&-exprs-to-valsets vs1)
								    (&&-exprs-to-valsets vs2))
							    :test #'equal :from-end t))
		    t))))

;;; ======================================================================

(defvar *classes-to-never-heuristically-merge* nil)
(defvar *slots-to-never-heuristically-merge* nil)

(defun dont-merge-prototype-vals-for (slot i1 i2 vs1 vs2)
  (declare (ignore i1 i2))
  (or (member slot *slots-to-never-heuristically-merge*)
      (let* ((vs1-classes (my-mapcan #'(lambda (v1) (cond ((kb-objectp v1) (immediate-classes v1)))) vs1))
	     (vs2-classes (my-mapcan #'(lambda (v2) (cond ((kb-objectp v2) (immediate-classes v2)))) vs2)))
	(or (intersection vs1-classes *classes-to-never-heuristically-merge*)
	    (intersection vs2-classes *classes-to-never-heuristically-merge*)))))

#|
See test-suite/combine-values-by-appending2.km, combine-values-by-appending3.km,

This is for the special case of merging cloned values on a combine-values-by-appending slot.
For this special case we *do*, sometimes, need to &! the values. ;-(
This is when a prototype has been trimmed, or extended, and so we reunify in the prototype.
As a result, we need to detect if any new values V2 are a RE-CLONED VERSIONS of v1, and thus should be unified.
If we don't do this, then the set of values will grow and grow, see combine-values-by-appending2.km

Thus:
(merge-prototype-vals (a b) (c d)) -> (a (b &! c) d)   if b and c have intersecting cloned-from tags AND are same classes.
This is really hacky, but I don't know what else to do!!

1/18/10: No, still get bad unifications. See test-suite/combine-values-by-appending4.km
         We could weaken this by using &&!, but then we'd have to rely on KB constraints to block bad
		unifications. However, there may not be KB constraints to block the unification,
		it was only by luck that I spotted it in combine-values-by-appending4.km due to a KB
		constraint.
         As a result I've strengthened the test for the rare case of a desirable unification:
	 	 v1 and v2 were cloned both from the same protoinstance from the same prototype
	  *AND*	 i1 and i2 were cloned both from the same protoinstance from the same prototype
	Seems like enough evidence now to decide that v2 is a RE-CLONED VERSION of v1, and thus should be unified.

	RESULT: combine-values-by-appending4.km - gets further now, but STILL has a problem.
	I give up! Is it really such a problem with trimming prototypes?

[4/23/12]:
Recap: I had said: (merge-prototype-vals (a b) (c d)) -> (a (b &! c) d)   if b and c have intersecting cloned-from tags AND are same classes.
However, this causes failure when c has been specialized (HLO-4228):
	[[Vesicle]] -is-part-of-> [Cell]
	    |				   \
	[[Synaptic-Vesicle]] -is-part-of-> [Nerve-Cell]

Now when KM does ((clone Vesicle) &! (clone Synaptic-Vesicle)), then (merge-prototype-vals i1 i2 (clone Cell) (clone Nerve-Cell))
returns ((clone Cell) (clone Nerve-Cell)) rather than &!'ing them. So change this from (intersection <classes1> <classes2>) to (classes-subsume-classes <classes1> <classes2>)

Cell and Nerve-Cell satisfy all the other conditions for unifiability: cloned from same node.
|#
(defun merge-prototype-vals (slot i1 i2 vs1 vs2)
  (let* (
;	 (i1-source-protoinstances (get-vals i1 '#$cloned-from))
	 (i1-source-protoinstances (node-cloned-from* i1))
	 (i1-source-protoroots (my-mapcan #'(lambda (i)
					      (get-vals i '#$prototype-participant-of))
					  i1-source-protoinstances))
;	 (i2-source-protoinstances (get-vals i2 '#$cloned-from))
	 (i2-source-protoinstances (node-cloned-from* i2))
	 (i2-source-protoroots (my-mapcan #'(lambda (i)
					      (get-vals i '#$prototype-participant-of))
					  i2-source-protoinstances))
	 (i12-source-protoroots (intersection i1-source-protoroots i2-source-protoroots))
	 (i1-source-protoinstances-in-protoroots
	  (remove-if-not #'(lambda (i)
			     (intersection i12-source-protoroots (get-vals i '#$prototype-participant-of)))
			 i1-source-protoinstances))
	 (i2-source-protoinstances-in-protoroots
	  (remove-if-not #'(lambda (i)
			     (intersection i12-source-protoroots (get-vals i '#$prototype-participant-of)))
			 i2-source-protoinstances)))
    (cond (*trace-merge-prototype-vals*
	   (km-format t "i1-source-protoroots = ~a~%" i1-source-protoroots)
	   (km-format t "i2-source-protoroots = ~a~%" i2-source-protoroots)
	   (km-format t "intersection = ~a~%" i12-source-protoroots)
	   (km-format t "i1-source-protoinstances-in-protoroots = ~a~%" i1-source-protoinstances-in-protoroots)
	   (km-format t "i2-source-protoinstances-in-protoroots = ~a~%" i2-source-protoinstances-in-protoroots)
	   (km-format t "intersection = ~a~%" (intersection i1-source-protoinstances-in-protoroots
							    i2-source-protoinstances-in-protoroots))))
    (cond
     ((and i12-source-protoroots		; i1 and i2 were cloned from the same prototype..
	   (intersection i1-source-protoinstances-in-protoroots   ; ...and even more so, were cloned from the same NODE
			 i2-source-protoinstances-in-protoroots)) ; in the same prototype...
      (prototype-merge-expr1 slot i1 i2 vs1 vs2 :source-protoroots i12-source-protoroots))
     (t (append vs1 vs2)))))

#|
======================================================================
 Find any &! equalities that should be applied, representing duplicated (non-trimmed) parts of the prototype
 =====================================================================

ALGORITHM for pairing up vs1 and vs2, e.g.,   (a b c (a Foo)) (c d a e (a Bar))
1. [remove-equal-items]
   Remove items that equal, or pending equal, each other, and also non-kb-objects
			(b) (d e)
2. [within prototype-merge-expr1]
   Find, score, and order (best to worst) all possible permutations  -> possible-unifications
									((b e 4)
									 (b d 3))
3. [prototype-merge-expr2]
   Walk through the original vs1 list again. For each v1 in turn:
     a. If the v1 item is a non-kb-object, add v1 to the new-vs1.
     b. If the v1 item is equal/pending-equal to a v2 item, remove the v2 item from vs2. Add v1 to the new-vs1.
     c. If (v1 &! ?v2) is in the possible-unifications, and v2 is still in vs2,
        then add the first (v1 &! v2) (= the best) to new-vs1, and remove v2 from vs2.
     d. Else add v1 to new-vs1.
4. Append any remaining vs2 to the list.

In this example, the result will be: (a (b &! d) c (a Foo) e (a Bar))	[ or same, with b and d switched ]
|#
;;; (prototype-merge-expr1 '#$(a b c (a Foo)) '#$(c d a e (a Bar)))
;;; -> (a (b &! d) c (a Foo) e (a Bar))
(defun prototype-merge-expr1 (slot i1 i2 vs1 vs2 &key source-protoroots)
  (multiple-value-bind
      (uneq-vs1 uneq-vs2)
      (remove-equal-items vs1 vs2)
    (let* ((all-pairs (permute (list uneq-vs1 uneq-vs2))) ;(permute '((a b c) (d e)))->((a d) (a e) (b d) (b e) (c d) (c e))
	   (scored-pairs (remove nil
			  (mapcar #'(lambda (pair)
				      (score-pair (first pair) (second pair) :source-protoroots source-protoroots))
				  all-pairs)))
	   (ordered-scored-pairs (sort scored-pairs #'> :key #'third))
	   (unifications (prototype-merge-expr2 ordered-scored-pairs vs1 vs2 i1 i2 slot)))
      (cond (unifications
	     (let ((expr (append (mapcar #'(lambda (v1)
					     (or (assoc v1 unifications) ; assoc returns (v1 &! v2)
						 v1))
					 vs1)
				 (ordered-set-difference vs2 (mapcar #'third unifications)))))
	       (cond  (*trace-merge-prototype-vals*
			 (km-format t "(merge-prototype-vals ~a ~a ~a ~a ~a)~%" slot i1 i2 vs1 vs2)
			 (km-format t " <- ~a~%" expr)
			 (km-format t "ordered-scored-pairs were:~%~{    ~a~%~}" ordered-scored-pairs)
			 (let ((affected-v1s (mapcar #'first ordered-scored-pairs))
			       (affected-v2s (mapcar #'second ordered-scored-pairs)))
			   (cond ((or (/= (length affected-v1s) (length (remove-duplicates affected-v1s)))
				      (/= (length affected-v2s) (length (remove-duplicates affected-v2s))))
				  (km-format t "WARNING!! Ambiguity in the pairings! DETAILS BELOW:~%")
				  (mapc #'(lambda (pair)
					    (score-pair (first pair) (second pair) :source-protoroots source-protoroots :silentp nil))
					ordered-scored-pairs)
				  )))))
		 (km-int (vals-to-val expr) :target `(#$the ,slot #$of (,i1 &! ,i2)))))
	    (t (append vs1 vs2))))))

;;; Returns just the unifications (v1 &! v2) in no particular order. The ununified elements are NOT returned -- we do
;;; postprocessing above to reorder the unifications and put the unused elements back in.
(defun prototype-merge-expr2 (ordered-scored-pairs vs1 vs2 i1 i2 slot)
  (cond
   ((endp ordered-scored-pairs) nil)
   (t (let* ((best-pair (first ordered-scored-pairs))
	     (v1 (first  best-pair))
	     (v2 (second best-pair)))
	(cond
	 ((and (member v1 vs1)		; not already done
	       (member v2 vs2)
	       (cond ((or (get-vals v1 '#$locked-instance-of)   ; (v1 &? v2) is still essentially a heuristic unification, leading to (v1 &! v2) if successful. So
			  (get-vals v2 '#$locked-instance-of)   ; we need to prohibit this heuristic combination if locked-instance-of prevents it.
			  (get-vals v1 '#$locked-instances-of)  ; Backwards-compatibility with KM invert-slot error
			  (get-vals v2 '#$locked-instances-of)) ;
		      (compatible-classes :instance1 v1 :instance2 v2 :check-locked-classes-p t))
		     (t))
	       (km-int `(,v1 &? ,v2) :target `(#$the ,slot #$of (,i1 &! ,i2)))) ; check it's actually possiblep
	  `((,v1 &! ,v2)
	    ,@(prototype-merge-expr2 (rest ordered-scored-pairs) (remove v1 vs1) (remove v2 vs2) i1 i2 slot)))
	 (t (prototype-merge-expr2 (rest ordered-scored-pairs) vs1 vs2 i1 i2 slot)))))))

#|
(remove-equal-items '#$(a b c (a Foo)) '#$(c d a e (a Bar))) -> (b) (d e)
RETURNS: TWO values
  - vs1 with equalities and non-kb-objects removed
  - vs2 with equalities and non-kb-objects removed
Note that there may be duplicates in vs1 and vs2 which should be removed too :-(
(REMOVE-EQUAL-ITEMS '#$(_Redox-Reaction161 _Redox-Reaction161) '#$(_Oxidation206 _Redox-Reaction210))
|#
(defun remove-equal-items (vs1 vs2)
  (remove-equal-items0 (remove-if-not #'kb-objectp vs1) (remove-if-not #'kb-objectp vs2)))

(defun remove-equal-items0 (vs1 vs2 &key rev-new-vs1 equal-vs2-so-far)
  (let ((v1 (first vs1)))
    (cond
     ((endp vs1) (values (reverse rev-new-vs1) (remove-if #'(lambda (v2) (member v2 equal-vs2-so-far :test #'equal)) vs2)))
     (t (let ((equal-vs2 (remove-if-not #'(lambda (v2)
					    (or (equal v1 v2)
						(pending-equality v1 v2)))	; if (v1 & v2) is on the goal stack
					vs2)))
	  (cond (equal-vs2 (remove-equal-items0 (rest vs1) vs2 :rev-new-vs1 rev-new-vs1 :equal-vs2-so-far (append equal-vs2 equal-vs2-so-far)))
;		(t (remove-equal-items0 (rest vs1) vs2 :rev-new-vs1 (cons v1 rev-new-vs1)))))))))	- BAD TYPO!!!! HLO-3916
		(t (remove-equal-items0 (rest vs1) vs2 :rev-new-vs1 (cons v1 rev-new-vs1) :equal-vs2-so-far equal-vs2-so-far))))))))

#|
(defun remove-equal-items (vs1 vs2 &key rev-new-vs1)
  (let ((v1 (first vs1)))
    (cond
     ((endp vs1) (values (reverse rev-new-vs1) (remove-if-not #'kb-objectp vs2)))
     ((not (kb-objectp v1)) (remove-equal-items (rest vs1) vs2 :rev-new-vs1 rev-new-vs1))
     (t (let ((v2 (find-equal-element v1 vs2)))
	  (cond (v2 (remove-equal-items (rest vs1) (remove v2 vs2 :count 1) :rev-new-vs1 rev-new-vs1))	; :count 1 should be unnecessary
		(t (remove-equal-items (rest vs1) vs2 :rev-new-vs1 (cons v1 rev-new-vs1)))))))))

;;; a (a b c) -> a
;;; a (x b c) -> x   if (a & x) is on the goal stack
(defun find-equal-element (v1 vs2)
  (cond ((member v1 vs2 :test #'equal) v1)
	(t (find-if #'(lambda (v2)
			(pending-equality v1 v2))
		    vs2))))
|#
#|
======================================================================
	VALIDATING AND SCORING A POSSIBLE PAIRWISE MATCH
======================================================================

Suppose we have [[_ProtoX]] -s-> [_ProtoY]
		     |		     |
		     v		     v
		   _CloneX  -s->    V1

v1-source-protoinstances = _ProtoY
v1-source-protoinstances = _ProtoX

vs1 =
_Living-Entity5068 -cloned-from*-> (_Living-Entity3351 _Living-Entity4321 _Living-Entity150)
_Living-Entity5069 -cloned-from*-> (_Living-Entity3350 _Living-Entity4322 _Living-Entity85)
_Living-Entity5073 -cloned-from*-> (_Living-Entity3349 _Living-Entity4323 _Living-Entity402 _Living-Entity85)
_Living-Entity5074 -cloned-from*-> (_Living-Entity3348 _Living-Entity4324 _Living-Entity404 _Living-Entity150)
_Diploid-cell5093 -cloned-from*-> (_Diploid-cell3268 _Diploid-cell5227 _Diploid-cell159 _Diploid-cell270 _Eukaryotic-cell26 _Cell140)
_Living-Entity5138 -cloned-from*-> (_Living-Entity3095 _Living-Entity4324 _Living-Entity404 _Living-Entity150)
_Living-Entity5139 -cloned-from*-> (_Living-Entity3096 _Living-Entity4323 _Living-Entity402 _Living-Entity85)
_Living-Entity5140 -cloned-from*-> (_Living-Entity3097 _Living-Entity4322 _Living-Entity85)
_Living-Entity5141 -cloned-from*-> (_Living-Entity3098 _Living-Entity4321 _Living-Entity150)

vs2 =
_Diploid-cell5093 -cloned-from*-> (_Diploid-cell3268 _Diploid-cell5227 _Diploid-cell159 _Diploid-cell270 _Eukaryotic-cell26 _Cell140)
_Living-Entity5267 -cloned-from*-> (_Living-Entity4321 _Living-Entity150)
_Living-Entity5266 -cloned-from*-> (_Living-Entity4322 _Living-Entity85)
_Living-Entity5265 -cloned-from*-> (_Living-Entity4323 _Living-Entity402 _Living-Entity85)
_Living-Entity5264 -cloned-from*-> (_Living-Entity4324 _Living-Entity404 _Living-Entity150)

Given a v1, pair it with the v2 with the greatest (and > 0) overlap in the cloned-from* values.
|#
;;; [4/23/12] update for HLO-4228
;;; If (v1 &! v2) is valid, return (v1 v2 <score>), where a higher score is more preferred
(defun score-pair (v1 v2 &key source-protoroots (silentp t))
  (let* ((v1-classes (get-vals v1 '#$instance-of))
	 (v1-source-protoinstances (node-cloned-from* v1))
	 (v1-source-protoroots (my-mapcan #'(lambda (i)
					      (get-vals i '#$prototype-participant-of))
					  v1-source-protoinstances)))
;    (km-format t "v1-classes = ~a~%" v1-classes)
;    (km-format t "v1-source-protoroots = ~a~%" v1-source-protoroots)
    (cond
     ((intersection v1-source-protoroots source-protoroots)
      (let* ((v2-classes (get-vals v2 '#$instance-of))
	     (v2-source-protoinstances (node-cloned-from* v2))
	     (v2-source-protoroots (my-mapcan #'(lambda (i)
						  (get-vals i '#$prototype-participant-of))
					      v2-source-protoinstances)))
;	(km-format t "v2-classes = ~a~%" v2-classes)
;	(km-format t "v2-source-protoroots = ~a~%" v2-source-protoroots)
	(cond ((and (intersection    source-protoroots v2-source-protoroots)
		    (intersection v1-source-protoroots v2-source-protoroots)
		    (intersection v1-source-protoinstances v2-source-protoinstances)
;		    (intersection v2-classes v1-classes)
		    (or (classes-subsume-classes v1-classes v2-classes)		; 4/23/12 see [4/23/12] above
			(classes-subsume-classes v2-classes v1-classes))
		    )
	       ;;; Add extra test after yet another failure :-(
	       ;;; A clone should have a subset of the original's classes. See below for the problem.
	       (let ((v1-all-classes (remove-duplicates (my-mapcan #'all-superclasses (remove-subsumers v1-classes))))
		     (v2-all-classes (remove-duplicates (my-mapcan #'all-superclasses (remove-subsumers v2-classes)))))
		 (cond ((or (is-subset-of v1-all-classes v2-all-classes)
			    (is-subset-of v2-all-classes v1-all-classes))
			(let* ((shared-source-protoinstances (intersection v1-source-protoinstances v2-source-protoinstances))
			       (shared-slotsvals (shared-slotsvals v1 v2))
			       (score (+ (* (length shared-source-protoinstances) 100) (length shared-slotsvals))))
			(cond ((not silentp)
			       (let ((*print-right-margin* 9999))
			       (km-format t "(score-pair ~a ~a :source-protoroots ~a)~%" v1 v2 source-protoroots)
			       (km-format t "   v1-classes = ~a~%" v1-classes)
			       (km-format t "   v2-classes = ~a~%" v2-classes)
			       (km-format t "   v1-source-protoroots = ~a~%" v1-source-protoroots)
			       (km-format t "   v2-source-protoroots = ~a~%" v2-source-protoroots)
			       (km-format t "   v1-source-protoinstances = ~a~%" v1-source-protoinstances)
			       (km-format t "   v2-source-protoinstances = ~a~%" v2-source-protoinstances)
			       (km-format t "  (intersection v1-source-protoinstances v2-source-protoinstances) = ~a~%"
					  shared-source-protoinstances)
			       (km-format t "  (shared-slotsvals ~a ~a) = ~a~%" v1 v2 shared-slotsvals)
			       (km-format t "  SCORE = (* 100 ~a) + ~a = ~a~%"
					  (length shared-source-protoinstances) (length shared-slotsvals) score))))
			(list v1 v2 score))))))))))))

#|
This is a 2nd order correction to scoring: If the two instances have identical cloned-from scores,
prefer the pair that have the highest number of shared values on (all) their slots. There was a case of this
in HLO-4335:

      HT1  HT2           HT
      /  ||obj\          | \
    DB   ||   SB      obj| CB
   /  \  ||  /  \        |/  \
  O    Phosph    O       A1   A2

Here, (DB &! CB) -> (Phosph &! A1).
Now (the object-of of (Phosph &! A1)) has ambiguity: Does HT unify with HT1 or HT2?
The scores were equal and so it makes a bad guess and picks HT2, resulting in (DB &! SB),
which is inconsistent but there was no constraint in the KB.
With the refinement, as HT1 and HT share DB/CB as a slot-value, HT1 is preferred.
|#
(defun shared-slotsvals (i1 i2)
  (let ((vs1 (remove-duplicates (my-mapcan #'vals-in (get-slotsvals i1))))
	(vs2 (remove-duplicates (my-mapcan #'vals-in (get-slotsvals i2)))))
    (intersection vs1 vs2 :test #'(lambda (v1 v2)
				    (or (equal v1 v2)
					(pending-equality v1 v2)))))) ; if (v1 & v2) is on the goal stack

#|
The unexpanded KB has:

Synthesis-Of-ATP-By-Oxidative-Phosphorylation
  agent: ATP-Synthase[1]
  subevent: Oxidative-Phosphorylation
  	       agent: ATP-Synthase[1]


Oxidative-Phosphorylation
  agent: ATP-Synthase[1]
  subevent: Chemiosmosis
 	      agent: ATP-Synthase[1]

These should be assembled into:

Synthesis-Of-ATP-By-Oxidative-Phosphorylation
  agent: ATP-Synthase[1]
  subevent: Oxidative-Phosphorylation
  	       agent: ATP-Synthase[1]
  	       subevent: Chemiosmosis
	       		    agent: ATP-Synthase[1]

Note that ATP-Synthase is the agent of *three* events in the taxonomy.
merge-prototype-vals causes
  Synthesis-Of-ATP-By-Oxidative-Phosphorylation &? Chemiosmosis to be unified,
as it passes the test for being cloned from the same node.
a result, the sub-sub-event is unified with the event, and we end up with
a subevent cycle ;-(

Here's the bad behavior. Note Channel-Protein is the Skolem name for ATP-Synthase:

[1c] KM(65): (MERGE-PROTOTYPE-VALS '|agent-of| '|_Channel-Protein548| '|_Channel-Protein616|
                      '(|_Oxidative-Phosphorylation546| |_Synthesis-Of-ATP-By-Oxidative-Phosphorylation544|
                       |_Synthesis-Of-ATP-By-Oxidative-Phosphorylation544|)
                      '(|_Add605| |_Oxidative-Phosphorylation615| |_Chemiosmosis619|))
i1-source-protoroots = (_Oxidative-Phosphorylation2918 _Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741 _ATP-Synthase10773
                        _Facilitated-Diffusion31 _Enzyme739 _Metabolic-Pathway15 _Channel-Protein457 _Transport-Protein16144
                        _Membrane-Protein12408 _Biomembrane376 _Protein181 _Polymer35474 _Amphipathic-Molecule8633 _Organic-Molecule27159
                        _Molecule22316 _Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012)
i2-source-protoroots = (_Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741 _ATP-Synthase10773 _Facilitated-Diffusion31
                        _Enzyme739 _Metabolic-Pathway15 _Channel-Protein457 _Transport-Protein16144 _Membrane-Protein12408 _Biomembrane376
                        _Protein181 _Polymer35474 _Amphipathic-Molecule8633 _Organic-Molecule27159 _Molecule22316
                        _Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012 _Oxidative-Phosphorylation2918)
intersection = (_Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012 _Molecule22316 _Organic-Molecule27159 _Amphipathic-Molecule8633
                _Polymer35474 _Protein181 _Biomembrane376 _Membrane-Protein12408 _Transport-Protein16144 _Channel-Protein457
                _Metabolic-Pathway15 _Enzyme739 _Facilitated-Diffusion31 _ATP-Synthase10773
                _Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741 _Oxidative-Phosphorylation2918)
i1-source-protoinstances-in-protoroots = (_Enzyme615 _Channel-Protein1033 _ATP-Synthase10773 _Entity1915 _Enzyme739 _Enzyme1156
                                          _Channel-Protein457 _Transport-Protein16144 _Membrane-Protein12408 _Integral-Protein10289
                                          _Protein181 _Polymer35474 _Amphipathic-Molecule8633 _Organic-Molecule27159 _Molecule22316
                                          _Enzyme18220)
i2-source-protoinstances-in-protoroots = (_Channel-Protein1033 _ATP-Synthase10773 _Entity1915 _Enzyme739 _Enzyme1156 _Channel-Protein457
                                          _Transport-Protein16144 _Membrane-Protein12408 _Integral-Protein10289 _Protein181 _Polymer35474
                                          _Amphipathic-Molecule8633 _Organic-Molecule27159 _Molecule22316 _Enzyme18220 _Enzyme615)
intersection = (_Enzyme18220 _Molecule22316 _Organic-Molecule27159 _Amphipathic-Molecule8633 _Polymer35474 _Protein181
                _Integral-Protein10289 _Membrane-Protein12408 _Transport-Protein16144 _Channel-Protein457 _Enzyme1156 _Enzyme739
                _Entity1915 _ATP-Synthase10773 _Channel-Protein1033 _Enzyme615)

----------
(score-pair _Synthesis-Of-ATP-By-Oxidative-Phosphorylation544 _Chemiosmosis619):
v1-source-protoroots = (_ATP-Synthase10773 _Synthesis-of-ATP525 _Exergonic-Reaction5501 _Anabolic-Pathway41 _Cellular-Process22803
                        _Synthesis19719 _Metabolic-Pathway15 _Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012 _Endergonic-Reaction1412
                        _Create5251 _Spontaneous-Change1085 _Chemical-Reaction2833 _Non-Spontaneous-Change1104)
v2-source-protoroots = (_Oxidative-Phosphorylation2918 _Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741
                        _Facilitated-Diffusion31 _Diffusion539 _Passive-Transport-Across-Biomembrane1159 _Cellular-Process22803
                        _Directed-Motion490 _Passive-Transport672 _Spontaneous-Change1085)
source-protoroots = (_Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012 _Molecule22316 _Organic-Molecule27159 _Amphipathic-Molecule8633
                     _Polymer35474 _Protein181 _Biomembrane376 _Membrane-Protein12408 _Transport-Protein16144 _Channel-Protein457
                     _Metabolic-Pathway15 _Enzyme739 _Facilitated-Diffusion31 _ATP-Synthase10773
                     _Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741 _Oxidative-Phosphorylation2918)
v1-source-protoinstances = (_Chemical-Reaction11055 _Synthesis-of-ATP525 _Exergonic-Reaction5501 _Anabolic-Pathway41 _Cellular-Process22803
                            _Synthesis19719 _Metabolic-Pathway15 _Synthesis-Of-ATP-By-Oxidative-Phosphorylation18012
                            _Endergonic-Reaction1412 _Create5251 _Spontaneous-Change1085 _Chemical-Reaction2833 _Non-Spontaneous-Change1104)
v2-source-protoinstances = (_Chemiosmosis16979 _Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein741 _Facilitated-Diffusion31
                            _Diffusion539 _Passive-Transport-Across-Biomembrane1159 _Cellular-Process22803 _Directed-Motion490
                            _Passive-Transport672 _Spontaneous-Change1085)
v1-classes = (Synthesis-Of-ATP-By-Oxidative-Phosphorylation Synthesis-of-ATP Endergonic-Reaction Non-Spontaneous-Change Create
              Metabolic-Pathway Spontaneous-Change Cellular-Process)
v2-classes = (Chemiosmosis Event Facilitated-Diffusion Passive-Transport-Across-Biomembrane
              Movement-Of-Entity-Across-Biomembrane-Using-Channel-Protein Cellular-Process Life-Cycle-Process)
(intersection v1-source-protoinstances v2-source-protoinstances) = (_Spontaneous-Change1085 _Cellular-Process22803)
----------
ordered-scored-pairs were:
    (_Synthesis-Of-ATP-By-Oxidative-Phosphorylation544 _Chemiosmosis619 2)

Note that as both _Synthesis-Of-ATP-By-Oxidative-Phosphorylation544 and _Chemiosmosis619 were cloned from
_Cellular-Process22803, it looks like they are equal. But that can't be the case as their classes aren't
subset/superset of each other, so v2 isn't just a recloning of v1. I'm not completely sure this test
is foolproof but seeks ok :-)
|#

;;; ======================================================================
;;; 		LAZY-UNIFY-EXPRS
;;; Does a subsumption check first
;;; ======================================================================

;;; Must be an & expr, ie. either (a & b), or ((a b) && (c d))
;;; The arguments to &/&& may themselves be &/&& expressions,
;;; 	eg. ((a & b) & c),
;;;	    ( (((a b) && (c d))) && (e f) )
;;; [ Note  (  ((a b) && (c d))  && (e f) ) is illegal, as the args to && must be a *list* of expressions ]
;;; ALWAYS returns a list of values (necessarily singleton, for '&)
;;; **NOTE** No point in doing any classification *DURING* unification (?). Better to wait until finished, and THEN do
;;; unification. But...might be incomplete? Better leave it in.
(defun lazy-unify-&-expr (expr &key (joiner '&) (fail-mode 'fail) target)
  (let* ( ; (constraints (find-constraints expr))		OLD
	  (constraints nil)					; DISABLE now! - move to get-slotvals.lisp
	  (unified0 (lazy-unify-&-expr0 expr :joiner joiner :fail-mode fail-mode :target target))
	  (unified (cond ((val-unification-operator joiner) (list unified0)) 	; must listify for &
			 (t unified0)))
	  (checked (cond (constraints (enforce-constraints unified constraints :target target))
			 (t unified))) )
    (remove nil checked)))

(defun lazy-unify-&-expr0 (expr &key (joiner '&) (fail-mode 'fail) target)
  (cond ((and (tracep) (not (traceunifyp)))

	 (let ((*trace* nil))
	   (lazy-unify-&-expr1 expr :joiner joiner :fail-mode fail-mode :target target)))
;	 (prog2 (suspend-trace) (lazy-unify-&-expr1 expr :joiner joiner :fail-mode fail-mode :target target)
;	   (unsuspend-trace)))
	(t (lazy-unify-&-expr1 expr :joiner joiner :fail-mode fail-mode :target target))))

;;; Input: A & or && expression. Output: a value (&) or value set (&&)
(defun lazy-unify-&-expr1 (expr &key (joiner '&) (fail-mode 'fail) target)
  (cond ((null expr) nil)
	((and (listp expr)
	      (eq (second expr) joiner))		; either (a & b) or (a & b & c)
	 (cond ((>= (length expr) 4)
		(cond ((neq (fourth expr) joiner)
		       (report-error 'user-error "Badly formed unification expression ~a encountered during unification!~%" expr)))
		(let ( (revised-expr (cond		 ; (a & b & c) -> ((a & b) & c),  (as && bs && cc) -> (((as && bs)) & c)  [NB extra () for &&]
				      ((val-unification-operator joiner)
				       `( (,(first expr)  ,joiner ,(third expr))   ,joiner ,@(rest (rest (rest (rest expr))))))
				      ((set-unification-operator joiner)
				       `(((,(first expr) ,joiner ,(third expr)))   ,joiner ,@(rest (rest (rest (rest expr)))))))) )
		  (lazy-unify-&-expr1 revised-expr :joiner joiner :fail-mode fail-mode :target target)))
	       ((val-unification-operator joiner)
		(lazy-unify-exprs (lazy-unify-&-expr1 (first expr) :joiner joiner :fail-mode fail-mode :target target)
				  (lazy-unify-&-expr1 (third expr) :joiner joiner :fail-mode fail-mode :target target)
				  :eagerlyp (eq joiner '&!) :fail-mode fail-mode :target target))				; [1]
	       ((set-unification-operator joiner)
		(lazy-unify-expr-sets (lazy-unify-&-expr1 (first expr) :joiner joiner :fail-mode fail-mode :target target)
				      (lazy-unify-&-expr1 (third expr) :joiner joiner :fail-mode fail-mode :target target)
				      :eagerlyp (eq joiner '&&!) :fail-mode fail-mode :target target))))
	((and (singletonp expr)				; special case: (((a b) && (c d))) [NB double parentheses] -> (a b c d)
	      (listp (first expr))			; This comes if I do (((set1 && set2)) && set3)
	      (set-unification-operator joiner)		; Note: ((set1 && set2) && set3) is badly formed! (&& takes a *set* of expressions)
	      (eq (second (first expr)) joiner))
	 (lazy-unify-&-expr1 (first expr) :joiner joiner :fail-mode fail-mode :target target))
	(t expr)))

;;; ======================================================================
;;; 	    UNIFICATION OF TWO EXPRESSIONS
;;; Returns an ATOM, or more strictly something which passes an is-km-term() test, eg. a triple.
;;; This *DOESN'T* enforce type constraints
;;; ======================================================================

;;; [1] Classify does a &, then does (undone X), which rechecks the classification a second time.
;;; Thus classify needs to know if & fails, or else it will loop repeatedly rechecking the classification.
;;; Thus we make lazy-unify-exprs return NIL rather than have a recovery attempt if there's a problem.
;;; [2] fail-mode = fail, not error here, as we want to report the error at the lazy-unify-exprs
;;;	level, not here.
;;; RETURNS a SINGLE ATOMIC VALUE
;;; [3] Presumably we took this out to make sure that expressions in the <val> position didn't get evaluated, e.g.
;;;	(:triple *Sue mood (a Mood))
(defun lazy-unify-exprs (x y &key eagerlyp classes-subsumep (fail-mode 'fail) target)
  (cond ((and (or (protoinstancep x)
		  (protoinstancep y))
	      (not (am-in-prototype-mode)))
	 (report-error 'user-error
			"Attempted unification with protoinstance(s) ~a when not in prototype mode!~%         Doing (~a ~a ~a)~%"
			(delistify (remove nil `(,(cond ((protoinstancep x) x))
						 ,(cond ((protoinstancep y) y)))))
			x
			(cond ((and eagerlyp classes-subsumep) '&+!)
			      (eagerlyp '&!) (classes-subsumep '&+) (t '&))
			y)))
  (cond ((and (null x) (null y)) nil)
	((null x) (km-unique-int y :target target))		; [2]
	((null y) (km-unique-int x :target target))
;#|bug|#((equal x y) x)
	((km-equal x y) (km-unique-int x :target target))
	((and (km-triplep x) (km-triplep y))		; [3]
	 nil)
	((or (km-structured-list-valp x)
	     (km-structured-list-valp y))
	 (let ( (dx (desource x))
		(dy (desource y)) )
#|	 (cond ((not (km-structured-list-valp dx)) (lazy-unify-exprs (list (first dy) dx) dy  			; dx & (:args dx dy)
								    :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode
								    :target target))
	       ((not (km-structured-list-valp dy)) (lazy-unify-exprs dx (list (first dx) dy)			; (:args dx dy) & dx
								    :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode
								    :target target))
|#
	 (cond ((and (km-structured-list-valp dy)
		     (not (km-structured-list-valp dx)))
		(let ( (edx (km-unique-int dx)) )
		  (cond ((not (km-structured-list-valp edx))
			 (cond ((null edx) (km-unique-int dy))		; dy is the structured item, edx is the evaluated
			       ((anonymous-instancep edx)
				(let ((ans (lazy-unify edx (km-unique-int dy) :fail-mode fail-mode)))
				  (cond (ans)
					((eq fail-mode 'error)
					 (report-error 'user-error "Unification (~a ~a ~a) failed!~%" x
						       (cond ((and eagerlyp classes-subsumep) '&+!)
							     (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y)
					 nil))))
			       ((km-argsp dy)
				(lazy-unify-exprs (list (first dy) edx) dy :fail-mode fail-mode))  			; dx & (:args dx dy)
			       ((eq fail-mode 'error)
				(report-error 'user-error "Unification (~a ~a ~a) failed!~%" x
					      (cond ((and eagerlyp classes-subsumep) '&+!)
						    (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y)
				nil)))
			(t (lazy-unify-exprs edx dy :fail-mode fail-mode)))))
	       ((and (km-structured-list-valp dx)
		     (not (km-structured-list-valp dy)))
		(let ( (edy (km-unique-int dy)) )
		  (cond ((not (km-structured-list-valp edy))
			 (cond ((null edy) (km-unique-int dx))
			       ((and (anonymous-instancep edy)
;				     (just-a-thing edy)		; special case
				     )
				(let ((ans (lazy-unify (km-unique-int dx) edy :fail-mode fail-mode)))
				  (cond (ans)
					((eq fail-mode 'error)
					 (report-error 'user-error "Unification (~a ~a ~a) failed!~%" x
						       (cond ((and eagerlyp classes-subsumep) '&+!)
							     (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y)
					 nil))))
			       ((km-argsp dx)
				(lazy-unify-exprs dx (list (first dx) edy) :fail-mode fail-mode))  			; dx & (:args dx dy)
			       ((eq fail-mode 'error)
				(report-error 'user-error "Unification (~a ~a ~a) failed!~%" x
					      (cond ((and eagerlyp classes-subsumep) '&+!)
						    (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y)
				nil)))
			(t (lazy-unify-exprs dx edy :fail-mode fail-mode)))))
	       ((and (listp dx) (listp dy)
		     (eql (first dx) (first dy))
		     (neq (first dx) '#$:triple)	; [3]
		     (unify-structured-list-vals dx dy :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode)))
	       ((eq fail-mode 'error)
		(report-error 'user-error "Unification (~a ~a ~a) failed!~%" x
			      (cond ((and eagerlyp classes-subsumep) '&+!)
				    (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y)
		nil))))
	((existential-exprp y)
	 (let ( (xf (km-unique-int x :target target)) )
	   (cond ((null xf) (km-unique-int y :target target))
		 (t (unify-with-existential-expr xf y :classes-subsumep classes-subsumep :eagerlyp eagerlyp
						 :fail-mode fail-mode :target target)))))
	((existential-exprp x)
	 (let ( (yf (km-unique-int y :target target)) )
	   (cond ((null yf) (km-unique-int x :target target))
		 (t (unify-with-existential-expr yf x :classes-subsumep classes-subsumep :eagerlyp eagerlyp
						 :fail-mode fail-mode :target target)))))
	((and (kb-objectp x)
	      (explained-by x y target))
	 (km-trace 'comment "[ ~a was originally derived from ~a, so must unify with it! ]" x y)
	 x)				; NEW
	(t (let ( (xf (km-unique-int x :target target))
		  (yf (km-unique-int y :target target)) )
	     (cond
	      ((null xf) yf)
	      ((null yf) xf)
	      ((or (km-structured-list-valp xf)
		   (km-structured-list-valp yf))
	       (lazy-unify-exprs xf yf :classes-subsumep classes-subsumep :eagerlyp eagerlyp
				 :fail-mode fail-mode :target target))
	      ((and (is-km-term xf) (is-km-term yf))
	       (cond ((lazy-unify xf yf :eagerlyp eagerlyp :classes-subsumep classes-subsumep :fail-mode fail-mode))
		     ((eq fail-mode 'error)
		      (report-error 'user-error "Unification (~a ~a ~a) failed!~%" xf
				    (cond ((and eagerlyp classes-subsumep) '&+!)
					  (eagerlyp '&!) (classes-subsumep '&+) (t '&)) yf)
#| NEW - give up [1] |#		   nil)))
	      ((eq fail-mode 'error)
	       (report-error 'user-error
			     "Arguments in a unification expression should be unique KM objects!~%Doing (~a ~a ~a) [ie. (~a ~a ~a)]~%"
			     x (cond ((and eagerlyp classes-subsumep) '&+!)
				     (eagerlyp '&!) (classes-subsumep '&+) (t '&)) y
			     xf (cond ((and eagerlyp classes-subsumep) '&+!)
				      (eagerlyp '&!) (classes-subsumep '&+) (t '&)) yf)))))))

;;;; e.g. _X is a concept with no properties
;(defun no-properties (frame) (not (symbol-plist frame)))
;(defun just-a-thing (instance)
;  (and (or (null (get-slotsvals instance :situation *global-situation*))
;	   (equal (get-slotsvals instance :situation *global-situation*) '#$((instance-of (Thing)))))
;       (or (am-in-global-situation)
;	   (null (get-slotsvals instance)))))		; no local situation values

;;; ======================================================================

;;; Called by lazy-unify-exprs
;;; Break up structured instances, and feed back fragments to lazy-unify-exprs
;;; [1] 3/13/01 - Bug! Need to check *all* unifications succeed before effecting them, not just one at a time!
;;;	Correction is to add this up-front test. This is slightly redundant (KM will work out the unifications twice, once in the test
;;;	and once when actually doing it), but that's ok.
;;;	It's possible KM will *think* a unification's possible but then fail to actually do it. Yikes! In this case, KM will be stuck
;;;	with a partly unified sequence. We'll live with that for now.
;;; [2] Must pass through km-int, as the elements may be expressions (not guaranteed to be atomic!)
;;; [3] & of structured vals are only decommented at the top level by km-int, so we need to do another decommenting here so that remaining
;;;     comments aren't taken as actual values themselves!
(defun unify-structured-list-vals (instance10 instance20 &key classes-subsumep eagerlyp fail-mode)
 (let ( (instance1 (desource+decomment-top-level instance10))		; [3]
	(instance2 (desource+decomment-top-level instance20)) )
  (cond ((and (listp instance1) (listp instance2)
	      (eql (first instance1) (first instance2))
;	      (try-lazy-unify instance1 instance2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp))	; [1]
	      (every #'(lambda (pair)										; [2]
			 (or (km-setp (first pair))			; ((:set a) &? _X), also ((:set a b) &? NIL) should succeed
			     (km-setp (second pair))
			     (km-int `(,(first pair) ,(cond (classes-subsumep '&+?) (t '&?)) ,(second pair)))))
		     (transpose (list (rest instance1) (rest instance2)))))
	 (let ( (unification (unify-structured-list-vals2 (rest instance1) (rest instance2) :classes-subsumep classes-subsumep :eagerlyp eagerlyp
							  :fail-mode fail-mode)) )
	   (cond ((eq unification 'fail)
		  (report-error 'nodebugger-error
				"Yikes! I partly unified two sequences ~a and ~a but then found they couldn't be unified!~%I'll continue and hope for the best (sorry!)...~%" instance1 instance2))
		 (t (cons (first instance1) unification))))))))

(defun unify-structured-list-vals2 (elements1 elements2 &key classes-subsumep eagerlyp fail-mode)
  (cond ((null elements1) elements2)
	((null elements2) elements1)
	((or (km-setp (first elements1))
	     (km-setp (first elements2)))
	 (let* ( (set-element1 (cond ((km-setp (first elements1)) (set-to-list (first elements1))) (t (list (first elements1)))))
		 (set-element2 (cond ((km-setp (first elements2)) (set-to-list (first elements2))) (t (list (first elements2)))))
		 (unification (lazy-unify-expr-sets set-element1 set-element2 #|:classes-subsumep classes-subsumep|# :eagerlyp eagerlyp
						   )) )
	   (cond (unification (let ( (unifications (unify-structured-list-vals2 (rest elements1) (rest elements2)
										:classes-subsumep classes-subsumep :eagerlyp eagerlyp
										:fail-mode fail-mode)) )
				(cond ((neq unifications 'fail) (cons (vals-to-val unification) unifications))
				      (t 'fail))))
		 (t 'fail))))
	(t (let* (
;		   (e1 (km-unique-int (first elements1)))	; - not necc to evaluate!
;		   (e2 (km-unique-int (first elements2)))
		   (e1 (first elements1))
		   (e2 (first elements2))
		   (unification (lazy-unify-exprs e1 e2 :classes-subsumep classes-subsumep :eagerlyp eagerlyp :fail-mode fail-mode)) )
	     (cond ((or unification
			(km-null e1)				; if e1 or e2 is NIL, or evaluates to NIL, then the
			(km-null e2)				; unification necessarily MUST succeed (inc. nil & nil -> nil)
			(and (not (existential-exprp e1)) (null (km-unique-int e1)))   ; efficiency: existentials can never be nil
			(and (not (existential-exprp e2)) (null (km-unique-int e2))))
		    (let ( (unifications (unify-structured-list-vals2 (rest elements1) (rest elements2)
								      :classes-subsumep classes-subsumep :eagerlyp eagerlyp
								      :fail-mode fail-mode)) )
		      (cond ((neq unifications 'fail) (cons unification unifications))
			    (t 'fail))))
		   (t 'fail))))))

;;; ======================================================================
;;;		LAZY-UNIFY-EXPR-SETS
;;; Handling of expressions: Here KM limits the evaluation of the second expression list,
;;; so as to avoid creating unnecessary instances and simplify the proof trace.
;;; HOWEVER: This is extremely cryptic to watch in the normal execution of KM,
;;; so hide it from the user!!
;;; ======================================================================

;;; Allows us to switch off KM's heuristic unification mechanism
(defparameter *no-heuristic-unification* nil)

#|
						((_Door178 _Door179 _Cat23 _Bumper176) && ((a Cat) (MyCar has-door) (a Door) (a Door))
  [1] evaluate any non-existential exprs		((_Door178 _Door179 _Cat23 _Bumper176) && ((a Cat) _Door178 (a Door) (a Door)))
  [2] remove duplicates				(_Door178) APPEND ((_Door179 _Cat23 _Bumper176) && ((a Cat) (a Door) (a Door))
  [3] remove subsuming elements  		(_Door178 _Door179 _Cat23) APPEND ((_Bumper176) && ((a Door)))
  [4] evaluate the remaining exprs		(_Door178 _Door179 _Cat23) APPEND ((_Bumper176) && (_Door180))
  [5] unify the result				(_Door178 _Door179 _Cat23 _Bumper176 _Door180)

[6] NOTE this is guaranteed to succeed, as there are no constraints here (constraints are on expressions in situ on slots)

[7] Eager set unification: previous error:
	(_Move3 _Enter4) &&! (_Enter5)
     With :eagerlyp passed to lazy-unify-sets, thus to lazy-unify-vals, I *force* _Enter5 and _Move3 to unify, even if there's a
	constraint violation. Urgh!
    Really I need a two-pass implementation:
	  (i) Do a &&
	  (ii) Evaluate the subexpression unifications & / &&
(((_Car1 with (color (_Red1 _Green1))) _Toy1) &&! ((_Car2 with (color (_Green2)))))
 -> ((_Car12 with (color (((_Red1 _Green1) &&! _Green2)))) _Toy1)
  -> need to map through all the slot-values of the unifications, looking for &&! and executing them.
     Will this catch them all? I *think* so.  Note &! CAN be executed within lazy-unify-slotvals, as this IS unambiguous, and thus
	we don't need this two-pass approach.
     I haven't accounted for multiple situations, though.

QUESTION: GIVEN: ((the parts of _Engine13)) && ((the parts of _Engine13) _Distributor14)
	  AND (the parts of _Engine13) include _Distributor12, then should _Distributor12 and _Distributor14 unify? Answer: no I think.
	  Any evaluation of a shared expression should *augment*, not *unify with* other values present.
|#

(defun lazy-unify-expr-sets (exprs1 exprs2 &key eagerlyp (fail-mode 'fail) target)
  (declare (ignore fail-mode))		; [6]
  (cond
   ((or (not (listp exprs1)) (not (listp exprs2)))
    (report-error 'user-error "(~a && ~a): Arguments should be *sets* of values, but just found a single value!~%"
		  exprs1 exprs2))
   (t (cond ((and (or (some #'protoinstancep exprs1)
		      (some #'protoinstancep exprs2))
		  (not (am-in-prototype-mode)))
	     (report-error 'user-error
			   "Attempt to unify protoinstance(s) ~a when not in prototype mode!~%         Doing (~a ~a ~a)~%"
			   (delistify `(,@(remove-if-not #'protoinstancep exprs1)
					,@(remove-if-not #'protoinstancep exprs2)))
			   exprs1
			   (cond (eagerlyp '&&!) (t '&&))
			   exprs2)))
      (cond
       ((subbagp exprs2 exprs1 :test #'equal) (km-int (vals-to-val exprs1) :target target))
       (t (let ( (set1 (km-int (vals-to-val exprs1) :target target)) )
	    (cond
	      ((null set1)
	       (km-int (vals-to-val exprs2) :target target))	; i.e. evaluated exprs1 is a subbag of exprs2
	      (t
	       (multiple-value-bind
		(unexplained-set1 unexplaining-exprs2)
		(remove-explained-vals set1 (dereference exprs2) :target target)
		(let* ( (set2 (remove-dup-instances
			       (my-mapcan #'(lambda (expr) ; [1] evaluate definite exprs in set2
					     (cond ((or (and (not (existential-exprp expr))
							     (not (km-structured-list-valp expr)))
							*no-heuristic-unification*)
						    (km-int expr :target target))
						   (t (list expr))))
					 unexplaining-exprs2))))
;	                (_dummy (km-format t "set1 = ~a, exprs2 = ~a, explained-set1 = ~a, unexplained-set1 = ~a, unexplaining-exprs2 = ~a~%"
;					 set1 exprs2 explained-set1 unexplained-set1 unexplaining-exprs2))
;	                (shared-elements (ordered-intersection unexplained-set1 set2 :test #'equal))		; [2]
;	                (reduced-set1 (ordered-set-difference unexplained-set1 shared-elements :test #'equal))
;	                (reduced-set2 (ordered-set-difference set2 shared-elements :test #'equal)) )
;		  (km-format t "unexplaining-exprs2 = ~a, set2 = ~a~%" unexplaining-exprs2 set2)
	          (multiple-value-bind
		   (reduced-set1 reduced-set2)						; don't need shared elements: added back in at [9] below
		      (remove-shared-elements unexplained-set1 set2 :test #'equal)
;		    (km-format t "reduced-set2 = ~a~%" reduced-set2)
		   (multiple-value-bind
		    (reduced-set1b reduced-set2b)
		    (do-pending-equalities reduced-set1 reduced-set2 :eagerlyp eagerlyp :target target)
		   (multiple-value-bind
		    (more-reduced-set1 more-reduced-set2)				; don't need shared elements: added back in at [9] below
		    (do-forced-unifications reduced-set1b reduced-set2b :eagerlyp eagerlyp :target target)
		    (multiple-value-bind
		     (remainder-set2 remainder-set1 subsumed-set1)			; [3]
; PC	             (remove-subsuming-exprs more-reduced-set2 more-reduced-set1)	; (expects exprs first, instances next)
; PC - Can I get away with :allow-coeercion t?? What will the effect be?
#|PC|#	             (remove-subsuming-exprs more-reduced-set2 more-reduced-set1
			     :allow-coercion t :target target :eagerlyp eagerlyp) ; more-reduced-set1 is already eval'd
#|[9]|#	             (declare (ignore subsumed-set1))

                     (let* ( (new-set2 (my-mapcan #'(lambda (expr)			; [4] now evaluate (remaining) existential exprs in set2
						      (cond ((or (existential-exprp expr)		; i.e., opposite of [1]
								 (km-structured-list-valp expr))
							     (km-int expr :target target))
							    (t (list expr))))
						  remainder-set2))
#| NEW |#	            (unified (lazy-unify-sets remainder-set1 new-set2 :eagerlyp eagerlyp :target target))
; [9] preserve ordering as best as possible:
; NOTE: unified contains (possibly reordered) set1 elements followed by ununified and STILL ORDERED remaining set2 elements
; Doing (dereference set1) is a clever way of preserving the original set1 orderings after doing the unifications.
;                            (final-result (remove-dup-instances (append (dereference set1)
;									(ordered-set-difference (dereference unified) (dereference set1))))) )
; [9] preserve ordering as best as possible:
; NEW: unified contains (possibly reordered) UNIFIED set1 & set2 elements *ONLY* (no ununified elements)
; Doing (dereference set1) is a clever way of preserving the original set1 orderings after doing the unifications.
                            (final-result (remove-dup-instances (append (dereference set1)
									(ordered-set-difference (dereference new-set2) (dereference unified))))))
		       (cond (eagerlyp (mapc #'eagerly-evaluate-exprs final-result)))
		       final-result)))))))))))))))

;;; ----------------------------------------------------------------------

#|
RETURNS two values
 - vals which are unexplained by any of exprs
 - exprs which don't explain any vals
ALGORITHM:
  (i) find all the explanations of vals
 (ii) For each val,
	- if val is explained by (path1) (path2) (a C) (a C2) in exprs then:
		- remove val from list of unexplained vals
		- remove *all* explaining paths, i.e., path1, path2
		- remove *one* existential, e.g., (a C).
***Actually** in the current implementation of explanations-for, explanations are *necessarily* existential-exprs, but we allow for
the case when they're also not below, even though it never currently can happen.
 Later - neah, drop this
[1] NOTE: cache-explanations now LEAVES comments in, because if we have two rules:
	(a Wing with (has-logo (t)) (@ Airplane parts)))
	(a Wing with (has-logo (t)) (@ Jumbo parts)))
    Then these should *BOTH* be recorded as explanations for _Wing1. If we discard rule 2 as "already used" as _Wing1 is
    explained by rule 1, then we'll lose rule 2 as an explanation for _Wing1.
    HOWEVER: We really want some clever matching which will "realize" that these two rules match, i.e. a value explained by
    rule 1 is also covered by rule 2...and hence rule 2 can be removed, but ALSO noted as an explanation for that value.
    We can do this at a later time.
|#
;;; [2] Now *includes* source info
;;; [3] cached-explanations may include (a Engine), existing recorded explanations may record (a Engine (@ Car parts)),
;;; 	all-explanations may include explanation (a Engine (@ Vehicle parts)), so need to record this explanation too if we
;;;     are going to drop the expr!
;;; [4a] The existential explanation is removed on the way down; [4b] The path explanations are removed on the way back
;(defun remove-explained-vals (vals exprs &key target)
;  (declare (ignore target))
;  (values vals exprs))

#|
Problem before:
 (_Car1 _Car2)  ((a Car with (color (Red))) (a Car))
and suppose _Car1 is explained by (a Car)
This causes the ordering to be violated:
	_Car1 matches (a Car)
	_Car2 matches (a Car with (color (Red)))
and this is bad for the Shaken system!

This reduced version insists the matching is sequential and exits otherwise [5].
Hmm... but doesn't seem to speed things up much, particularly because there are paths in the exprs (which aren't in the cache).

----------------------------------------
[6] Revised - we still insist on sequentiality, but now allow gaps to avoid the below problem.
(Parent-Stuff has (superclasses (Entity)))
(every Parent-Stuff has
   (location ((a Place)))
   (has-part ((a Entity))))

(Child-Thing has (superclasses (Parent-Stuff)))
(every Child-Thing has
   (has-part ((a Entity) (a Tangible-Entity) (a Physical-Object))))
(every Child-Thing has-definition
   (instance-of (Parent-Stuff))
   (has-part ((a Tangible-Entity))))

[_Situation6] KM> (a Parent-Stuff)
(_Parent-Stuff7)

[_Situation6] KM> (the has-part of _Parent-Stuff7)
(_Entity8)

[_Situation6] KM> (_Parent-Stuff7 also-has (has-part ((a Tangible-Entity))))
(_Parent-Stuff7 #|"a Child-Thing"|#)	; classified fine

;;; Problem - the also-has Tangible-Entity is unified with (a Entity) on Child-Thing.
[_Situation6] KM> (the has-part of _Parent-Stuff7)
(_Entity8 #|"a Tangible-Entity"|# _Tangible-Entity9 _Physical-Object10)
|#
(defun remove-explained-vals (vals exprs &key target)
  (cond ((null vals) (values nil exprs))
	(t (let* ( (val (first vals))
		   (expr (first exprs))
		   (cached-explanations (cached-explanations-for val)) )
	     (cond ((member (desource expr) cached-explanations :test #'equal)		; first val explained by first expr...
		    (cond (target (record-explanation-for target val expr)))		; [3]
		    (cond ((existential-exprp expr)
			   (remove-explained-vals (rest vals) (rest exprs) :target target))  ; [4a]
			  (t (multiple-value-bind 					     ; expr is a path
			      (unexplained-vals unexplaining-exprs)
			      (remove-explained-vals (rest vals) exprs :target target)       ; [4a]
			      (values unexplained-vals (remove expr unexplaining-exprs :test #'equal))))))	       ; [4b]

;		   (t (values vals exprs)))))))						; [5]
; NEW: *do* continue recursively -- preserve order, but allow gaps [6]
		   (t
		    (multiple-value-bind
		     (unexplained-vals unexplaining-exprs)
		     (remove-explained-vals (rest vals) exprs :target target)
		     (values (cons val unexplained-vals) unexplaining-exprs))))))))

#|
(defun remove-explained-vals (vals exprs &key target)
  (cond ((endp vals) (values nil exprs))
	(t (let* ( (val (first vals))
; correct!	   (explanations (intersection (cached-explanations-for val) exprs :test #'equal)) 	; [1]

; Temp - need to remove these for backward library compatibility...
;		   (cached-explanations (desource (cached-explanations-for val)))	; desource to be removed shortly...
		   (cached-explanations (cached-explanations-for val))
		   (explanations (remove-if-not #'(lambda (expr) (member (desource expr) cached-explanations :test #'equal)) exprs)) ; [2]
		   (path-explanations (remove-if #'existential-exprp explanations))
		   (existential-explanation (find-if #'existential-exprp explanations)) 		; find just first...
		   (all-explanations (cond (existential-explanation (cons existential-explanation path-explanations))
					   (t path-explanations))) )
	     (cond (all-explanations
;		    (km-format t "~a removed as existing explanations for ~a = ~a!~%" all-explanations target val)
		    (km-trace 'comment "[ ~a is already known to be computed from ~a ]" val all-explanations)
		    (cond (target (mapc #'(lambda (explanation)
					    (record-explanation-for target val explanation))			; [3]
					all-explanations)))
		    (multiple-value-bind
		     (unexplained-vals unexplaining-exprs)
		     (remove-explained-vals (rest vals) (remove existential-explanation exprs :test #'equal :count 1) :target target)  ; [4a]
		     (values unexplained-vals (ordered-set-difference unexplaining-exprs path-explanations :test #'equal))))	       ; [4b]
		   (t
		    (multiple-value-bind
		     (unexplained-vals unexplaining-exprs)
		     (remove-explained-vals (rest vals) exprs :target target)
		     (values (cons val unexplained-vals) unexplaining-exprs))))))))
|#
;;; ----------

;;; This implements the eager evaluation of sub-unified expressions.
(defun eagerly-evaluate-exprs (instance &optional (situation (curr-situation)))
  (mapc #'(lambda (slotvals)
	    (let ((slot (slot-in slotvals))
		  (vals (vals-in slotvals)))
	      (cond ((minimatch vals '((?x &&! ?y) &rest))
		     (km-int `#$(the ,SLOT of ,INSTANCE))))))
	(get-slotsvals instance :situation situation)))

;;; ======================================================================
;;;			FORCED UNIFICATIONS
;;; ======================================================================
#|
do-forced-unifications originally combined testing cloned-from/called tags and pending-equalities.
However, I've had to split this into two passes: (i) pending-equalities (ii) cloned-from/called tags.
The reason is as follows: We had a rare case of:
  (do-forced-unifications '(A B) '(X Y))
WHERE tags on A and B each suggests forced unifications with either X or Y, i.e., tags suggested all permutations of forcing.
  BUT there was also a pending equality of (B & X)
The problem with the old code was that, working left to right, A ambiguously is a forced unification with X or Y,
so KM takes the first (A & X), ignoring that there's a later pending equality, (B & X), which contradicts this. So
to fix this we need to make two passes:
  a. DO all the pending equalities
  b. THEN do the tags
|#
(defun do-pending-equalities (set1 exprs2 &key eagerlyp target)
  (cond ((endp set1) (values nil exprs2 nil))
	((null exprs2) (values set1 nil nil))	; PEC 10/21/11 for efficiency of course!
	(t (let* ((val1 (first set1))
		  (matches (remove-if-not #'(lambda (val2)
					      (and (kb-objectp val2)
						   (pending-equality val1 val2)))
					  exprs2))
		  (val2 (first matches)))
	     (cond
	      ((null matches)
	       (multiple-value-bind
		   (reduced-set1 reduced-exprs2 unifications)
		   (do-pending-equalities (rest set1) exprs2 :eagerlyp eagerlyp :target target)
		 (values (cons val1 reduced-set1) reduced-exprs2 unifications)))
;;; NOTE: We don't actually need to do the unification here, as it is already (by definition) pending, so trying it again here will just
;;; trigger the looping detector and it'll automatically exist anyway
	      (t (multiple-value-bind
		     (reduced-set1 reduced-exprs2 unifications)
		     (do-pending-equalities (rest set1) (remove val2 exprs2 :test #'equal) :eagerlyp eagerlyp :target target)
		   (values reduced-set1 reduced-exprs2 (cons val1 unifications)))))))))

#|
Old, copied from do-forced-unifications
	      (t ;;; New: allow continuation if *on-error* = 'continue
    	         (cond ((and (>= (length matches) 2)
			(report-error 'user-error "KB error! There are multiple, different pending equalities ~a <-> ~a trying to unify ~a and ~a!~%" val1 matches set1 exprs2)
  	 	        ;;; If *on-error* = 'continue
			(report-error 'user-error "Will attempt to continue, taking the first value (~a <-> ~a)...~%" val1 val2))))
		    (let ( (unification (cond ((existential-exprp val2)							; UNIFY! Result = val1
					       (unify-with-existential-expr val1 val2
						    :eagerlyp eagerlyp
						    :classes-subsumep t ; NEW: Feb 07 - allow for failure
						    :fail-mode 'fail
						    ; :check-constraintsp nil   ; NEW: commented out Feb 07
						    :target target)) ; allow :fail-mode 'fail so error is caught below
					; otherwise we do unify them
					      (eagerlyp (km-int `(,val1 &+! ,val2) :target target)) ; Route through query interpreter for &!, so pending unifications seen.
					     							    ; Note &+! *is* allowed to quietly fail.
					      (t (lazy-unify val1 val2
						     :eagerlyp eagerlyp
						     :classes-subsumep t ; NEW: Feb 07 - allow for failure
						     :fail-mode 'fail
						     ; :check-constraintsp nil  ; NEW: commented out Feb 07
						     )))) )
		      (cond ((not unification)
			     (multiple-value-bind		; NEW: Feb 07 - allow recovery if failure
				 (reduced-set1 reduced-exprs2 unifications)
				 (do-pending-equalities (rest set1) exprs2 :eagerlyp eagerlyp :target target)
			       (values (cons val1 reduced-set1) reduced-exprs2 unifications)))
			    (t (multiple-value-bind
				   (reduced-set1 reduced-exprs2 unifications)
				   (do-pending-equalities (rest set1) (remove val2 exprs2 :test #'equal) :eagerlyp eagerlyp :target target)
				 (values reduced-set1 reduced-exprs2 (cons val1 unifications))))))))))))
|#
;;; --------------------------------------------------

;;; Experimental patch, leave off for now. If on, the cloned-from tags are also used to align concepts
(defparameter *force-with-cloned-from* nil)

#|
HLO-4470. *force-with-cloned-from* can go wrong as it is too eager: If there are *any* shared tags, it will
force a unification. However the fallback lazy-unify-sets now does a much more sophisticated matching based
on how many tags overlap, looking at all permuatations.

The problematic case was:

Solution
 has-part: Chemical1 Chemical2
 has-solvent: Chemical1
 has-solute: Chemical2

Buffered-Solution
 has-part: Chemical3 Water4
 has-solvent: Water4
 has-solute: Chemical3

Then we do ((Chemical1 Chemical2) && (Chemical3 Water4))
 -> (Chemical1 & Chemical3)  *but*:
	Chemical1 is the SOLVENT in Solution
	Chemical3 is the SOLUTE in Buffered-Solution
     So we end up unifying Solvent and Solute

Looking at the tags we see the form:
   Chemical1: A B C D
   Chemical2: E F G

   Chemical3: E F G H B I J
   Water4: A B C D K L M

Chemical1 is forced with Chemical3 based on the "B" overlap causing it to be a "forced unification",
although clearly counting the overlaps this is completely wrong.

So we will switch this off now, and fall back on lazy-unify-sets which *does* look at maximizing the overlap.
|#
#|
INPUT: set1 set2
RETURNS: three values:
	- shorter set1
	- shorter set2
	- list of items which unified via forcing (through "called" tags)

[1] Remove clone-built-from from tag list, to prevent
 _ProtoChemical1 -> _H2
 _ProtoChemical1 -> _O2
;;; Manually entered:
 (_Reaction1 has
   (raw-material (((_H2) && (_O2)))))
but then we don't want _H2 and _O2 to unify simply because they come from the same clone.
Changed this so only use cloned-from which DON'T include clone-built-from.
ALSO: Changed the unification to require constraint checking AND classes-subsumep (was nil before)
ALSO: We'll add in a check so that the unificiation is allowed to fail and KM will still recover.

[2] More problems, in a similar vein:
(ProtoHusband has (wife (ProtoWife)))
then:
(Husband1 has (wife (Sue [&ed with cloned of ProtoWife])))
(Husband2 has (wife (Mary [&ed with cloned of ProtoWife])))
(Fred has (friends ((Sue) && (Mary))))
We don't want to force Sue and mary to simply because they were cloned from the same clone participant.
It's entirely possible that multiple, different clones of a participant will end up in the same slot.


We deal with this by allowing "forced" unifications to fail, and only gently try and unify them
(with :subsumesp t). Thus the tags are really preference heuristics, and allowed to fail.

This is how it would be done with Skolem functions:
?x:husband -> ?x(wife->_1:woman(?x))

fred(wife->_1(fred))
john(wife->_1(john))
mike(friends->{fred.wife, john.wife})
mike(friends->{_1(fred),_1(john))
|#
;;; Dormant for a year, reinstated
(defun do-forced-unifications (set1 exprs2 &key eagerlyp target)
  (cond ((endp set1) (values nil exprs2 nil))
	((null exprs2) (values set1 nil nil))	; PEC 10/21/11 for efficiency of course!
	((and (not *are-some-tags*)
;	      (not *record-explanations-for-clones*)
	      (or (not *are-some-prototypes*)
		  (not *force-with-cloned-from*)))
	 (values set1 exprs2 nil))	; optimization
	(t (let* ((val1 (first set1))
		  (val1-tags (cond ((kb-objectp val1)
				    (append (cond (*force-with-cloned-from*
						   (ordered-set-difference (get-vals val1 '#$cloned-from) ; [1]
									   (get-vals val1 '#$clone-built-from))))
					    (cond (*called-forces-unification*
						   (append (get-vals val1 '#$called)
							   (get-vals val1 '#$uniquely-called))))))))
		  (matches (or
; NOW done separately in do-pending-equalities phase, see above
;			       (remove-if-not #'(lambda (val2)
;						  (and (kb-objectp val2)
;						       (pending-equality val1 val2)))
;					      exprs2)
			       (remove-if-not #'(lambda (expr)
						  (intersection (tags-in-expr expr :use-cloned-from *force-with-cloned-from*)
								val1-tags :test #'equal))
					      exprs2)
			       ))
		  (val2 (first matches))
		  (val2-tags (cond (val2 (tags-in-expr val2 :use-cloned-from *force-with-cloned-from*)))) )
; 	     (km-format t "val1 = ~a, val1-tags = ~a, matches = ~a, val2 = ~a, val2-tags = ~a~%" val1 val1-tags matches val2 val2-tags)
	     (cond
	      ((null matches)
	       (multiple-value-bind
		   (reduced-set1 reduced-exprs2 unifications)
		   (do-forced-unifications (rest set1) exprs2 :eagerlyp eagerlyp :target target)
		 (values (cons val1 reduced-set1) reduced-exprs2 unifications)))
	      ((not (is-consistent (append val1-tags val2-tags))) ; Note, this is consistency of the TAGS not the VALUES
	       (report-error 'user-error 			  ;       themselves.
			     "Tag inconsistency! ~a and ~a have tags both forcing and disallowing unification!~%       Tag sets were: ~a and ~a~%"
			     val1 val2 val1-tags val2-tags)
	       ;;; Don't do the forced unification in this case if *on-error* = 'continue.
	       (multiple-value-bind
		   (reduced-set1 reduced-exprs2 unifications)
		   (do-forced-unifications (rest set1) exprs2 :eagerlyp eagerlyp :target target)
		 (values (cons val1 reduced-set1) reduced-exprs2 unifications)))
	      (t ;;; New: allow continuation if *on-error* = 'continue
    	         (cond ((and (>= (length matches) 2) 	    ; [2] This is an apparent inconsistency: val1 matches > 1 things
					; BUT: We now allow > 1 matches if ONLY cloned-from tags (i.e., it's ok to have >1 match with cloned-from tags)
			     *called-forces-unification*
			     (let* ((reduced-val1-tags (cond ((kb-objectp val1)
							      (append (get-vals val1 '#$called)
								      (get-vals val1 '#$uniquely-called)))))
				    (reduced-matches (remove-if-not #'(lambda (expr)
								   (intersection (tags-in-expr expr :use-cloned-from nil)
										 reduced-val1-tags :test #'equal))
								    exprs2)))
			       (>= (length reduced-matches) 2)))
			(report-error 'user-error "Tagging error! ~a's tags ~a imply it should unify with multiple, distinct values:~%       ~a!~%"
				  val1 val1-tags matches)
  	 	        ;;; If *on-error* = 'continue
			(report-error 'user-error "Will attempt to continue, taking the first value (~a)...~%"
				      (first matches))))
;		      (cond ((existential-exprp val2)							; UNIFY! Result = val1
;;; No, the is0 test is too expensive!
;			     (cond ((is0 val1 val2)							; val2 subsumes val1, so no unification needed....
;				    (cond ((set-difference val2-tags val1-tags :test #'equal)		; ...except for tranferring the tags.
;					   (cond (target (record-explanation-for target val1 val2)))
;					   (km-int `(,val1 #$has (,'#$called ,val2-tags)) :fail-mode 'error))))
;				   (t (lazy-unify val1 (km-unique-int val2 :fail-mode 'error :target target) :eagerlyp eagerlyp))))		; otherwise we do unify them
; try 2			     (lazy-unify val1 (km-unique-int val2 :fail-mode 'error :target target)
					;					 :eagerlyp eagerlyp :check-constraintsp nil))			; otherwise we do unify them
;		    (km-format t "DEBUG: Forced unification ~a with ~a~%" val1 val2)
		    (let ( (unification (cond ((existential-exprp val2)							; UNIFY! Result = val1
					       (unify-with-existential-expr val1 val2
						    :eagerlyp eagerlyp
						    :classes-subsumep t ; NEW: Feb 07 - allow for failure
						    :fail-mode 'fail
						    ; :check-constraintsp nil   ; NEW: commented out Feb 07
						    :target target)) ; allow :fail-mode 'fail so error is caught below
					; otherwise we do unify them
					      (eagerlyp (km-int `(,val1 &+! ,val2) :target target)) ; Route through query interpreter for &!, so pending unifications seen.
					     							    ; Note &+! *is* allowed to quietly fail.
					      (t (lazy-unify val1 val2
						     :eagerlyp eagerlyp
						     :classes-subsumep t ; NEW: Feb 07 - allow for failure
						     :fail-mode 'fail
						     ; :check-constraintsp nil  ; NEW: commented out Feb 07
						     )))) )
		      (cond ((not unification)

; [2] NEW: We *allow* failure of unification of tagged items, for special cases described above.
; In other words, we now consider tags as preference heuristics (hence the :classes-subsumep t flag above), rather
; than a full forcing of unification.
;			     (report-error 'user-error
;					   "Tagging error! tags ~a (on ~a) and ~a (on ~a) imply (~a & ~a) must be unified, but this unification fails!"
;					   val1-tags val1 val2-tags val2 val1 val2)
			     (multiple-value-bind		; NEW: Feb 07 - allow recovery if failure
				 (reduced-set1 reduced-exprs2 unifications)
				 (do-forced-unifications (rest set1) exprs2 :eagerlyp eagerlyp :target target)
			       (values (cons val1 reduced-set1) reduced-exprs2 unifications)))
			    (t (multiple-value-bind
				   (reduced-set1 reduced-exprs2 unifications)
				   (do-forced-unifications (rest set1) (remove val2 exprs2 :test #'equal) :eagerlyp eagerlyp :target target)
				 (values reduced-set1 reduced-exprs2 (cons val1 unifications))))))))))))

;;; ----------

;;; expr is necessarily an *instance* or an *existential expr*
(defun tags-in-expr (expr &key (use-cloned-from t))
  (cond ((kb-objectp expr) (append (cond (use-cloned-from
					  (ordered-set-difference (get-vals expr '#$cloned-from)
								  (get-vals expr '#$clone-built-from))))
				   (cond (*called-forces-unification*
					  (append (get-vals expr '#$called)
						  (get-vals expr '#$uniquely-called))))))
	(t (let ( (class+slotsvals (breakup-existential-expr expr)) )
	     (cond (class+slotsvals (append (cond (use-cloned-from
						   (ordered-set-difference
						    (vals-in (assoc '#$cloned-from (second class+slotsvals)))
						    (vals-in (assoc '#$clone-built-from (second class+slotsvals))))))
					    (cond (*called-forces-unification*
						   (append
						    (vals-in (assoc '#$called (second class+slotsvals)))
						    (vals-in (assoc '#$uniquely-called (second class+slotsvals)))))))))))))

;;; ======================================================================
;;;		LAZY-UNIFY-SETS
;;; Here KM makes a plausible guess as to which members of the sets should
;;; be coreferential.
;;; Is an ***auxiliary function*** to lazy-unify-expr-sets, not called from
;;; anywhere else in KM.
;;; INPUT: Both sets must be lists of instances. They will already have been dereferenced before this point.
;;; ======================================================================

#|
(lazy-unify-sets set1 set2)
For the members which *will* unify, actually do the unification.
Below does not allow *different* set1s to unify with the *same* set2.
INPUT: Both sets must be lists of instances. They will already have been dereferenced before this point.
RETURNS: ONE value (only), namely a list of unified instances (possibly NIL).
         The ORDER of the unified instances is irrelevant (we reorder them in the calling procedure)
NOTE: This procedure is only used once earlier, which does a reordering. The only assumption in the earlier
      use is that the ordering of any set2 elements which are NOT unified with set1 is preserved. The
      ordering of the unifications does not matter, as they will be reordered again earlier.

[1] need :count 1, so that ((Open) && (Open Open)) = (Open Open), not just (Open)
[2] Need to first remove duplicate, named instances, so that
	((*MyCar) && (_Car2 *MyCar))  = (_Car2 *MyCar), not (*MyCar)
MAR99: Why just named?
	((_Car3) && (_Car2 _Car3))  = (_Car2 _Car3), not (_Car3)
INPUT: The members of the sets must be FULLY EVALUATED - it's an error otherwise.
|#
#|
(defun lazy-unify-sets (set1 set2 &key eagerlyp target)
  (cond
   (*no-heuristic-unification* nil)
   (t ; (km-format t "----------~%(~a && ~a):~%" set1 set2)
      (let* ((shared-elements (ordered-intersection set1 set2))
	     (restset1 (ordered-set-difference set1 shared-elements))
	     (restset2 (ordered-set-difference set2 shared-elements)))
	; (km-format t "1. ~a + (~a && ~a)~%" shared-elements restset1 restset2)
	(multiple-value-bind
	    (unifieds rest2set1 rest2set2)
	    (lazy-unify-sets2 restset1 restset2 :eagerlyp eagerlyp :heuristic 'same-class-and-slots :target target)
	  ; (km-format t "2. ~a + (~a && ~a)~%" unifieds rest2set1 rest2set2)
	  (multiple-value-bind
	      (unifieds2 rest3set1 rest3set2)
	      (lazy-unify-sets2 rest2set1 rest2set2 :eagerlyp eagerlyp :heuristic 'same-class :target target)
	    ; (km-format t "3. ~a + (~a && ~a)~%" unifieds2 rest3set1 rest3set2)
	    (multiple-value-bind
		(unifieds3 rest4set1 rest4set2)
		(lazy-unify-sets2 rest3set1 rest3set2 :eagerlyp eagerlyp :heuristic 'normal :target target)
	      ; (km-format t "4. ~a + (~a && ~a)~%" unifieds3 rest4set1 rest4set2)
	      (let ((all-unifieds (append shared-elements unifieds unifieds2 unifieds3)))
		; (km-format t "RESULT = ~a~%````----------~%" (append all-unifieds rest4set1 rest4set2))
		(append all-unifieds rest4set1 rest4set2)))))))))
|#
;;; ======================================================================

#|
lazy-unify-sets2:
RETURNS: THREE values
 - the unified set12 values
 - the remainder of set1
 - the remainder of set2

[1] HLO-2366 (see hlo2366 example in test-suite/unification.km):
  Prefer unification if SAME immediate classes, so below the 2 Exert-Forces and the 2 ExertForceByEarth unify.
  ((_Exert-Force39_c11 _ExertForceByEarth40_c11) && (_ExertForceByEarth89 _Exert-Force88))

[2] for HLO-2358:
(_Move-It5 has  (object (_Device6 _Device7)))
(_Device6 has   (has-part (_Artifact8)))
(_Device7 has   (material (_Substance9)))

(_Move-It_c1 has  (object (_Device_c3 _Device_c2)))  ; note, reverse order. Want KM to reorder these for unification!
(_Device_c2 has   (has-part (_Artifact_c4)))	     ; Do this by preferring instances with same used slots [3]
(_Device_c3 has   (material (_Substance_c5)))

(_Move-It5 &! _Move-It_c1)

;;; One of these should be null
(print (the has-part of _Device6))
(print (the has-part of _Device7))

[4] Route &! through query interpreter, so we record that the unification is pending
|#
#|
(defun lazy-unify-sets2 (set1 set2 &key eagerlyp heuristic target)
  (cond
   ((or (endp set1) (endp set2))
    (values nil set1 set2))
   (t (let* ((unifier
	      (case heuristic
		(same-class-and-slots
		 (find-if #'(lambda (set2el) ; [2]
			      (and (equal (immediate-classes (first set1)) (immediate-classes set2el))
				   (set-equal (mapcar #'slot-in (get-slotsvals (first set1))) ; [3]
					      (mapcar #'slot-in (get-slotsvals set2el)))
;				   (or (not eagerlyp) (try-lazy-unify (first set1) set2el :classes-subsumep t))
;				   (lazy-unify (first set1) set2el :classes-subsumep t :eagerlyp eagerlyp)))
				   (cond (eagerlyp (cond ((try-lazy-unify (first set1) set2el :classes-subsumep t) ; Test...
							  (km-int `(,(first set1) &! ,set2el) :target target)))) ; then do...[4]
					 (t (lazy-unify (first set1) set2el :classes-subsumep t :fail-mode 'fail)))))  ; Test and do if test succeeds.
			  set2))
		(same-class
		 (find-if #'(lambda (set2el) ; [1]
			      (and (equal (immediate-classes (first set1)) (immediate-classes set2el))
;				   (or (not eagerlyp) (try-lazy-unify (first set1) set2el :classes-subsumep t))
;				   (lazy-unify (first set1) set2el :classes-subsumep t :eagerlyp eagerlyp))
				   (cond (eagerlyp (cond ((try-lazy-unify (first set1) set2el :classes-subsumep t) ; Test...
							  (km-int `(,(first set1) &! ,set2el) :target target)))) ; then do...[4]
					 (t (lazy-unify (first set1) set2el :classes-subsumep t :fail-mode 'fail))))) ; Test and do if test succeeds.
			  set2))
		(normal
		 (find-if #'(lambda (set2el)
;			      (and (or (not eagerlyp) (try-lazy-unify (first set1) set2el :classes-subsumep t))
;				   (lazy-unify (first set1) set2el :classes-subsumep t :eagerlyp eagerlyp))
			      (cond (eagerlyp (cond ((try-lazy-unify (first set1) set2el :classes-subsumep t) ; Test...
						     (km-int `(,(first set1) &! ,set2el) :target target)))) ; then do...[4]
				    (t (lazy-unify (first set1) set2el :classes-subsumep t :fail-mode 'fail)))) ; Test and do if test succeeds.
			  set2)))))
					; back to original code...
	     (cond ((and unifier eagerlyp) (simple-eval-instance unifier)))	; [4]
	     (cond (unifier
		    (multiple-value-bind
			(unifieds restset1 restset2)
			(lazy-unify-sets2 (rest set1)
					 (remove unifier set2 :count 1)
					 :eagerlyp eagerlyp :heuristic heuristic :target target) ; [1]
		      (values (cons unifier unifieds) restset1 restset2)))
		   (t (multiple-value-bind
			  (unifieds restset1 restset2)
			  (lazy-unify-sets2 (rest set1) set2
					   :eagerlyp eagerlyp :heuristic heuristic :target target)
			(values unifieds (cons (first set1) restset1) restset2))))))))

|#

;;; set1 and set2 necessarily don't have shared elements (they'll have been removed earlier)
(defun lazy-unify-sets (set1 set2 &key eagerlyp target)
  (cond
   ((null set1) nil)
   ((null set2) nil)
   (*no-heuristic-unification* nil)
   (t (let* ((all-pairs (permute (list set1 set2))) ;(permute '((a b c) (d e)))->((a d) (a e) (b d) (b e) (c d) (c e))
	     (cloned-from-sources
	      (cond (*are-some-prototypes*
		     (remove nil (mapcar #'(lambda (i)
					     (cond ((anonymous-instancep i) (list i (cloned-from* i)))))
					 (append set1 set2))))))
	     (scored-pairs
	      (cond ((singletonp all-pairs) `((,@(first all-pairs) 0)))
		    (t (mapcar #'(lambda (pair)
				   `(,@pair ,(rank-unification (first pair) (second pair) :cloned-from-sources cloned-from-sources)))
			       all-pairs))))
	     (ordered-scored-pairs (sort scored-pairs #'> :key #'third)))
; Debug only
;	(let* ((gathered (gathers-by-key ordered-scored-pairs))
;	       (ambiguous-bindings (remove-if #'(lambda (x) (singletonp (second x))) gathered)))
;	  (cond (ambiguous-bindings
;		 (show-goal-stack)
;		 (km-format t "Ambiguous bindings for ~a:~%" target)
;		 (mapc #'(lambda (x) (km-format t "   ~a -> ~a~%" (first x) (second x))) ambiguous-bindings)
;		 (mapc #'showme (mapcar #'first ambiguous-bindings))
;		 (mapc #'showme (remove-duplicates (remove-if-not #'anonymous-instancep (flatten (mapcar #'second ambiguous-bindings)))))
;		 (break)
;		 )))
;	(km-format t "ordered-scored-pairs = ~a~%" ordered-scored-pairs)
	(lazy-unify-sets2 ordered-scored-pairs set1 set2 :eagerlyp eagerlyp :target target)))))

;;; List of (<i1> <i2> <score>)
(defun lazy-unify-sets2 (ordered-scored-pairs set1 set2 &key eagerlyp target)
  (cond
   ((endp ordered-scored-pairs) nil)
   (t (multiple-value-bind
	  (best-pair rest-ordered-scored-pairs)
	  (best-pair ordered-scored-pairs)
	(let* ((v1 (first  best-pair))
	       (v2 (second best-pair)))
	(cond
	 ((and (member v1 set1)		; not already done
	       (member v2 set2)
	       (cond (eagerlyp (cond ((try-lazy-unify v1 v2 :classes-subsumep t)  ; try
				      (km-int `(,v1 &! ,v2) :target target)))) ; then do...[4]
		     (t (lazy-unify v1 v2 :classes-subsumep t :fail-mode 'fail)))) ; Test and do if test succeeds.
	  `(,v1  ; the unified result
	    ,@(lazy-unify-sets2 rest-ordered-scored-pairs (remove v1 set1) (remove v2 set2) :eagerlyp eagerlyp :target target)))
	 (t (lazy-unify-sets2 rest-ordered-scored-pairs set1 set2 :eagerlyp eagerlyp :target target))))))))

#|
HLO-4721:
KM> (a Second-Electron-Shell)
(_Second-Electron-Shell47498)

KM> (the has-region of _Second-Electron-Shell47498)
... -> constraint violation with KB v1067-rec

	Second-Electron-Shell.km                         Electron-Shell.km
          Electron[1]	Electron[2]		  	    Electron
 	   |    ^          ^ |                     	    |^
  	   v     \has-part/ v is-inside           is-inside |  \ has-part
         2nd-Orb    Atom    2nd-Orb                    Orbital   Atom
	   |    /has-region\ |  is-region-of    is-region-of|   / has-region
	   v   v            vv                              v v
           2ndES            1stES                           EShell

Unify 2ndES &! EShell
  -> Atom &! Atom
   -> (Electron[1] Electron[2]) &&! (Electron)
The problem is now getting the pairing correct. The only way we can bias to the correct answer (Electron[1])
is via no-of-pending-unifications that looks ahead and sees Electron[1] -> 2nd-Orb -> 2ndES is a pending unification with Electron -> Orbital -> EShell, so prefer it.
|#
;;; Returns an integer
(defun rank-unification (i1 i2 &key cloned-from-sources)
  (let ((n-overlap
	 (cond (cloned-from-sources
		(length (intersection (second (assoc i1 cloned-from-sources))
				      (second (assoc i2 cloned-from-sources)))))
	       (t 0))))
    (+ n-overlap
       (cond ((set-equal (immediate-classes i1) (immediate-classes i2))
	      (cond ((set-equal (mapcar #'slot-in (get-slotsvals i1)) ; [3]
				(mapcar #'slot-in (get-slotsvals i2)))  100)
		    (t 50)))
	     (t 0))
       (* 2 (no-of-pending-equalities i1 i2)) ; this is horribly heuristic but allows us a small bias towards pending equalities
       )))

;;; Originally, we just picked the first element in ordered-scored-pairs.
;;; But HLO-4721 we can still get a tie. In this case, we use a tie-breaker based on the unification with more pending equalities
;;; 	This is basically the only thing which distinguishes the otherwise tied case in HLO-4721
;;; List of (<i1> <i2> <score>)
(defun best-pair (ordered-scored-pairs)
  (cond
   (ordered-scored-pairs
    (let* ((best-rank (third (first ordered-scored-pairs)))
	   (best-pairs (pairs-with-rank ordered-scored-pairs best-rank))
	   (best-pair (cond ((singletonp best-pairs) (first best-pairs))
;			    ((notevery #'(lambda (pair) 			; only try no-of-pending-equalities if all pairs are kb objects
;					   (and (kb-objectp (first pair))
;						(kb-objectp (second pair))))
;				       best-pairs)
;			     (first best-pairs))
			    ((null best-pairs)
			     (format t "ERROR! null best-pairs in best-pair! Continuing...~%")	; should never happen
			     (first ordered-scored-pairs))
			    (t (first (sort (copy-tree best-pairs) #'> :key #'(lambda (pair)
										(no-of-pending-equalities (first pair) (second pair))))))))
	   (rest-pairs (remove best-pair ordered-scored-pairs :test #'equal)))
      (values best-pair rest-pairs)))))

; (pairs-with-rank '((a b 3) (c d 3) (e f 2)) 3) -> ((A B 3) (C D 3))
(defun pairs-with-rank (pairs rank)
  (cond
   ((null pairs) nil)
   ((null rank) (format t "ERROR! Null rank to pairs with rank!~%"))
   ((= (third (first pairs)) rank)
    (cons (first pairs) (pairs-with-rank (rest pairs) rank)))))

;;; ----------------------------------------------------------------------
;;;	Count the pending equalities - this is the tie-breaker if the rank-unification is tied
;;; ----------------------------------------------------------------------

;;; either one of x and y's slotvals are a pending-equality, or one the slotsvals of x and y's slotsvals are a pending-equality (i.e., look two-deep)
(defun no-of-pending-equalities (x y)
  (cond
   ((and (kb-objectp x)
	 (kb-objectp y))
    (let* ((level1 (no-of-pending-equalities-between-slotsvals x y))
	   (level2s (let ((x-slotsvals (get-slotsvals x :situation *global-situation*))
			(y-slotsvals (get-slotsvals y :situation *global-situation*)))
		    (mapcan #'(lambda (x-slotvals)
				(let* ((x-slot (slot-in x-slotvals))
				       (x-vals (vals-in x-slotvals))
				       (y-slotvals (assoc x-slot y-slotsvals))
				       (y-vals (vals-in y-slotvals)))
				  (cond
				   ((and (not (member x-slot *neq-slots*))
					 (not (member x-slot *slots-with-nonparticipant-skolems*))
					 (not (member x-slot *unclonable-slots*))
					 (not (member x-slot '#$(instance-of)))
					 (<= (length x-vals) 2)
					 (<= (length y-vals) 2)) ; for efficiency
				    (mapcan #'(lambda (x-val)
					    (mapcar #'(lambda (y-val)
						      (no-of-pending-equalities-between-slotsvals x-val y-val))
						    y-vals))
					x-vals)))))
			  x-slotsvals)))
	(level2 (apply #'+ level2s)))
;      (+ (* 1000 level1) level2)))
      (+ (* 2 level1) level2)))
   (t 0)))

;;; Somehow, mapcan causes this to go into an infinite loop :-(
(defun no-of-pending-equalities-between-slotsvals (x y)
  (cond
   ((and (kb-objectp x)
	 (kb-objectp y))
    (let ((x-slotsvals (get-slotsvals x :situation *global-situation*))
	  (y-slotsvals (get-slotsvals y :situation *global-situation*)))
    (apply #'+
      (my-mapcan #'(lambda (x-slotvals)
		 (let* ((x-slot (slot-in x-slotvals))
			(x-vals (vals-in x-slotvals))
			(y-slotvals (assoc x-slot y-slotsvals))
			(y-vals (vals-in y-slotvals)))
		   (cond ((and (not (member x-slot *neq-slots*))
			       (not (member x-slot *slots-with-nonparticipant-skolems*))
			       (not (member x-slot *unclonable-slots*))
			       (not (member x-slot '#$(instance-of)))
			       (<= (length x-vals) 2)
			       (<= (length y-vals) 2))		; for efficiency
			  (my-mapcan #'(lambda (x-val)
			       (my-mapcan #'(lambda (y-val)
					   (cond ((and (kb-objectp x-val)
						       (kb-objectp y-val)
						       (pending-equality x-val y-val))
;						  (km-format t "((~a ~a ~a) &! (~a ~a ~a)) pending~%"
;							     x x-slot x-val y x-slot y-val)
						  '(1))))
				       y-vals))
				  x-vals)))))
		 x-slotsvals))))
   (t 0)))

;;; ======================================================================
;;;	MACHINERY FOR REMOVING DUPLICATES WHEN &'ing TOGETHER STUFF
;;; ======================================================================

#|
and-append:
 - Takes two *sets* of values. For &, those sets will necessarily be singletons.
 - Returns a *set* containing a *single* value, = the unification of those
	two sets (either using & or && as specified in the call).

This simple task ends up being surprisingly tricky to implement correctly...

;;; without duplicates
(and-append '(a) '& '(b)) 		;-> ((a & b))
(and-append '(a) '& '((b & c))) 	;-> ((a & b & c))
(and-append '((a & b)) '& '((c & d))) 	;-> ((a & b & c & d))

;;; with duplicates
(and-append '(a) '& '((b & a))) 	;-> ((b & a))
(and-append '((b & a)) '& '(a)) 	;-> ((b & a))
(and-append '((a & b)) '& '((c & a))) 	;-> (( b & c & a))

The critical property is that repeated and'ing doesn't make the list grow indefinitely:
(and-append '(a) '& '(b))		;-> ((a & b))
(and-append '((a & b)) '& '(b))		;-> ((a & b))
(and-append '(a b) '&& '(c d))		;-> (((a b) && (c d)))
(and-append '(((a b) && (c d))) '&& '(c d)) ;-> (((a b) && (c d)))

Inputs get converted to call and-append2 as follows:
(((a b) && (c d)))      (((a b) && (e f))) [1a] -> ((a b) && (c d))     ((a b) && (e f))
((a & b))		((a & c))	   [1b] -> (a & b)		(a & c)
(((a b) && (c d)))      (a b)		   [2a] -> ((a b) && (c d))     ((a b))
((a & b))		(a)		   [2b] -> (a & b)		(a)
(a b)			(c d)		   [3a] -> returns  ((a b) && (c d))
(a)			(c)		   [3b] -> returns  (a & b)
|#
(defun and-append (xs0 and-symbol ys0)
  (let ( (xs (remove-dup-atomic-instances xs0))
	 (ys (remove-dup-atomic-instances ys0)) )
  (cond ((equal xs ys) xs)
	((and (singletonp xs) 			; (((a b) && (c d)))    (((a b) && (e f))) [1a]
	      (and-listp (first xs) and-symbol) ; ((a & b))		((a & c))	   [1b]
	      (singletonp ys)
	      (and-listp (first ys) and-symbol))
	 (list (and-append2 (first xs) and-symbol (first ys))))
	((and (singletonp xs) 			; (((a b) && (c d)))    (a b)		   [2a]
	      (and-listp (first xs) and-symbol)) ; ((a & b))		(a)		   [2b]
	 (list (and-append2 (first xs) and-symbol (do-setify ys and-symbol))))
	((and (singletonp ys) 			; (a b)			(((a b) && (c d))) [2a]
	      (and-listp (first ys) and-symbol)) ; (a)			((a & b))	   [2b]
	 (list (and-append2 (do-setify xs and-symbol) and-symbol (first ys))))
	((set-unification-operator and-symbol)	; (a b)			(c d)		   [3a]
	 (list (list xs and-symbol ys)))
	((val-unification-operator and-symbol)	; (a)			(c)		   [3b]
	 (list (list (first xs) and-symbol (first ys))))
	(t (report-error 'user-error "Unknown case for (ands-append ~a ~a ~a)!~%" xs and-symbol ys)))))

(defun do-setify (set and-symbol)
  (cond ((set-unification-operator and-symbol) (list set))
	(t set)))

;;; Here x and y are lists of conjoined values. Note how non-and-lists have been ()'ed
;;; (and-append2 '(a)   '& '(a & b))
;;; (and-append2 '((a)) '&& '((a) && (b)))
;;; eg. (and-(a & b),  or (a)  but not  a
(defun and-append2 (x and-symbol y)
  (cond ((null x) y)					; termination
	((and (not (singletonp x))
	      (not (and (> (length x) 2)
			(eq (second x) and-symbol))))
	 (report-error 'program-error "and-append2 given a badly formed list (not an and-list!)~%Doing (and-append2 ~a ~a ~a)~%" x and-symbol y))
	((and-member (first x) y and-symbol)
	 (and-append2 (rest (rest x)) and-symbol y))
	(t (cons (first x)
		 (cons and-symbol
		       (and-append2 (rest (rest x)) and-symbol y))))))

; (and-listp '(a & b) '&)  -->   t
; (and-listp '((a) && (b)) '&&)  -->   t
(defun and-listp (list and-symbol)
  (and (listp list)
       (> (length list) 2)
       (eq (second list) and-symbol)))

(defun and-member (el list and-symbol)
  (cond ((equal el (first list)))
	((singletonp list) nil)
	((and (> (length list) 2)
	      (eq (second list) and-symbol))
	 (and-member el (rest (rest list)) and-symbol))
	(t (report-error 'program-error
			 "and-member given a badly formed list (not an and-list!)~%Doing (and-member ~a ~a ~a)~%" el list and-symbol))))

;;; ======================================================================
;;;		UNIFYING SITUATIONS
;;; ======================================================================
#|
An extra step is required besides unifying the frames themselves, namely unifying
their situational contents.
|#
;;; source and target are instances
(defun copy-situation-contents (source-sitn target-sitn)
  (cond ((eq source-sitn target-sitn))
	((not (isa source-sitn '#$Situation)))
	((not (kb-objectp target-sitn))
	 (report-error 'user-error "Can't copy ~a's contents to target situation ~a, as ~a isn't a KB object!~%"
		       source-sitn target-sitn target-sitn))
	(t (let ( (curr-situation (curr-situation))
		  (objects-to-copy (remove-if-not #'(lambda (instance)
						      (has-situation-specific-info instance source-sitn))
						  (get-all-concepts))) )
;	     (km-format t "Changing to the target-sitn = ~a...~%" target-sitn)
	     (in-situation target-sitn)			; Change to target...
	     (mapc #'(lambda (instance)
		       (merge-slotsvals instance source-sitn target-sitn :facet 'own-properties)
		       (merge-slotsvals instance source-sitn target-sitn :facet 'member-properties))
		   objects-to-copy)
	     (mapc #'un-done objects-to-copy)	; - now in put-slotsvals via merge-slotsvals; Later: No!
	     (mapc #'classify objects-to-copy)
;	     (km-format t "Changing back the curr-sitn = ~a...~%" curr-situation)
	     (in-situation curr-situation)))))		; Change back...

;;; ----------

;;; (No result passed back)
;;; [1] The inverses will be installed anyway when the other frames in the situation are merged.
;;; [2] here we just merge the *structures*, which is why i1 and i2 are nil
(defun merge-slotsvals (instance source-sitn target-sitn &key classes-subsumep (facet 'own-properties))
  (let ( (source-svs (get-slotsvals instance :facet facet :situation source-sitn))
	 (target-svs (get-slotsvals instance :facet facet :situation target-sitn)) )
    (cond
     (source-svs
      (multiple-value-bind
       (successp unified-svs)
       (lazy-unify-slotsvals nil nil source-svs target-svs 			; [2]
			     :cs1 (immediate-classes instance :situation source-sitn)
			     :cs2 (immediate-classes instance :situation target-sitn)
			     :classes-subsumep classes-subsumep
			     :check-constraintsp nil
			     :fail-mode 'error)
       (cond (successp
	      (cond ((not (equal unified-svs target-svs))
		     (put-slotsvals instance unified-svs :facet facet :situation target-sitn :install-inversesp nil))))	; install-inversesp = nil [1]
	     (t (report-error 'user-error
			      "Failed to unify ~a's slot-values of ~a in ~a~%with its slot-values ~a in ~a!~%Dropping these values...~%"
			      instance source-svs source-sitn target-svs target-sitn))))))))

;;; ======================================================================
;;;		UNIFIABLE-WITH-EXPR
;;; ======================================================================

;;; 5.3.00 remove this, replace with &? as it ignores constraints attached to class.

#|
unifiable-with-existential-expr: This is like the &? operator, except its second argument is
an expression rather than an instance. It uses the same comparison machinery
(lazy-unify-slotsvals) as &?, except enters it a bit lower down (lazy-unify-slotsvals,
rather than try-lazy-unify), and without actually creating a temporary Skolem
instance denoting expr.

Unifiable - eventually should merge with subsumes.
EXPR = necessarily '(a Class with slotsvals)), for now
[1] Technically, we unify in *every* situation, but of course the existential-expr is invisible in other situations*** so we'd just
    be unifying instance with nil for all other situations = redundant.
    9/8/00 *** - no! It's also visible in all subsituations of the current situation and so should check them too!
[2] Merging an instance with a structure, so i2 = NIL
[3] for multiple classes in expr, e.g., (a Car with (instance-of (Expensive-Thing)) (...)):
		classes -> (Car Expensive-Thing)
		slotsvals ->  ((instance-of (Car Expensive-Thing)) ... 	, for constraint-checking by lazy-unify-slotsvals
[4] Optimization: (_Agent3 & (a Agent)) shouldn't test all the constraints on _Agent3's slots!
[5] Let's *try* and allow people to put expressions on instance-of slots
[7] Michael Wessel only wants to check locked classes for heuristic unification (when :classes-subsumep t), not for forced unification.
|#
(defun unifiable-with-existential-expr (instance expr &key classes-subsumep)
 (cond
  ((explained-by instance expr)
   (km-trace 'comment "[ ~a was originally derived from ~a, so must unify with it! ]" instance expr)
   instance)
  (t
   (let ( (class+slotsvals (bind-self (breakup-existential-expr expr) instance)) )   ; [1]
    (cond (class+slotsvals				;;; 1. An INDEFINITE expression
	   (let* ( (class (first class+slotsvals))		;;;    (so do subsumption)
		   (slotsvals0 (second class+slotsvals))
		   (classes (remove-duplicates (cons class (vals-in (assoc '#$instance-of slotsvals0)))))  ; [3]
		   (slotsvals (update-assoc-list slotsvals0 `(#$instance-of ,classes))) )		   ; [3]
	     (are-slotsvals slotsvals)						; inc. look for constraints in slots
	     (cond
	      ((and (null slotsvals)
		    (isa instance class)) instance)	; [4]
	      ((and ;(can-be-a instance class)
		(compatible-classes :instance1 instance :classes2 (remove-constraints classes)	; incomplete [no constraint checking] lookahead
				    :classes-subsumep classes-subsumep :check-locked-classes-p classes-subsumep) ; [7]
		(cond ((am-in-local-situation-or-theory)
			(let ( ; (local (remove-if-not #'(lambda (slotvals)
			       ;			 (fluentp (slot-in slotvals))) slotsvals))
			       (global (remove-if #'(lambda (slotvals)
						      (fluentp (slot-in slotvals))) slotsvals))
			       (curr-situation (curr-situation)) )
			  (and (lazy-unify-slotsvals instance nil (get-slotsvals instance) slotsvals	; was "local", not "slotsvals" [1]***
;						     :cs2 (remove-constraints classes)
						     :cs2 (remove-if-not #'kb-objectp classes)   ; [5]
						     :classes-subsumep classes-subsumep :fail-mode 'fail)
			       (prog2
				   (change-to-situation *global-situation*)
				   (lazy-unify-slotsvals instance nil (get-slotsvals instance) global
;						     :cs2 (remove-constraints classes)
						     :cs2 (remove-if-not #'kb-objectp classes)   ; [5]
						     :classes-subsumep classes-subsumep :fail-mode 'fail)
				 (change-to-situation curr-situation)))))
		      (t (lazy-unify-slotsvals instance nil (get-slotsvals instance) slotsvals
;					       :cs2 (remove-constraints classes)
					       :cs2 (remove-if-not #'kb-objectp classes)   ; [5]
					       :classes-subsumep classes-subsumep :fail-mode 'fail))))))))	; only unify in curr sitn [1], [2]
	  (t (report-error 'program-error "unifiable-with-existential-expr() in lazy-unify.lisp wasn't given an existential expr!~%   (was ~a instead)~%"
			   expr)))))))

;;; This unifies instance with an existential expr *without* creating then subsequently deleting a Skolem
;;; constant for that existential expr. It's rather a lot of code just to save extra instance creation,
;;; but useful for must-be-a constraints.
;;; IF successful returns INSTANCE, if not returns NIL. [Note: Failure is allowed]
;;; [1] creation routine is largely copied from create-named-instance in frame-io.lisp
;;; [2] this subsumption test is new, from remove-subsuming-exprs. It avoids creating
;;;     unnecessary structures e.g. if (Pete has (owns (_Car0))) then:
;;;		(unify-with-existential-expr Pete '#$(a Person with (owns ((a Car)))))
;;;	would otherwise have resulted in (Pete has (owns (((_Car0) && ((a Car)))))).
;;; [2b]    PC  - beta48 - so why is that a problem? You just defer resolving the && until later!
;;; [3] Merging an instance with a structure, so i2 = NIL
;;; NOTE: This unification is *only* done in the local situation.
;;; [4] Optimization: (_Agent3 & (a Agent)) shouldn't test all the constraints on _Agent3's slots!
;;; [5] Let's *try* and allow people to put expressions on instance-of slots
;;; [6] (u-w-e-e '#$_Fish1 '#$(a Pet (@ _Person3 Person owns)) - don't want to lose explanation for _Fish1 instance-of Pet
;;; [7] Michael Wessel only wants to check locked classes for heuristic unification (when :classes-subsumep t), not for forced unification.
(defun unify-with-existential-expr (instance expr
				    &key eagerlyp classes-subsumep (fail-mode 'fail) target (check-constraintsp t))
  (cond
   ((explained-by instance expr target)
    (km-trace 'comment "[ ~a was originally derived from ~a, so must unify with it! ]" instance expr)
    instance)
   ((and (fluent-instancep instance)			; special case: (_SomePerson23 & (a Person)) -> _Person35, a definite object
	 (neq (first expr) '#$some))
    (let ((val (km-unique-int expr :target target))
	  (joiner (cond ((and eagerlyp classes-subsumep) '&+!)
			(eagerlyp '&!) (classes-subsumep '&+) (t '&))))
      (km-unique-int `(,instance ,joiner ,val) :fail-mode fail-mode)))
;  ((km-int `#$(,INSTANCE is ',EXPR)) instance))   	; [2], [2b]
   (t (let ( (class+slotsvals (bind-self (breakup-existential-expr expr) instance)) )   ; [1]
	(cond
	 (class+slotsvals				;;; 1. An INDEFINITE expression
	  (let* ((class (first class+slotsvals))		;;;    (so do subsumption)
		 (slotsvals0 (second class+slotsvals))
		 (_dummy (are-slotsvals slotsvals0)) ; inc. look for constraints in slots
		 (extra-classes (vals-in (assoc '#$instance-of slotsvals0))) ; [1]
		 (all-new-classes (cons class extra-classes))
		 (unification
		    (cond
		       ((and (null slotsvals0)			      ; [4] - optional optimization (in practice doesn't
			     (isa instance class)		      ; make much difference)
			     (remove-subsumers-slotp '#$instance-of)) ; NOTE: Otherwise instance-of assertions *do* need
								      ; updating in the KB.
			instance)
		       (t (multiple-value-bind
			      (compatiblep violated-partitions locked-violations)
			      (compatible-classes :instance1 instance :classes2 (list class) ; incomplete [no constraint checking], quick lookahead
						  :classes-subsumep classes-subsumep :check-locked-classes-p classes-subsumep) ; [7]
			    (cond
			     (compatiblep
			      (cond ((not (kb-objectp instance)) instance) ; e.g. (1 & (a Coordinate))
				    (t (or (unify-with-slotsvals2 instance all-new-classes
								  slotsvals0 :classes-subsumep classes-subsumep
								  :eagerlyp eagerlyp :check-constraintsp check-constraintsp :fail-mode fail-mode)
					   (cond ((eq fail-mode 'error)
						  (report-error 'user-error
								"Unification (~a ~a ~a) failed! (Some slot-values are incompatible)~%"
								instance
								(cond ((and eagerlyp classes-subsumep) '&+!)
								      (eagerlyp '&!) (classes-subsumep '&+) (t '&))
								expr)
						  nil))))))
			     ((eq fail-mode 'error)
			      (cond
			       (violated-partitions
				(report-error 'user-error "Unification (~a ~a ~a) failed! The classes were found to be incompatible.~%Partition(s) ~a was violated:~%~{~a~}"
					      instance
					      (cond ((and eagerlyp classes-subsumep) '&+!)
						    (eagerlyp '&!) (classes-subsumep '&+) (t '&))
					      expr
					      (delistify violated-partitions)
					      (mapcar #'write-frame violated-partitions)))
			       (locked-violations
				(report-error 'user-error "Unification (~a ~a ~a) failed! The unification would replace the locked class ~a with ~a. (not allowed!)~%"
					      instance
					      (cond ((and eagerlyp classes-subsumep) '&+!)
						    (eagerlyp '&!) (classes-subsumep '&+) (t '&))
					      expr
					      (first locked-violations)
					      (second locked-violations)))
			       (t (report-error 'user-error "Unification (~a ~a ~a) failed! The classes were found to be incompatible.~%"
					      instance
					      (cond ((and eagerlyp classes-subsumep) '&+!)
						    (eagerlyp '&!) (classes-subsumep '&+) (t '&))
					      expr))))))))))
	    (declare (ignore _dummy))
;	    (km-format t "DEBUG: ~a~%" `(record-explanation-for ,target ,instance ,expr))
	    (cond (unification (cond (target (record-explanation-for target instance expr)))
			       (cond ((kb-objectp instance)
				      (mapc #'(lambda (new-class) ; [6]
  					        (record-explanation-for `#$(the instance-of of ,INSTANCE) new-class expr))
					    all-new-classes)))
			       (cache-explanation-for instance expr)		; new - missed this first time round
			       (setq *statistics-unifications* (1+ *statistics-unifications*))
			       unification))))
; No, error reporting done earlier now
;		  ((eq fail-mode 'error)
;		   (report-error 'user-error "Unification (~a ~a ~a) failed! (Some slot-values are incompatible)~%"
;				 instance
;				 (cond ((and eagerlyp classes-subsumep) '&+!)
;				       (eagerlyp '&!) (classes-subsumep '&+) (t '&))
;				 expr))
	 (t (report-error 'program-error "unify-with-existential-expr() in lazy-unify.lisp wasn't given an existential expr!~%   (was ~a instead)~%"
			  expr)))))))

(defun unify-with-slotsvals2 (instance classes slotsvals00
			      &key classes-subsumep eagerlyp (check-constraintsp t) (fail-mode 'fail))
 (let ((slotsvals (convert-comments-to-internal-form slotsvals00)))   ; new!
  (cond
   ((am-in-local-situation-or-theory)
    (let* ( (local0 (remove-if-not #'(lambda (slotvals) (fluentp (slot-in slotvals))) slotsvals))
	    (global0 (remove-if #'(lambda (slotvals) (fluentp (slot-in slotvals))) slotsvals))
	    (local (cond ((fluentp '#$instance-of)
			  (update-assoc-list local0 `#$(instance-of ,CLASSES)))
			 (t local0)))
	    (global (cond ((not (fluentp '#$instance-of))
			   (update-assoc-list global0 `#$(instance-of ,CLASSES)))
			  (t global0)))
	    (curr-situation (curr-situation)) )
      (multiple-value-bind
       (successp1 unified-svs1)
       (lazy-unify-slotsvals instance nil (get-slotsvals instance) local
;			     :cs2 (remove-constraints classes)
			     :cs2 (remove-if-not #'kb-objectp classes)   ; [5]
			     :classes-subsumep classes-subsumep ; [3]
			     :eagerlyp eagerlyp
			     :check-constraintsp check-constraintsp
			     :fail-mode fail-mode)
       (cond
	(successp1
	 (change-to-situation *global-situation*)
	 (multiple-value-bind
	  (successp2 unified-svs2)
	  (lazy-unify-slotsvals instance nil (get-slotsvals instance) global
;				:cs2 (remove-constraints classes)
				:cs2 (remove-if-not #'kb-objectp classes)   ; [5]
				:classes-subsumep classes-subsumep ; [3]
				:eagerlyp eagerlyp
				:check-constraintsp check-constraintsp
				:fail-mode fail-mode)
	 (cond
	  ((and successp1 successp2)
	   (let ( (local-change-made nil)
		  (global-change-made nil) )
	    (cond ((not (equal unified-svs2 (get-slotsvals instance)))			; GLOBAL SITUATION
		   (cond ((not global-change-made)
;			  (km-format t "unified-svs2 = ~a~%" unified-svs2)
;			  (km-format t "(get-slotsvals ~a) = ~a~%" instance (get-slotsvals instance))
			  (setq global-change-made t)))
;		   (km-format t "tracepoint 1: ~a~%" unified-svs2)
		   (mapc #'(lambda (slotvals) (put-vals instance (slot-in slotvals)
							(vals-in slotvals))) unified-svs2) ; [1]
		   (cond ((some #'(lambda (class) (is-subclass-of class '#$Situation)) classes)
			  (make-assertions instance unified-svs2)))))
	    (change-to-situation curr-situation)
	    (cond ((not (equal unified-svs1 (get-slotsvals instance)))			; LOCAL SITUATION
		   (cond ((not local-change-made)
;			  (km-format t "unified-svs1 = ~a~%" unified-svs1)
;			  (km-format t "(get-slotsvals ~a) = ~a~%" instance (get-slotsvals instance))
			  (setq local-change-made t)))
;		   (km-format t "tracepoint 2: ~a~%" unified-svs1)
		   (mapc #'(lambda (slotvals) (put-vals instance (slot-in slotvals)
							(vals-in slotvals))) unified-svs1) ; [1]
		   (cond ((some #'(lambda (class) (is-subclass-of class '#$Situation)) classes)
			  (make-assertions instance unified-svs1)))))
;	    (un-done instance)
; It looks like slotsvals are adequate, but no:
; i1 & (a Move with (object (...))) may, as a side effect, include OTHER changes on OTHER slots on i1 too,
; inherited from Move or its superclasses. So we better undo all of these!
;	    (mapc #'(lambda (slot) (un-done instance :slot slot :situation (curr-situation))) (mapcar #'slot-in slotsvals))
	    (cond (local-change-made
		   (mapc #'(lambda (slot) (un-done instance :slot slot :situation (curr-situation))) (mapcar #'slot-in unified-svs1))))
	    (cond (global-change-made
		   (mapc #'(lambda (slot) (un-done instance :slot slot :situation *global-situation*)) (mapcar #'slot-in unified-svs2))))
	    (cond ((or local-change-made global-change-made)
		   (classify instance))))

; OLD VERSION
;	    (cond (change-made
;		   (mapc #'(lambda (slot) (un-done instance :slot slot :situation (curr-situation))) (mapcar #'slot-in unified-svs1))
;		   (classify instance))))

	   instance)
	  (t (change-to-situation curr-situation) nil))))))))	; oops! Must change back again even after failure!
   (t (multiple-value-bind
       (successp unified-svs)
       (lazy-unify-slotsvals instance nil (get-slotsvals instance)
			     (update-assoc-list slotsvals `#$(instance-of ,CLASSES))
;			     :cs2 (remove-constraints classes)
			     :cs2 (remove-if-not #'kb-objectp classes)   ; [5]
			     :classes-subsumep classes-subsumep ; [3]
			     :eagerlyp eagerlyp
			     :check-constraintsp check-constraintsp
			     :fail-mode fail-mode)
      (cond (successp
	     (let ( (change-made nil) )
	      (cond ((not (equal unified-svs (get-slotsvals instance)))
		     (mapc #'(lambda (slotvals)
			       (cond ((not change-made)
;				      (km-format t "unified-svs = ~a~%" unified-svs)
;				      (km-format t "(get-slotsvals ~a) = ~a~%" instance (get-slotsvals instance))
				      (setq change-made t)))
					;			       (km-format t "tracepoint 3: ~a~%" slotvals)
			       (put-vals instance (slot-in slotvals) (vals-in slotvals)))
			   unified-svs)	; [1]
		     (cond ((some #'(lambda (class) (is-subclass-of class '#$Situation)) classes)
			    (make-assertions instance unified-svs)))
;		     (un-done instance)
; It looks like slotsvals are adequate, but no:
; i1 & (a Move with (object (...))) may, as a side effect, include OTHER changes on OTHER slots on i1 too,
; inherited from Move or its superclasses. So we better undo all of these!
		     (cond (change-made
			    (mapc #'(lambda (slot) (un-done instance :slot slot :situation (curr-situation))) (mapcar #'slot-in unified-svs))
			    (classify instance)))
		     )))
	     instance)))))))

;;; ======================================================================

#|
INPUT: you can give either classes1, or instance1 (in which case classes1 is looked up)
TEST: "compatibilty", i.e., Classes mustn't be disjoint, and may have a subsumption requirement also.
RETURNS: TWO values
 - non-NIL if the classes are compatible, NIL if they are incompatible
 - A list of the partitions that were violated, if any.

IN ADDITION: As we also allow negated class values, we must also check consistency here,
	e.g. (instance-of (Car)) and (instance-of ((<> Car))) are incompatible.
	Also, because instance-of is a *built-in-remove-subsumers-slots*, (instance-of (Car)) and (instance-of ((<> Vehicle))) are incompatible,
			although (instance-of (Vehicle)) and (instance-of ((<> Car))) are not.
	[This handling of types as values needs better facilities in KM]
HOWEVER: We **DEFER** this checking instead to check-slotvals-constraints instead, as this kind of check is already performed for other slots.
class constraints are simply ignored here as if they weren't there.
Note: The subsumption requirement isn't that the instance is subsumed by a class,
	  but that one set of classes is subsumed by another.
[2] This may miss some constraints if instance-of-is-fluent is true.
[3] New: classes-subsumep = 'exact-match, 't or nil. exact-match checks for identity.
|#
(defun compatible-classes (&key instance1 instance2 classes1 classes2 classes-subsumep check-locked-classes-p)
  (let ( (immediate-classes1
	  (or classes1
	      (and instance1 (immediate-classes instance1))
	      (report-error 'program-error "compatible-classes: missing instance/classes for instance1!~%")))
	 (immediate-classes2
	  (or classes2
	      (and instance2 (immediate-classes instance2))
	      (report-error 'program-error "compatible-classes: missing instance/classes for instance2!~%"))) )
    (cond ((eq classes-subsumep 'exact-match)					; [3]
	   (set-equal immediate-classes1 immediate-classes2))

	  ;;; 2/28/12 HLO-4165. locked-instance-of: These classes are NOT allowed to be removed by unification
	  ((and check-locked-classes-p
		(some #'(lambda (locked-class1)
			  (some #'(lambda (class2)
				    (and (is-subclass-of class2 locked-class1)
					 (neq class2 locked-class1)))		; oops! Need to allow equality still (HLO-4848)
				immediate-classes2))
		      (and (kb-objectp instance1) (or (get-vals instance1 '#$locked-instance-of)
						      (get-vals instance1 '#$locked-instances-of)))))  ;	Backwards-compatibility with KM invert-slot error
	   (let* ((locked-classes1 (or (get-vals instance1 '#$locked-instance-of)
				       (get-vals instance1 '#$locked-instance2-of)))	; Backwards-compatibility with KM invert-slot error
		  (violating-classes2 (remove-if-not #'(lambda (class2)
							 (some #'(lambda (locked-class1)
								   (and (is-subclass-of class2 locked-class1)
									(neq class2 locked-class1)))
							       locked-classes1))
						     immediate-classes2)))
	     (values nil nil (list (delistify locked-classes1) (delistify violating-classes2)))))
	  ((and check-locked-classes-p
		(some #'(lambda (locked-class2)
			  (some #'(lambda (class1)
				    (and (is-subclass-of class1 locked-class2)
					 (neq class1 locked-class2)))
				immediate-classes1))
		      (and (kb-objectp instance2) (or (get-vals instance2 '#$locked-instance-of)
						      (get-vals instance2 '#$locked-instances-of)))))
	   (let* ((locked-classes2 (or (get-vals instance2 '#$locked-instance-of)
				       (get-vals instance2 '#$locked-instances-of)))
		  (violating-classes1 (remove-if-not #'(lambda (class1)
							 (some #'(lambda (locked-class2)
								   (and (is-subclass-of class1 locked-class2)
									(neq class1 locked-class2)))
							       locked-classes2))
						     immediate-classes1)))
	     (values nil nil (list (delistify locked-classes2) (delistify violating-classes1)))))
	  ((or classes-subsumep
; 9/27/12 - I'll remove the below constraint, as sometimes we want to use Sequence in the KB also and avoid
;           KM> ((a Foo) & (a Sequence)) -> ERROR! Unification (_Foo2 & (a Sequence)) failed! The classes were found to be incompatible.
;           That is: There is not really any significant reason to insist that Sequence only refers to a (:seq ...) KM structure
;	    However, we *do* want to retain ((:seq a b) &? (a Cat)) -> NIL, otherwise we'll end up with _Cat1 -> (:seq a b) isa Sequence, no longer a Cat
;	       (intersection immediate-classes1 '#$(Sequence Pair Triple Bag))		; force subsumep test on these types of objects
;	       (intersection immediate-classes2 '#$(Sequence Pair Triple Bag))
	       (and instance1 (not (kb-objectp instance1)) (intersection immediate-classes1 '#$(Sequence Pair Triple Bag))) ; block ((:seq a b) &? (a Cat)), otherwise we'll end up with _Cat1 -> (:seq a b) isa Seq
	       (and instance2 (not (kb-objectp instance2)) (intersection immediate-classes2 '#$(Sequence Pair Triple Bag)))
	       )
	   (or (classes-subsume-classes immediate-classes1 immediate-classes2)
	       (classes-subsume-classes immediate-classes2 immediate-classes1)))
	  (t (let ((violated-partitions (disjoint-class-sets immediate-classes1 immediate-classes2 :instance1 instance1 :instance2 instance2)))
	       (cond ((null violated-partitions) t)
		     (t (values nil violated-partitions))))))))
#|
======================================================================
    HANDLING OF PARTITIONS - only used by the above function compatible-classes
======================================================================

[1] all-superclasses0 is like all-superclasses, except it INCLUDES class, and MAY NOT
     include Thing unless Thing is explicitly declared as a superclass. This is exactly
     what we want here!
RETURNS:
  - A list of Partitions that an instance in both immediate-classes1 and immediate-classes2 violates
    or NIL of no Partition is violated (i.e. the two class sets are NOT disjoint and can be combined.
|#
(defun disjoint-class-sets (immediate-classes1 immediate-classes2 &key instance1 instance2)
  (disjoint-class-sets0 (remove-duplicates (my-mapcan #'all-superclasses0 (remove '#$Thing immediate-classes1))) ; [1]
			(remove-duplicates (my-mapcan #'all-superclasses0 (remove '#$Thing immediate-classes2))) ; [1]
			:instance1 (or instance1 `#$(a ,(VALS-TO-VAL IMMEDIATE-CLASSES1))) ; purely for tracing output
			:instance2 (or instance2 `#$(a ,(VALS-TO-VAL IMMEDIATE-CLASSES2))))) ; purely for tracing output

#|
[1] all-superclasses0 retains class, excludes Thing
RETURNS: NIL if no partition was violated
	 A list of partitions if some partition was violated; removing singletons will show which partitions were violated.
|#
(defun disjoint-classes (classes &key check-singletonp)
  (cond
   ((null classes) nil)
   ((and (singletonp classes) (not check-singletonp)) nil)
   (t (let* ((all-classes (remove-duplicates (my-mapcan #'all-superclasses0 classes)))
	     (all-partitions (my-mapcan #'(lambda (c) (get-vals c '#$member-of)) all-classes)))
	(cond ((not (= (length all-partitions) (length (remove-duplicates all-partitions)))) all-partitions))))))
		; duplicates -> disjoint (dups can only arise if multiple, different classes point to same partition)

#|
RETURNS: A list of partitions that are violated by an instance that is an instance-of both classes1 and classes2
(disjoint-class-sets0 '(Na Substance) '(Zn Substance))
    Na -> Partition1, Zn -> Partition1 so there's a clash
But Substance -> Partition1, Substance -> Partition1 no clash
So we just need the UNIQUE elements of classes1, and see their partitions
   and the UNIQUE elements of classes2, and see their partitions
   and check for no overlap.
   Proof: UNIQUE means they are DIFFERENT values. And so they can't both belong to the same partition.
|#

(defun disjoint-class-sets0 (classes1 classes2 &key instance1 instance2)
  (declare (ignore instance1 instance2))
  (and (not (equal classes1 classes2))
       (not (subsetp classes1 classes2))
       (not (subsetp classes2 classes1))
       ;;; Much more efficient implementation of partition checking with large partitions
       (let ((partitions1 (my-mapcan #'(lambda (c1) (get-vals c1 '#$member-of)) (set-difference classes1 classes2)))
             (partitions2 (my-mapcan #'(lambda (c2) (get-vals c2 '#$member-of)) (set-difference classes2 classes1))))
	 (intersection partitions1 partitions2))))

#|
(some #'(lambda (partition)
		 (let* ( (partition-members (get-vals partition '#$members :situation *global-situation*))
			 (classes1-in-partition (intersection classes1 partition-members)) )

;;; Exhaustive partition check...
	       SEE BELOW
;;; Disjoint classes check
		   (cond ((null classes1-in-partition) nil)						; Non-mutually exhaustive partition - null is ok
			 ((not (singletonp classes1-in-partition))
			  (report-error 'user-error "An object ~a was encountered which was in mutually exclusive classes ~a!~%   [Partition was: (~a has (members ~a))]~%"
					instance1 classes1-in-partition partition partition-members))
			 ;;; We could also check partition2 like this, but don't bother
			 (t (intersection classes2 (remove (first classes1-in-partition) partition-members))))))   ; = classes1 & classes2 are
	     (all-instances '#$Partition))))									   ;       disjoint
|#
#|
EXHAUSTIVE PARTITIONS -- needs some more work: They are only applicable if the instance is a member of the partition's PARENT, an as-yet
undefined slot.
	e.g. (a Exhaustive-Partition with (parent (Tangible)) (members (Solid Liquid Gas)))
 So it's OK if a Dream isn't in any of this partition's members, but not for _Dog23.  But it IS okay if _Tangible23 isn't in any members
 (ie. we haven't decided on which member it is in). But then, which instances DO we check for compulsory class membership for??

;;; Exhaustive partition check...
		   (cond ((isa partition '#$Exhaustive-Partition)
			  (cond ((null classes1-in-partition)
				 (report-error 'user-error "Instance ~a must be in exactly one class in the below exhaustive partition!~%    (~a has (members ~a))~%    [~a is currently in classes ~a]~%" instance1 partition partition-members instance1 classes1))
				((null (intersection classes2 partition-members))
				 (report-error 'user-error "Instance ~a must be in exactly one class in the below exhaustive partition!~%    (~a has (members ~a))~%    [~a is currently in classes ~a]~%" instance2 partition partition-members instance2 classes2)))))
|#


