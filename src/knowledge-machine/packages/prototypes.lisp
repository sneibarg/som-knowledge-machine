
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: prototypes.lisp
;;; Author: Peter Clark
;;; Purpose: Knowledge Representation using Prototypes -- the answer to life!

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

#|
An explanation is recorded for cloned triples such as:

	(explanation (:triple <clone-node> <slot> <val>) ((cloned-from <prototype-root> <clone-root> <prototype-node>)))
	(explanation (:triple _Entity23 agent-of _Foo22) ((cloned-from _ProtoFoo7 _Foo22 _ProtoEntity10)))

where <prototype-root> was cloned onto <clone-root>, resulting in <prototype-node> cloning to <clone-node>.

NOTES:
If B is cloned from ProtoA, then raised to a prototype ProtoB, then ProtoB cloned to C:
Normally (if *record-explanations-for-clones* is t), triples in C will have explanations
		(cloned-from ProtoB) (cloned-from ProtoA)
But with *record-explanations-for-clones-selectively* set to t (and *record-explanations-for-clones* t),
		triples in C will just retain the ORIGINAL source explanation (cloned-from ProtoA).
		Note: If the triple in ProtoA had it's own explanation e.g., from (every SuperA has ....),
		then (cloned-from ProtoA) would not be recorded in C, rather (again) just the original source
		would be recorded.
|#
;(defparameter *record-explanations-for-clones-selectively* t) ; NO! Need nil for some fns, e.g., triple-expanded-from
;(defparameter *record-explanations-for-clones-selectively* nil)

(defparameter *clone-built-from-slot* '#$clone-built-from)
(defparameter *add-cloned-from-links* t)
(defparameter *propogate-explanations-to-clones* t) ; see knowledge-revision/add-triple-asif-cloned/test-clones-of-clones.lisp for why is needed

;;; This always T, except for the special case of AURA when we can skip this. See [4] in (defun clone () ...) later
(defparameter *dereference-explanations-during-cloning* t)

;;; Used for cloning itself: Don't clone these slots' values when cloning the prototype graph.
;;; cloned-from and clone-built-from NOT in this list, to allow clones to be added into prototypes
;;; Make this a parameter (not constant), so user can change it
(defparameter *unclonable-slots*
    '#$(prototype-participant-of prototype-participants
	prototype-of prototypes
	prototype-scope locked-instance-of
	has-clones
	has-built-clones))

;;; The above parameter might change, but this one won't. This is used:
;;; - in save-prototype and trim-prototype to bypass the check that a slot's values are all participants
;;;	(and remove the non-participants). These special slots are allowed to have non-participant values.
;;; - in build-clone, to take care of an obscure case: In obscure circumstances, a non-root might be
;;;	cloned-from its own root. During cloning, we do NOT want these particular cloned-from values to
;;;	be copied to the clone.
(defparameter *slots-with-nonparticipant-skolems*
    '#$(cloned-from
	clone-built-from
	has-clones
	has-built-clones))

;;; We don't want to save the run-time clones in a prototype to disk (see writer.lisp), as the clones don't persist.
(defparameter *prototype-slots-not-to-save-to-file* '#$(;; added by MW, 2011-06-24:
							;; clean-instance-of clean-instances  - no, application-specific. Moved to application code.
							has-clones has-built-clones ))

;;; Added by MW, 2011-06-24: we don't want to save explanations for slots like clean-instance
;;; PEC moved to loadkb.lisp where it's used, also set to NIL as the values here are application-dependent
; (defparameter *exclude-explanations-for-prototype-slots* '#$(clean-instance-of clean-instances))

;;; Purpose: save-prototype will output these, even though their values are not prototype-participants.
; (defparameter *prototype-bookkeeping-slots* '#$(has-clones has-built-clones cloned-from clone-built-from))
; (defparameter *prototype-bookkeeping-slots* '#$(has-clones has-built-clones))
; Now hard-wired into writer.lisp

;;; We can tell if it's cloned or not like this
(defun isa-clone (instance)
  (and (kb-objectp instance)
       (get-vals instance '#$cloned-from :situation *global-situation*)))

;;; ----------

; (defvar *curr-prototype* nil)		; in header.lisp
(defun am-in-prototype-mode () *curr-prototype*)
(defun curr-prototype () *curr-prototype*)

(defun protoinstancep  (concept)
  (and (kb-objectp concept) (get-vals concept '#$prototype-participant-of :situation *global-situation*)))
(defun prototypep (concept)
  (and (kb-objectp concept) (get-vals concept '#$prototype-of :situation *global-situation*)))
;; Synonym
(defun protorootp (concept) (prototypep concept))

(defun protoclass (protoinstance)
  (let ((protoroot (get-unique-val protoinstance '#$prototype-participant-of)))
    (when protoroot (delistify (get-vals protoroot '#$prototype-of)))))

;;; Returns: The prototype root (an instance)
;;; Updated by Sunil Mishra:
;;; Subject: [JIRA] Commented: (HLO-1755) triple-cloned-from doesn't work forcomplex values
;;; Triples claims the triple doesn't exist in the KB. Below is an updated version that I think does what you'd intended.
(defun in-prototype (triple)
  (let* ((f (dereference (first triple)))
	 (s (second triple))
	 (v (dereference (third triple))))
    (cond
      ((not (member v (get-vals f s :situation *global-situation*) :test #'equal))
       (report-error 'user-error "~a does not exist as part of a prototype in the KB!" triple triple))
      (t (let* ((prototype-roots0
		 (cond ((anonymous-instancep v)
			(list (get-unique-val f '#$prototype-participant-of)
			      (get-unique-val v '#$prototype-participant-of)))
		       ((consp v)
			(cons (get-unique-val f '#$prototype-participant-of)
			      (mapcan (lambda (v-item)
					(when (anonymous-instancep v-item)
					  (list (get-unique-val v-item '#$prototype-participant-of))))
				      (flatten v))))
		       (t (list (get-unique-val f '#$prototype-participant-of)))))
		(prototype-roots (remove-duplicates (remove nil prototype-roots0))))
	   (cond ((null prototype-roots)
		  (report-error 'user-error "~a is not part of a prototype!" triple triple))
		 ((not (singletonp prototype-roots))
		  (report-error 'user-error
				"~a appears to incoherently be part of multiple prototypes!"
				triple triple))
		 (t (first prototype-roots))))))))

					; Not used any more.
;;; concept /= generic, but a special case of it.
;(defun qualified-prototypep (concept)
;  (and (prototypep concept)
;       (find-vals concept '#$activity-type)))

;;; ======================================================================
;;;			LAZY CLONING:
;;;	We only clone prototypes which have a value for the slot of interest.
;;; ======================================================================

;;; If slot is nil, then all prototypes are unified in. Returned result is irrelevant (nil).
;;; 9/22/03: New: return list of prototypes unified in
;(defun unify-in-prototypes (instance0 &optional slot)
;  (let* ( (instance (dereference instance0))				; identity may change with each iteration
;	  (prototype (first-applicable-prototype instance slot)) )
;    (cond (prototype (unify-in-prototype instance prototype slot)
;		     (cons prototype (unify-in-prototypes instance slot))))))

;;; MODIFICATION: [1] Prevent unifying prototypes while unifying in prototypes, for more efficiency -- with
;;; lots of prototypes, the whole thing can grind to a halt.
;;; This *seems* to be okay, although might be completeness problems?
;;; [ How it works: *recursive-prototypes* is NIL, and unify-in-prototypes is only called if *use-prototypes* is T ]
;;; [2] NOTE: unifying in applicable prototype1 may result in applicable prototype2 not being needed any
;;;	      more, because protoroot1 was clone-built-from* protoroot2 (thus after cloning in prototype1,
;;;	      instance will be clone-built-from* protoroot2 also, i.e., already include prototype2 within it).
(defun unify-in-prototypes (instance0 &optional slot)
;    (let* ((*are-some-prototypes* nil)		; [1] local scope change, prevents recursive prototype cloning
; (let* ((*are-some-prototypes* *recursive-prototypes*) ; [1] local scope change, prevents recursive prototype cloning
  (let* ((*use-prototypes* *recursive-prototypes*) ; [1] local scope change, prevents recursive prototype cloning
;	 (*unifying-in-prototype* t)		   ; Additional flag, for lazy-unify-vals - no, not needed
	 (instance (dereference instance0)) 		; NEW: Allow that prevention to be toggleable
	 (all-applicable-prototypes (all-applicable-prototypes instance slot)))
    (mapc #'(lambda (prototype)
	      (cond ((not (member prototype (clone-built-from* instance)))	; [2]
		     (unify-in-prototype instance prototype slot))))
	  all-applicable-prototypes)
    all-applicable-prototypes))

#|
[3] NOTE: defined-prototypes includes ALL prototypes, i.e., is a superset of (<class> has (prototypes (<x>))) values.
    That is, if we simply have (_Car1 has (prototype-of (Car)) (prototype-scope (Car)))  then  (get '#$Car '#$defined-prototypes) *will* include _Car1
Note: the fact _Euk-cell14 below has a definition on it will be logged on Cell (property 'defined-prototypes):
(_Euk-cell14 has
  (instance-of (Euk-cell))
  (prototype-of (Euk-cell))
  (prototype-scope (Euk-cell
                    (the-class Cell with (has-part ((a Nucleus))))))

(get '#$Cell 'defined-prototypes) -> (|_Euk-cell14|)
(get '#$Euk-Cell 'defined-prototypes) -> (|_Euk-cell14|)
|#
(defun all-applicable-prototypes (instance &optional slot)
  (remove-if-not #'(lambda (prototype) 				; NEW [2]
		     (suitable-for-cloning instance slot prototype))
		 (my-mapcan #'(lambda (class)
;				(get-vals class '#$prototypes :situation *global-situation*)
;				(km-format t "(get ~a 'defined-prototypes) = ~a~%" class (get class 'defined-prototypes))
				(get class 'defined-prototypes))   ; [3]
			    (all-classes instance))))

;;; ------------------------------

;;; with eager unification, we can end up in an infinite loop with big KBs (e.g. aeronet.km)
;;; So make this toggleable
(defvar *trace-unify-in-prototype* nil)

#|
[4] KM 1.4.0-beta32, we substantially simplified prototypes so that a prototype will never draw any external information in
when building a prototype, so the problem [3] never occurs.
The implementation of (obj-stack), called by remove-from-stack, is terrifyingly inefficient!!!!
sequential version no longer may get into these looping problems
[5] Neah, with situations we need to clone and merge for each situation, unfortunately.
In particular, we want any CONSTRAINTS to be passed down to instances in EVERY situation, and constraints aren't projected.
RETURNS: Irrelevant
[6] We cannibalize the stack to make sure we don't unify a prototype as part of unifying the same prototype. The stack is
    searched in applicable-prototypes to check on this.
[7] If cloned-from is a non-fluent, so we only ever clone once, then we better unify in Global so any local values and
    constraints are universally applicable
[8] If cloned-from is a non-fluent, then we only ever clone once. So we better put all the clone results in *Global, so
    that any constraints are universally applicable.
|#
(defun unify-in-prototype (instance prototype &optional slot)	; slot is purely for tracing purposes
  (cond (*trace-unify-in-prototype*
	 (km-format t "UNIFYING IN PROTOTYPE ~a for ~a~%" prototype instance))) ; just for Shaken use
  (push-to-goal-stack `#$(unify-with-clone-of ,PROTOTYPE))			; [6]
  (let ((*use-prototypes* *recursive-prototypes*)      ; Double-check this is correctly set (prevents recursive prototype cloning), in case it's called directly rather than via unify-in-prototypes
	(clone (km-unique-int `#$(clone ,PROTOTYPE)))) ; [3] route through query interpreter for tracing

    (cond ((null slot) (make-comment "Cloned ~a~28T  -> ~a~%~10Tto find all info about ~a.~%~10t(~a is/satisfies definition of ~a)" prototype clone instance instance
				     (delistify (get-vals prototype '#$prototype-of))))
	  (t (make-comment "Cloned ~a~28T  -> ~a~%~10Tto find (the ~a of ~a).~%~10t(~a is/satisfies definition of ~a)" prototype clone slot instance instance
			   (delistify (get-vals prototype '#$prototype-of)))))

;    In theory, this should be redundant as we already have (instance has (cloned-from (prototype))) created during
;    the cloning operation. Anyway, leave it here.
; JUNE 2007 - No let's try removing it
;   (add-val instance *clone-built-from-slot* prototype) ; restating default extra args unnecessary

#|
If the prototype SPECIALIZES the classes on instance, then record the explanation why.
This rarely fires, but occasionally is needed (see test-suite/prototypes.km) when there are class expressions on
the prototype-scope. The example is:
	(_ProtoPerson2 has (protoype-scope (Person (the-class Animal with (parts ((a Big-Brain)))))))
	(a Animal with (parts ((a Big-Brain)))) -> _Animal1
	(get-explanation-data '#$_Animal1) ->
	    (_Animal1 instance-of Person (_Animal1 isa (the-class Animal with (parts ((a Big-Brain))))))
|#
#| 10/29/11 -
   record-explanation-for stopped working, as the actual assertion (instance instance-of new-class) has not been made yet (and hence
	is filtered out by record-explanation-for).
   To repair, this is now done as part of classify-as-prototype0 in satisfies-prototype-definition, where classify-as-prototype0 actually
   	does the assertion.
     (cond (*record-explanations*
;	    (km-format t "START: recording explanations for (clone ~a) onto ~a...~%" prototype instance)
	    (let ((old-classes (immediate-classes instance))	; Animal
		  (new-classes (immediate-classes prototype)))	; Person (the-class Animal with (parts (a Big-Brain)))
	      (cond ((not (classes-subsume-classes new-classes old-classes)) ; so new-classes SPECIALIZE old-classes...
		     (let ((target `#$(the instance-of of ,INSTANCE))
			   (prototype-scopes (subst instance prototype 		; update Self after cloning
						    (get-vals prototype '#$prototype-scope))))
		       (mapc #'(lambda (new-class)
				 (mapc #'(lambda (prototype-scope)
					   (cond ((the-class-exprp prototype-scope)
;						  (record-explanation-for target new-class `#$(,INSTANCE isa ,PROTOTYPE-SCOPE)))))
						  (let* ((class+slotsvals (class-descriptionp prototype-scope))
							 (class (first class+slotsvals))
							 (slotsvals (second class+slotsvals)))
						    (record-explanation-for target new-class `#$(every ,NEW-CLASS has-definition (instance-of (,CLASS)) ,@SLOTSVALS))))))
				       prototype-scopes))
			     new-classes)))))
;	    (km-format t "END: recording explanations for (clone ~a) onto ~a...~%" prototype instance)
;	    (break)
	    ))
|#
; [10] If instance is already cloned-from prototype (but is necessarily not clone-built-from prototype, else we
;      wouldn't be unifying in the prototype in the first place), then instance's graph may already contain *part*
;      of the prototype. This is the condition for considering &&! for combine-values-by-appending slots, to
;      stop the values growing endlessly.
; [11] Suppose X cloned-from, but not clone-built-from, Y, i.e., X is partially clone from Y.
;      Now we have A, we unify in a clone of X  (-> A cloned-from X), now we consider unifying in a clone of Y.
;      We need to register that Y is already partially included in A, hence we need to use cloned-from*, not cloned-from.
;    (cond ((member prototype (get-vals instance '#$cloned-from)) ; [11]

;     (km-format t "prototype = ~a~%" prototype)
;     (km-format t "instance = ~a~%" instance)
;     (km-format t "(cloned-from* instance) = ~a~%" (cloned-from* instance))
     (cond ((member prototype (cloned-from* instance)) ; [10]
	    (let ((*partially-included-prototype* prototype))
	      (cond (*eagerly-unify-prototypes* (km-int `(,instance &! ,clone) :fail-mode 'error))
		    (t (km-int `(,instance & ,clone) :fail-mode 'error)))))
	   (t (cond (*eagerly-unify-prototypes* (km-int `(,instance &! ,clone) :fail-mode 'error))
		    (t (km-int `(,instance & ,clone) :fail-mode 'error)))))

     )
  (pop-from-goal-stack))

;;; We only clone prototype roots, not things which are *in* a prototype
;(defun find-and-clone-prototypes (instance slot)
;  (mapcar #'clone (applicable-prototypes instance slot)))

;;; Returns a list of prototypes which can validly provide values of slot for instance
;;; NB We must do the "already-done" test *after* the suitable-for-cloning work, because suitable-for-cloning may
;;; itself create new prototypes when doing the subsumption check!
;;; [1] If P1 and P2 are prototypes to clone, but P2 is already cloned from P1, then don't reclone P1!
;;;     I assume you can't get mutual dependencies, where P1 is cloned from P2, is cloned from P1.
;;; [2] return just the first one instead
;(defun applicable-prototypes (instance slot)			; OLD [2]
;  (remove-if-not #'(lambda (prototype) 			; OLD [2]
;;; 1/19/10 - Appears to be no longer used for years, so comment out!
;(defun first-applicable-prototype (instance &optional slot) ; NEW [2]
;  (find-if #'(lambda (prototype) 				; NEW [2]
;	       (suitable-for-cloning instance slot prototype))
;	   (my-mapcan #'(lambda (class)
;			  (get-vals class '#$prototypes :situation *global-situation*))
;		      (all-classes instance))))

; No longer used
;;; Returns a list of prototypes which can provide values of slot for instance, valid for a particular context only
;(defun qualified-prototypes (instance slot)
;  (let* ( (all-classes (all-classes instance))
;	  (all-prototypes (remove-if-not #'protoinstancep (my-mapcan #'(lambda (class)
;								     (find-vals class '#$instances))
;								 all-classes)))
;	  (qualified-prototypes (remove-if-not #'(lambda (prototype)
;						   (find-vals prototype slot))
;					       all-prototypes)) )
;    qualified-prototypes))

;;; Should we clone prototype to find the slot of instance?
;;; [1] This is comparing just along one dimension of "context space"
;;; [2] It's not obvious, but we only ever need to clone a prototype *once* per instance, namely in the highest supersituation in which that
;;; 	instance is an instance-of the prototype class. In any next-situations, the values will then be projected. In any new-situations,
;;;	the instance will have no known instance-of relationship, and thus the cloning wouldn't be valid anyway.
;;; [6] This catastrophic kind of looping should *never* occur, but we better test for it anyway! See test-suite/protolooping2.km for
;;;     a case where it might be necessary.
(defun suitable-for-cloning (instance slot prototype)
  (and (neq instance prototype)			; don't clone yourself!
       (prototypep prototype)		; 1. Is a prototype
       (or 					; Ignore constraint 2 -- it may provide other valuable info!!
	(null slot)
	(instance-has-something-to-say-about prototype slot))
       (neq prototype (curr-prototype))		; 4. don't clone curr prototype to help answer query during building curr prototype!

;       (not (member prototype (get-vals instance *clone-built-from-slot*)))
	; No, clone-built-from is transitive!!! So do the below for significant efficiency improvements!
       (not (member prototype (clone-built-from* instance)))

;      (not (looping-on `#$(unify-with-clone-of ,PROTOTYPE)))	; See note [6] in unify-in-prototype, and above
			        ; 5. do subsumption check, to make sure instance satisfies prototype's qualifications
       (progn
	 (km-trace 'comment "Seeing if prototype ~a is applicable to ~a..." prototype instance)

	 (satisfies-prototype-definition instance prototype)
	 )))

#|
;;; 1/16/04 - allow multiple prototype-scope statements
;;; [1] NOTE: get-vals undesirably does a bind-self with the prototype instance, so need to undo it for scopes like:
;;; (prototype-scope ((the-class Rectangle with (length ((the width of Self))) (width ((the length of Self))))))
(defun satisfies-prototype-definition (instance prototype)
;  (km-int `(,(get-unique-val prototype '#$prototype-scope :situation *global-situation*) #$covers ,instance)))
  (some #'(lambda (prototype-scope)
	    (cond ((or *prototype-classification-enabled*
		       (not (second (class-descriptionp prototype-scope)))); Cat, (the-class Cat) ok, but no "with" allowed
		   (km-int `(,instance #$isa ,prototype-scope)))))
	(subst '#$Self prototype (get-vals prototype '#$prototype-scope :situation *global-situation*)))) ; [1]
|#

;;; [1] (classify-as-prototype0 i p) returns NIL if i is already a p, but here we want success for this case, as inheritance hasn't been done
;;; [2] Takes care of asserting the new class, tracing, and adding to the explanation DB
(defun satisfies-prototype-definition (instance prototype)
  (let ((protoclasses (remove-subsumers 	; Ug - remove-subsumers because AURA allows redundant classes e.g., (instance-of (Cell Tangible-Entity))
		       (get-vals prototype '#$instance-of)))) ; I guess...rather than '#$prototype-of, which may be overly general as used for indexing
    (or (some #'(lambda (protoclass) (instance-of instance protoclass)) protoclasses)    ; [1]
	(and *prototype-classification-enabled* (classify-as-prototype0 instance prototype))))) ; [2]

#|
 ======================================================================
			CLONING
A prototype is an anonymous prototype instance, connected to a network of other
instances, which can be both:
	- anonymous prototype instances
	- named instances

Cloning involves building a copy of this network, with prototype instances
replaced with new anonymous instances.

Note that cloning DOESN'T do any evaluation of expressions, they are just
cloned as is.

:including-extra-slots has been added so that AURA can control when coordinate information is cloned or not.
This is done by:
  (i) AURA modifying *unclonable-slots* to include the slots containing coordinate info (so for KM's reasoning,
		by default it's not cloned)
		(ii) adding those slots back in using this keyword, when cloning for knowledge editing.

:without-bookkeeping changes the cloning behavior to create an IDENTICAL COPY of the original. The
   difference (cf normal cloning) is purely in which explanations are created and cloned:
   (1) KM does NOT record cloned-from links from the prototype nodes to the clones
   (2) KM copies the ENTIRE explanation database from the prototype verbatim (renaming Skolems, of course)
   	(cf. with normal cloning, added-at explanations *aren't* copied)
   Note that cloned-from links from the clone to the prototype ARE still asserted in the KB (HLO-1423), just not
   explanations for them. Sunil then manually removes these cloned-from links when the clone is promoted up
   to replace the original prototype (HLO-1802).

RETURNS: two values: the clone name, and also the mappings from proto-instances to the cloned instances

=====================================================================

[1] prevents trying to clone P to find info about a clone of P.
Later: instead of flagging "nil" here, I added cloned-from as a non-inverse-recording slot, to prevent this problem in general.
For example: I1 & Clone1, where Clone1 has cloned-from X, results in X being added to the object stack when the unified result
is asserted into memory and the inverses are automatically installed.

[2] This call to km causes redundant work: Suppose my clone is
	(:set
	  (_ProtoCar1 has (parts (_ProtoEngine1)))			  ; (i)
	  (_ProtoEngine1 has (parts-of (_ProtoCar1 _ProtoTransmission1))) ; (ii)
	  ...)
(i) will assert both _ProtoCar1 and the inverse link (_ProtoEngine1 parts-of _ProtoCar1)
Then at (ii), because _ProtoEngine1 already has some slotsvals, KM will merge in rather than just assert the
given slotsvals. And this merging can be computationally complex (?) [though I think my optimizations filters these out]?
But worse: If we load a prototype while in prototype mode, (<i> has <slotsvals>) will be followed by an (evaluate-paths),
which is killingly expensive and unnecessary!

A put-slotsvals will work fine here, it will clober any old values (eg. any earlier-installed inverses), but that's
fine as the new values should necessarily include those old values.

[3] It's not clear that we really need to keep these prototype-participant links, (they could be recomputed by a search algorithm if really
necessary). I'll leave them for now, as I went to all the trouble!.
[4] knowledge-revision/add-triple-asif-cloned/test-clones-of-clones.lisp fails otherwise, as
	USER: (get-all-explanations |_Finger5| |parts-of| :situation |*Global| :ignore-clone-cycles nil)
	((|_Finger5| |instance-of| |Finger| (|cloned-from| |_Arm1| |_Arm3| |_Finger1|))
	 (|_Finger5| |parts-of| |_Hand4| (|cloned-from| |_Arm1| |_Arm3| |_Finger1|)))
    but _Arm3 has been bound earlier to _Arm2. We are counting on _Arm2 being returned so that the sublis at [5] succeeds:
	prototype = _Body1, prototype0 = _Body1
	participant = _Hand4, clone0 = _Hand10
	mapping-alist = ((_Finger5 . _Finger11) (_Hand4 . _Hand10) (_Arm2 . _Arm9) (_Body1 . _Body8))
	old-isv-explanations = ((_Hand10 parts _Finger11 (cloned-from _Body1 _Body8 _Hand4))
	                        (_Hand10 instance-of Hand (cloned-from _Body1 _Body8 _Hand4))
	                        (_Hand10 parts-of _Arm9 (cloned-from _Body1 _Body8 _Hand4)))
	isv-explanations = ((_Hand4 parts _Finger5 (cloned-from _Arm1 _Arm3 _Hand1))
			    (_Hand4 instance-of Hand (cloned-from _Arm1 _Arm3 _Hand1))
	                    (_Hand4 parts-of _Arm3 (cloned-from _Arm1 _Arm3 _Hand1)))
    We are counting on the sublis at [5] replacing _Arm2 with _Arm9, but as _Arm3 has not been dereferenced to _Arm2 this doesn't happen.
|#
(defun clone-without-bookkeeping (prototype &key including-extra-slots)
  (clone prototype :including-extra-slots including-extra-slots :without-bookkeeping t))

(defun clone (prototype0 &key including-extra-slots without-bookkeeping)
;  (km-format t "Cloning ~a...~%" prototype0)
;  (break)
  (let (; (*classification-enabled* nil)	; New - disable classification, of course!
	; NEW: Moved it later inside the mapc iteration
	; classification afterwards on the clone. (It's possible a clone instance might satisfy a new definition)
	(*trace* nil)
	(*dereferencing-on* nil)	; Inefficient and not necessary to do dereferencing
	(*am-reasoning* t)		; In case (clone ...) called directly from the Lisp prompt
;	NOTE: ***is** needed (critical) for dereferencing the *explanations* later in this function in get-all-explanations [4]
	(prototype (dereference prototype0)))
  (cond
   ((not (prototypep prototype))
    (report-error 'user-error "Attempt to clone a non-prototype ~a!~%" prototype))
   ((and (am-in-situations-mode)
	 (am-in-global-situation))
    (report-error 'user-error "Attempt to clone a prototype ~a in the global situation while using Situations -- not allowed!~%Only do cloning in local situations when using KM Situations.~%"
		  prototype))
   (t
;    (format t "build-clones...~%")
    (multiple-value-bind
     (clones mapping-alist)  ; clones = list of (<clone> <slotsvals>) pairs. mappings = alist (<orig-object>.<clone>) pairs
     (build-clones prototype :including-extra-slots including-extra-slots)	; compute what clones would look like
     (let ((clone-of-prototype (rest (assoc prototype mapping-alist)))) ; find the clone of the ROOT instance
       (let ((*classification-enabled* nil)
	     (*prototype-classification-enabled* nil)      ; temporarily disable classification, as we need to do ALL
							   ; the assertions first before attempting classification!
;	     (*dereferencing-on* nil)			  ; Slightly inefficient and not necessary to do dereferencing
	     )
;	 (format t "add-slotsvals...~%")

         (mapc #'(lambda (clone+slotsvals) ; expr = (<clone> <slotsvals>)		; NEW drop <situation>
		 (let* ((clone (first clone+slotsvals))
			(slotsvals (second clone+slotsvals))
			(cloned-from (first (rassoc clone mapping-alist))))
		   (add-slotsvals clone slotsvals) ; install-inversesp = t; eg. (I instance-of C), we *do* need

; Neah...
;		   (cache-explanation-for clone `#$(cloned-from ,PROTOTYPE (,CLONE-OF-PROTOTYPE)))

; Neah again...well (1/8/02) let's make it switchable...
		   (cond
		    ((and (or *record-explanations* *record-explanations-for-clones*)
			  (not without-bookkeeping))
		     (mapc #'(lambda (slotvals)
			       (let* ((slot (slot-in slotvals))
				      (target `#$(the ,SLOT of ,CLONE)))
				 (cond
				  ((member slot '#$(cloned-from clone-built-from)) nil)

				  ((and (eq slot '#$instance-of) ; don't "explain" the root node class (HLO-1355)
;					(eq cloned-from prototype)
; NEW: *Don't* create cloned-from links for the instance-of explanations, they're redundant wrt. the copied added-at links in AURA. See knowledge-revision/oct11-problem.txt
					)
;				   (mapc #'(lambda (val) (km-format t "DEBUG: Not creating cloned-from explanation for (~a instance-of ~a)~%" clone val)) (vals-in slotvals))
				   nil)	; See knowledge-revision/instance-of-support/
				  (t (mapc #'(lambda (val)
					       (record-explanation-for target val ; [2]
						       `#$(cloned-from ,PROTOTYPE ,CLONE-OF-PROTOTYPE
								       ,CLONED-FROM ; ,CLONE-OPERATION-ID
								       )))
					   (vals-in slotvals))))))
; This would be a better solution, rather than storing explanations in both directions.
;				  (t (mapc #'(lambda (val)
;					       (let* ((val-cloned-from 				       ; May be nil
;						       (listify (first (rassoc val mapping-alist))))   ; Listified for ,@
;						      (explanation `#$(cloned-from ,PROTOTYPE ,CLONE-OF-PROTOTYPE
;										   ,CLONED-FROM ,@VAL-CLONED-FROM)))
;						 (cond
;						  ;; NB inverse may have already been recorded, in which case don't
;						  ;; redundantly record it in the other direction
;						  ((not (member explanation (get-explanations clone slot val)
;								:test #'equal))
;						   (record-explanation-for target val explanation)))))
;					   (vals-in slotvals))))))
			   slotsvals)))

		   (cond ((am-in-prototype-mode) ; 1.4.5.17 - allow cloning *within* a prototype too
			  (add-val clone '#$prototype-participant-of (curr-prototype) t *global-situation*))))) ; install-inverses = t; Note in GLOBAL situation
	     clones))			; inverse (C instances I) installed

#|
New: 1/10/02 - copy *all* explanations over. **NOTE** These will be deposited in the *GLOBAL* situation,
QUESTION: Why do we do this?
For AURA, the only purpose of explanations is to note the source node(s).
Suppose		Arm1-parts->Hand1-parts->Finger2
		Body2-parts->Arm2-parts->Hand2-parts->Finger2
					 (cloned-from Arm1 Arm2)
	 Now    Person3-parts->Body3-parts->Arm3-parts->Hand3-parts->Finger3
							(cloned-from Body2 Body3)
The question is, do we also need to clone the expln:    (cloned-from Arm1 Arm3)		? [1]
Note we *do* clone cloned-from links, so we have:    Arm3 cloned-from (Arm2 Arm1)
						     Hand3 cloned-from (Hand2 Hand1)
	triple-expanded-from will say Body3, and Arm3 if [1] is done.
	get-supports will say Arm, Body, but the check to remove Body if Body3 is deleted will be lost.
	get-support-details will say Hand1-parts->Finger2 -- it only shows the ORIGINAL source, not the intermediate

because, cloning is necessarily done in the global situation ONLY (see (in-situation *Global ...) in unify-in-prototype
earlier)
10/25/07 -
However, if we *don't* record the cloned-from explanations, will KM re-apply the prototype Arm1 onto Arm3,
which will recreate them? e.g., that (Arm3 parts Hand3) is cloned-from Arm1? The answer is no (which is bad),
because Arm3 is already noted as (clone-built-from Arm1) which blocks re-cloning. It's bad as we'll have lost
additional information in the explanation database (that Arm1 was cloned onto Arm3), needed for
triple-expanded-from.
Thus, we need to either copy the clone-built-from info AND the explanations (as we do now), OR not copy either.
But we can't do one without the other.
Note we also need to record explanations attached to "traditional" structures, e.g., build with (a-prototype ...)
form. However, we can ignore these if they were inherited [4], as they will be reinherited when recomputed. LATER:
No, let's copy them all and not rely on recomputation.
[5] Note if we are doing without-bookkeeping, then the goal is the clone is an IDENTICAL COPY of the original, for
    the purposes of editing in AURA. As a result, in this special situation, we *do* need to copy the WHOLE
    explanation database over. In particular, we need to preserve the added-at links.
[6] 3/2/08: I appear to have decided NOT to propogate the added-at explanations to clones after all in KM 2.1.7
    back in October 2007. I guess the rationale is that if the SME does added-at (x y z), then (x y z) is
    cloned to (a b c), (a b c) really should just be explained by (x y z) (it's not really true the SME added-at
    (a b c) directly). Of course, if we clone-without-bookkeeping (which DOES copy added-at) then save the
    new graph as a subclass of the original, then we will have kept some added-at links from the original.
    I guess that's ok.
    HLO-2362 - actually it is ok, and we can always copy the added-at links. Just because a clone has an added-at
    explanation doesn't mean the link was added-at that clone; rather the source class is in the added-at structure.
[7] There's an issue of whether we copy the explanations in *Global or not during cloning. Here it looks like we *don't*;
    This is very strange, as participant has no explanations in the local situation (?).

|#
;      (km-format t "mapping-alist = ~a~%" mapping-alist)
    (cond
     ((and (or *record-explanations* *record-explanations-for-clones*)
	   *propogate-explanations-to-clones*)
;      (format t "put-explanations...~%")
      (let ((*dereferencing-on* *dereference-explanations-during-cloning*))		; [4]
       (mapc #'(lambda (participant-dot-clone)
		(let* ((participant (first participant-dot-clone))
		       (clone0 (rest participant-dot-clone))
		       (isv-explanations (get-all-explanations participant nil)) ; slot=nil   ; [7] - Combines both local and global explanations
; OLD		       (filtered-isv-explanations
;			(cond (without-bookkeeping isv-explanations) ; [5]
;			      (t (remove-if #'(lambda (isv-explanation) ; [6]
;						(eq (explanation-type (explanation-in isv-explanation)) '#$added-at))
;					    isv-explanations))))
; NEW		       (filtered-isv-explanations isv-explanations) ; NEW - HLO-2362 and HLO-1802 we need added-at copied
		       (filtered-isv-explanations
			(cond (without-bookkeeping isv-explanations)
			      (t (remove-if #'(lambda (isv-explanation)
						(let* ((triple (triple-in isv-explanation))
						       (slot (second triple)))
;						(format t "isv-explanation = ~a~%" isv-explanation)
						(and (eq slot '#$instance-of) 	; for instance-of, ONLY keep (added-at ...) and (a Foo (@ ...)) explns
						     (let ((explanation (explanation-in isv-explanation)) ; see knowledge-revision/oct11-problem.txt
							   (instance (first triple))
							   (class (third triple)))
						       (or (eq (explanation-type explanation) '#$cloned-from) 	; remove all copied cloned-from explanations for instance-of links
							   (and (pairp explanation) (eq (first explanation) '#$a)) ; remove all copied (a X) explanations for instance-of links
							   (not (member class (get-vals instance '#$instance-of))))) ; triple doesn't even exist now!
;						     (or (km-format t "DEBUG: Not cloning explanation for ~a (redundant/not valid)...~%" triple) t)
						     )))
					    isv-explanations))))

		       (old-isv-explanations (get-all-explanations clone0 nil))) ; may be some from [2] - here we get from local...
;			 (km-format t "prototype = ~a, prototype0 = ~a~%" prototype prototype0)
;			 (km-format t "participant = ~a, clone0 = ~a~%" participant clone0)
;			 (km-format t "mapping-alist = ~a~%" mapping-alist)
;			 (km-format t "old-isv-explanations = ~a~%" old-isv-explanations)
;			 (km-format t "isv-explanations = ~a~%" isv-explanations)
;			 (km-format t "filtered-isv-explanations = ~a~%" filtered-isv-explanations)

		  (cond (filtered-isv-explanations
			 (put-explanations clone0 nil
			  (append old-isv-explanations
;			   (remove-clone-cycles (sublis  mapping-alist filtered-isv-explanations)))))))) ; [5] ... and assert in local...
		           (remove-clone-cycles (sublis* mapping-alist filtered-isv-explanations)))))))) ;smh 2012-06-9
	     mapping-alist))))

;      (add-val clone-of-prototype '#$cloned-from prototype nil *global-situation*) ; install-inverses = nil [1]
	; NEW: add cloned-from links for *all* participants. Then we can get a constant handle on them.
;    (format t "add cloned-from links...~%")
       (cond
	(*add-cloned-from-links*
	 (mapc #'(lambda (protopart-dot-clone)
		   (let ( (protopart (first protopart-dot-clone))
			 (clone (rest protopart-dot-clone)) )
		     (add-val clone '#$cloned-from protopart t)))  ; cloned-from is global, so will go in global sitn
	       mapping-alist)))
       (add-val clone-of-prototype *clone-built-from-slot* prototype) ; restating default extra args unnecessary

       ;;; NOW classify the nodes
;      (km-format t "*classification-enabled* = ~a~%" *prototype-classification-enabled*)
;      (km-format t "Now classifying the clones ~a...~%" (mapcar #'first clones))

;       (format t "classify...~%")
;;; This is a bit drastic, as it calls arbitrary classification reasoning on every prototype node after every
;;; cloning operation :-(. Maybe we can tone it down a bit (?):
      (let ((*use-inheritance* nil)	; new - tone it down a bit
	    (*use-prototypes* nil)	; new - tone it down a bit
	    (*recursive-classification* t) ; Note: We *do* need to allow this as a subgoal of classification, else an unclassified clone slips through.
	    )				   ; The (*use-prototypes* nil)	ensures we won't get any deeper in the reasoning. See test-suite/prototypes5.km
	 (mapc #'classify (mapcar #'first clones)))

;       (format t "Done!~%")
       (values clone-of-prototype mapping-alist))))))) ; return clone of prototype

#| ======================================================================
build-clones: Redefined: rather than walking the clone graph,
we know all the proto-instances already as they're stored on the prototype-participants slot of the
clone root!
RETURNS TWO VALUES:
	- a list of (<clone> <slotsvals>) pairs
	- the clone-instance mapping, a list of (<protoname> . <clone>) acons's.
======================================================================

This was originally meant to allow prototypes to include some situation-specific components, but this generates errors
when cloning!
[1] NO!!!!! You are *not* allowed to do any reasoning on PROTOTYPES! Bad!!!!
    In fact we get away with it because classification is disabled during cloning, but still let's change it!
     In particular it's still leaving an explanation for prototype-participants in the expln db (urgh)
|#
(defun build-clones (prototype &key including-extra-slots)
; [1] (let* ( (prototype-participants (km-int `#$(the prototype-participants of ,PROTOTYPE) :fail-mode 'error)) ; includes prototype	e.g. (_ProtoCar1 _ProtoWheel2)
   (let* ((prototype-participants (get-vals prototype '#$prototype-participants)) ;includes prototype eg (_PCar1 _PWheel2)
	  (clones (mapcar #'(lambda (prototype-participant)
				   (cond ((anonymous-instancep prototype-participant)
					  (create-instance-name (first (immediate-classes prototype-participant))))
					 (t prototype-participant)))
			       prototype-participants))
	  (mapping-alist (pairlis prototype-participants clones)) )		; (pairlis '(_ProtoCar1 _ProtoWheel2) '(_Car3 _Wheel4)) ->
     (cond ((null prototype-participants)
	    (report-error 'user-error "(clone ~a): No prototype-participants declared for this prototype!~%" prototype))
	   (t
	    (values (remove nil (mapcar #'(lambda (prototype-participant) ; ((_ProtoCar1 . _Car3) (_ProtoWheel2 . _Wheel4))
				    (build-clone prototype-participant mapping-alist ; nil: some prototype-participants need no assertions
						 :including-extra-slots including-extra-slots))
				prototype-participants))
		    mapping-alist)))))

#|
Patch for prototype reasoning
RETURNS: (<clone-root> <clone-slotsvals>)
:including-extra-slots allows user to override (hence clone) slots in *unclonable-slots*, e.g., coordinate info slots
[1] Normally cloned-from and clone-built-from point to other prototypes OUTSIDE the current prototype being cloned,
    and so these links are simply copied. However, it's possible they point WITHIN the prototype itself, e.g,

        [[Person]] -parent-> [Person]
	    <--cloned-from----/

For these links it's critical we *don't* copy the cloned-from link, as it results in an inverse has-clones link
on the (non-prototype) instance clone. The test [1] removes such pointers, but leaves the rest preserved.
|#
(defun build-clone (prototype mapping-alist &key including-extra-slots)
  (cond
   ((anonymous-instancep prototype)    ;;; NEW: Important that slotvals on *named* instances are NOT cloned
    (let* ((clone (rest (assoc prototype mapping-alist)))
	   (slotsvals (get-slotsvals prototype :situation *global-situation*)) ; now prototypes are *only* in Global
	   (new-slotsvals (remove nil
			   (mapcar #'(lambda (slotvals)
				       (let ((slot (slot-in slotvals)))
					 (cond ((and (member slot *unclonable-slots*)
						     (not (member slot including-extra-slots))) nil)
;					       ((member slot '#$(cloned-from clone-built-from))
					       ((member slot *slots-with-nonparticipant-skolems*)	; more general 1/7/11
						(let ((vals-outside-prototype
						       (remove-if #'(lambda (val)
								      (assoc val mapping-alist))  ; [1]
								  (vals-in slotvals))))
						  (cond (vals-outside-prototype
							 (make-slotvals slot vals-outside-prototype)))))
					       (t slotvals))))
				   slotsvals))))
;     (km-format t "slotsvals = ~a~%" slotsvals)
      (cond (new-slotsvals
;	     (list clone (sublis mapping-alist (dereference new-slotsvals)))))))))
	     (list clone (sublis* mapping-alist (dereference new-slotsvals)))))))))	; smh

;;; ======================================================================

;;; NOTE: This records the KM commands which created the prototype, purely as comments
;;; for a showme command. These are *not* retained by (save-kb ...).
(defun add-to-prototype-definition (prototype expr)
  (let ( (definition-so-far (get prototype 'definition)) )
    (km-setf prototype 'definition (append definition-so-far (list expr)))))

;;; ======================================================================
;;; NOT part of KM's inference engine, but a utility for tracing the has-clones links
;;; ======================================================================

(defun node-cloned-to (f) (remove-duplicates (get-vals f '#$has-clones))) ; NB get-vals may contain dups

;;; ======================================================================
;;;   NODES-CLONED-TO: Also see knowledge-revision/propogating-changes/README.txt
;;; ======================================================================
#|
If nodes is a pair, it returns a list of pairs of corresponding clones
e.g., (nodes-cloned-to '#$(_N1 _N2)) -> ((_n3 _n4) (_n6 _n7))
where _n1 _n2 are in prototype 1, _n3 _n4 are in prototype 2, and _n6 _n7 are in prototype 3.

Revised algorithm:
   (i) find all the clones (_CNodes) of nodes (_PNodes)
   (ii) Find all the explanations for all the clones (i.e., <expn> for ALL triples (:triple _CNode ?any ?any) <expn>
  (iii) Find the signatures of all the different "cloning operations". If the explanation is
	  (cloned-from _PRoot _CRoot _CNode) then the signature is (_PRoot _CRoot)
  (iv) Step through and see the mappings
I extended the explanation DB to include the necessary information to support this

Consider: Prototype _Foo1, containing (_Foo1 _Bar1), is cloned *twice* onto_Foo2 and _Foo3 respectively
USER: (nodes-cloned-to '(_Foo1 _Bar1))
isv-explanations =
   (_Foo2 parts _Bar5 (cloned-from _Foo1 _Foo2 _Foo1))
   (_Foo3 parts _Bar7 (cloned-from _Foo1 _Foo3 _Foo1))
   (_Bar5 instance-of Bar (cloned-from _Foo1 _Foo2 _Bar1))
   (_Bar5 parts-of _Foo2 (cloned-from _Foo1 _Foo2 _Bar1))
   (_Bar7 instance-of Bar (cloned-from _Foo1 _Foo3 _Bar1))
   (_Bar7 parts-of _Foo3 (cloned-from _Foo1 _Foo3 _Bar1))
RETURNS:
'((_Foo2 _Bar5) (_Foo3 _Bar7))
|#

;;; ------------------------------ STANDARD CACHING WRAPPER

(defvar *nodes-cloned-to-keys* nil)
(defvar *nodes-cloned-to-caching* nil)

(defun nodes-cloned-to (nodes0 &key clones-of-interest)
; (let ((start-time (get-internal-run-time)))
   (prog1
       (cond
	((or clones-of-interest		; cache only the full (unrestricted) answer
	     (not *nodes-cloned-to-caching*))
	 (nodes-cloned-to0 nodes0 :clones-of-interest clones-of-interest))
	(t (let* ((key (intern (format nil "~a" nodes0) *km-package*))
		  (cached-answer (get key 'nodes-cloned-to)))
	     (cond (cached-answer
		    (cond ((neq cached-answer 'no) cached-answer)))
		   (t (let* ((answer (nodes-cloned-to0 nodes0)))
;			(km-format t "Retrieve from cache: (nodes-cloned-to0 ~a) -> ~a~%" nodes0 answer)
			(setf (get key 'nodes-cloned-to) (or answer 'no))
			(push key *nodes-cloned-to-keys*)
			answer))))))
;     (km-format t "[~,2f sec for (nodes-cloned-to ~a)~%"
;		(/ (- (get-internal-run-time) start-time) internal-time-units-per-second)
;		nodes0))
   ))

(defun clear-nodes-cloned-to-cache ()
  (mapc #'(lambda (key) (setf (get key 'nodes-cloned-to) nil)) *nodes-cloned-to-keys*)
  (setq *nodes-cloned-to-keys* nil)
  t)

;;; ------------------------------

(defun nodes-cloned-to0 (nodes0 &key clones-of-interest)
 (let ((nodes (dereference nodes0)))
  (cond
   ((notevery #'protoinstancep nodes)
   (report-error 'user-error "ERROR! nodes-cloned-to: ~a is/are not instances in a prototype!~%"
		  (remove-if #'protoinstancep nodes)))
   ((not (= (length (remove-duplicates nodes)) (length nodes0)))
    (report-error 'user-error
	  "nodes-cloned-to: ~a are not all distinct nodes (some are bound; they dereference to ~a)~%"
	  nodes0 nodes))
   (t (let* ((original-prototypes (gets-vals nodes '#$prototype-participant-of))
	     (original-prototype (first original-prototypes)) ; original-prototypes must be a singleton (checked below)
;	    (original-prototypes (km-int `#$(the prototype-participant-of of ,(VALS-TO-VAL NODES))))
	    )
	(cond
	 ((not (singletonp original-prototypes))
	  (report-error 'user-error "nodes-cloned-to: ~a should belong to the same prototype, but belong to multiple ones ~a!~%" nodes original-prototypes))
	 (t (let* ((clones0 (gets-vals nodes '#$has-clones))
		   (clones (cond (clones-of-interest (intersection clones0 clones-of-interest)) (t clones0)))
		   (isv-explanations (dereference
				      (remove-if-not #'(lambda (isv-explanation)
							 (let ((explanation (explanation-in isv-explanation)))
							   (and (eq (explanation-type explanation) '#$cloned-from)
								(or (member (fourth explanation) nodes) ; src protonode
								    (and (null (fourth explanation)) ; backwards compat.
									 (eq (second explanation) original-prototype))))))
						     (my-mapcan #'get-explanation-data clones))))
		   (clone-operation-ids
		    (remove-duplicates
		     (remove nil
		      (mapcar #'(lambda (isv-explanation)
				  (let ((explanation (explanation-in isv-explanation))); (cloned-from _PRoot _CRoot _PNode)
				    (list (second explanation) (third explanation))))  ; (_PRoot _CRoot)
			      isv-explanations))
		     :test #'equal)))
;	      (km-format  t "isv-explanations = ~%~{   ~a~%~}" isv-explanations)
;	      (km-format  t "clone-operation-ids = ~a~%" clone-operation-ids)
;	      (km-format  t "~a clone-operation-ids~%" (length clone-operation-ids))
	      (remove-duplicates
	       (mapcan #'(lambda (clone-operation-id)
			   (collect-clonesets nodes isv-explanations clone-operation-id))
		       clone-operation-ids)
	       :test #'equal :from-end t)))))))))

;;; --------------------

;;; Returns a set of (Clone1...CloneN) matching (Node1...NodeN) created under CLONE-OPERATION-ID
(defun collect-clonesets (nodes isv-explanations clone-operation-id)
;  (km-format t ".")
  (let ((clonesets  	; a list of N elements (<Clones of Node1>...<Clones of NodeN>) under CLONE-OPERATION-ID
	 (mapcar #'(lambda (node)
		     (remove-duplicates
		      (remove nil (mapcar #'(lambda (isv-explanation)
					       (find-clone-of-node node isv-explanation clone-operation-id))
					  isv-explanations))))
		 nodes)))
;		 (km-format t "clone-operation-id = ~a, clonesets = ~a~%" clone-operation-id clonesets)
    (permute-clonesets clonesets)))

;;; Look in isv-explanation for a clone of node created under clone-operation-id. Can return NIL if not found
(defun find-clone-of-node (node isv-explanation clone-operation-id)
  (let ((cloned-from (first clone-operation-id))
	(expanded-from (second clone-operation-id)))
    (case (length (explanation-in isv-explanation)) ; returns the CLONE of NODE under CLONE-OPERATION-ID
; Awaiting implementation following modification to get-explanations
;		         (5 (or (minimatch1 isv-explanation
;				     `(?clone ?any ?any (#$cloned-from ,cloned-from ,expanded-from ,node ?any)))
;				(minimatch1 isv-explanation
;				     `(?any ?any ?clone (#$cloned-from ,cloned-from ,expanded-from ?any ,node)))))
#|
; Inefficient (?) let's reimplement!
      (4 (or (minimatch1 isv-explanation ; backwards compatibility
			 `(?clone ?any ?any (#$cloned-from ,cloned-from ,expanded-from ,node)))
	     ; This case if only the inverse, but not forward, explanation is stored (shouldn't happen)
	     (let ((clone (minimatch1 isv-explanation ; backwards compatibility
				      `(?any ?any ?clone (#$cloned-from ,cloned-from ,expanded-from ?any)))))
	       (cond ((and clone (kb-objectp clone) (member node (get-vals clone '#$cloned-from))) clone)))))
      (3				; backwards compatibility
       (let ((clone (minimatch1 isv-explanation `(?clone ?any ?any (#$cloned-from ,cloned-from ,expanded-from)))))
	 (cond ((and clone (kb-objectp clone) (member node (get-vals clone '#$cloned-from))) clone))))
|#
; REIMPLEMENTED
      (4 (cond	; Backwards compatibility
		; (minimatch1 isv-explanation (?clone ?any ?any (#$cloned-from ,cloned-from ,expanded-from ,node)))
	       ((equal (fourth isv-explanation) `(#$cloned-from ,cloned-from ,expanded-from ,node))
		(first isv-explanation))
		; This case if only the inverse, but not forward, explanation is stored (shouldn't happen)
	       (t (let* (; (clone (minimatch1 isv-explanation ; backwards compatibility `(?any ?any ?clone (#$cloned-from ,cloned-from ,expanded-from ?any)))))
			 (explanation (explanation-in isv-explanation))
			 (clone (cond ((and (eq (first explanation) '#$cloned-from)
					    (eq (second explanation) cloned-from)
					    (eq (third explanation) expanded-from))
				       (third isv-explanation)))))
		    (cond ((and clone (kb-objectp clone) (member node (get-vals clone '#$cloned-from))) clone))))))
      (3				; backwards compatibility
;       (let ((clone (minimatch1 isv-explanation `(?clone ?any ?any (#$cloned-from ,cloned-from ,expanded-from)))))
        (let* ((explanation (explanation-in isv-explanation))
	       (clone (cond ((and (eq (first explanation) '#$cloned-from)
				  (eq (second explanation) cloned-from)
				  (eq (third explanation) expanded-from))
			     (first isv-explanation)))))
	  (cond ((and clone (kb-objectp clone) (member node (get-vals clone '#$cloned-from))) clone))))

   (t (report-error 'program-error "Invalid explanation length in nodes-cloned-to!~%")))))

;;; (permute-cloneset '((a) (c))) -> ((a c))
;;; (permute-cloneset '((a b) (c))) -> ((a c) (b c))
;;; (permute-cloneset '((a b) (c))) -> ((a c) (b c))
;;; (permute-cloneset '((a) nil)) -> ((a nil))
;;; (permute-cloneset '((a b) nil (c d))) -> ((a nil c) (a nil d) (b nil c) (b nil d))
(defun permute-clonesets (sets)
  (cond ((endp sets) (list nil))
	(t (let ((set (first sets)))
	     (mapcan #'(lambda (set-el)
			 (mapcar #'(lambda (rest-set)
				     (cons set-el rest-set))
				 (permute-clonesets (rest sets))))
		     (or set '(nil)))))))

(defun node-cloned-from (f) (remove-duplicates (get-vals f '#$cloned-from)))
(defun node-cloned-from-originally (f) (remove-duplicates (remove-if #'node-cloned-from (get-vals f '#$cloned-from))))


;;; Transitive closure
;;; added by MW, 2011-08-08: this is very inefficient...
;;; calls frequently need more than 40 secs, and some
;;; don't terminate at all. I have replaced that with a
;;; (hopefully correct) more efficient version. Confirmed
;;; by PEC, mail from 2011-08-06.
#+:ignore
(defun node-cloned-from* (f &key done)
  (let ((sources (get-vals f '#$cloned-from)))
    (remove-duplicates
     (append sources
	     (my-mapcan #'(lambda (x)
			    (cond ((member x done)
; Seems that loops can occur for obscure reasons
;			   (km-format t "ERROR! node-cloned-from*: Looping on cloned-from for ~a ~a; stopping...~%"
;					      x (cons x done))
				   )
				  (t (node-cloned-from* x :done (cons x done)))))
			sources)))))

;;; added by MW, 2011-08-08
(defvar *cloned-hash* (make-hash-table))
;;; added by MW, 2011-08-08
(defvar *node-visited-hash* (make-hash-table))
;;; added by MW, 2011-08-08
(defvar *node-result-hash* (make-hash-table))

;;; added by MW, 2011-08-08: more efficient version,
;;; see comments above
(defun compute-transitive-closure-of-slot (rel f &key done)

  (clrhash *cloned-hash*)
  (clrhash *node-visited-hash*)
  (clrhash *node-result-hash*)

  (let ((agenda (list f)))
    (loop
      (let ((node (pop agenda)))
	(cond ((not node)
	       (return-from compute-transitive-closure-of-slot
		 ;; weird - if I reverse the result before returning it,
		 ;; then this speeds up MTS test suite by two thirds!
		 ;; so, lets do it:
		 (reverse done)))

	      ((not (gethash node *node-visited-hash*))
	       (setf (gethash node *node-visited-hash*) t)
	       (let ((sources (or (gethash node *cloned-hash*)
				  ;; we are deliberatly asking KM again
				  ;; here, even if nil was already computed
				  ;; and stored once in the hash table (note
				  ;; that usually one would use the second
				  ;; value returned by gethash, whether the
				  ;; key was found or not - it may be the
				  ;; case that the node has no cloned-from vals?)
				  (setf (gethash node *cloned-hash*)
				    (get-vals node rel)))))
		 ;;(pprint (list node sources))
		 (dolist (source sources)
		   (unless (gethash source *node-result-hash*)
		     (setf (gethash source *node-result-hash*) t)
		     (push source done)
		     (push source agenda))))))))))

;;; added by MW, 2011-08-08: optimization
(defun node-cloned-from* (f &key done)
  (compute-transitive-closure-of-slot '#$cloned-from f :done done))

;;; Synonym for above
(defun cloned-from* (f &key done) (node-cloned-from* f :done done))

;;; Transitive closure of #$clone-built-from
;;; added / ignored by MW, 2011-08-08: see comments for node-cloned-from*,
;;; analogous change here
#+:ignore
(defun clone-built-from* (f &key done)
  (let ((sources (get-vals f '#$clone-built-from)))
    (remove-duplicates
     (append sources
	     (my-mapcan #'(lambda (x)
			    (cond ((member x done))
				  (t (clone-built-from* x :done (cons x done)))))
			sources)))))

;;; added by MW, 2011-08-08: optimization
(defun clone-built-from* (f &key done)
  (compute-transitive-closure-of-slot '#$clone-built-from f :done done))

;;; ======================================================================

;;; [1] If A clones to B clones to C (where A,B,C are triples), then (triple-cloned-from C) -> (A B)
;(defun triple-cloned-from (triple)
;  (let* ((f (dereference (first triple)))
;	 (s (second triple))
;	 (v (dereference (third triple)))
;	 (f-protos (node-cloned-from f))
;	 (v-protos (node-cloned-from v)))
;    (mapcan #'(lambda (f-proto)
;		(let ((vals (get-vals f-proto s :situation *global-situation*)))
;		  (mapcar #'(lambda (val)
;			      (list f-proto s val))
;			  (intersection vals (cons v v-protos))))) ; allow for v to be named instances also
;	    f-protos)))

#|
Rewritten by Sunil Mishra 2/29/08:
triple-cloned-from fails on inputs such as (_Equation-Set90 equation-symbol (:pair 'x_1 _Speed-Value91)).
In fact, if the value is non-atomic, with error reporting turned on, triple-cloned-from will always given an error.
The following code replaces the existing triple-cloned-from. For list values containing anonymous instances,
triple-cloned-from-complex* carefully considers each possible filler for that value in a prototype, then filters
out all non-existent triples. Other cases are handled through triple-cloned-from-simple*.

ALGORITHM for (triple-cloned-from (<x> <r> <y>):
  1. Find all <source-x>s that <x> was cloned-from
  2. Find all <source-y>s that <y> was cloned-from
  3. Select from these to find all pairs (<source-x> <source-y>) such that:
	a. <source-x> and <source-y> are in the same prototype <p>
	b. <source-x> and <source-y> are connected by relation <r>, i.e., (<source-x> <r> <source-y>) is in <p>
     Return all such pairs found.

(There are also some refinements for some special cases such as handling property values)
|#
;;; [1] If TripleA clones to TripleB clones to TripleC, then (triple-cloned-from TripleC) -> (TripleA TripleB)
(defun triple-cloned-from (triple)
  (let* ((f (dereference (first triple)))
	 (s (second triple))
	 (v (dereference (third triple))))
    (if (and (consp v) (some #'anonymous-instancep (flatten v)))
	(triple-cloned-from-complex* f s v)
	(triple-cloned-from-simple* f s v))))

(defun triple-cloned-from-simple* (f s v)
  (let* ((f-protos (node-cloned-from f))
	 (v-protos (if (anonymous-instancep v) ; allow for v to be non-anonymous instances
		       (node-cloned-from v)
		       (list v))))
    (select-real-triples f-protos s v-protos)))

;;; 8/10/12 - Updated to remove-duplicates and also avoid memory overflow with ridiculously many permutations
(defun triple-cloned-from-complex* (f s v)
  (let* ((f-protos (node-cloned-from f))
	 (v-content (remove-duplicates (remove-if-not #'anonymous-instancep (flatten v))))
	 (v-content-substs (mapcar (lambda (v-node)
				     (mapcar (lambda (v-node-proto) (cons v-node v-node-proto))
					     (node-cloned-from v-node)))
				   v-content))
	 (v-content-permutations
	  (cond ((or (<= (length v-content) 5) ; quick lookahead
		     (let ((n-permutations (apply #'* (mapcar #'length v-content-substs))))
		       (cond ((<= n-permutations 30000) t)
			     (t (km-format t "DEBUG: Too many permutations to check doing:~% (triple-cloned-from-complex* ~a ~a ~a)
  Assuming result is NIL...~%" f s v)))))
		 (permute v-content-substs))))
	 (v-protos (mapcar (lambda (v-permutation)
;			     (sublis  v-permutation v))
			     (sublis* v-permutation v)) ; smh 2012-06-19
			   v-content-permutations)))
    (select-real-triples f-protos s v-protos)))

;;; GIVEN a set of f, a slot, and a set of v
;;; RETURN ONLY the (f slot v) which actually exist in the KB (are "real")
(defun select-real-triples (fs s vs)
    (mapcan #'(lambda (f)
		(let ((vals (cond ((protoinstancep f) ; all prototype info necessarily in the global situation
				   (get-vals f s :situation *global-situation*))
				  (t (get-vals f s)))))
		  (mapcan #'(lambda (v)
			      (when (member v vals :test #'equal)
				(list (list f s v))))
			  vs)))
	    fs))

;;; ======================================================================

;;; Do similar thing for triple-cloned-to
;(defun triple-cloned-to (triple)
;  (let* ((f (dereference (first triple)))
;	 (s (second triple))
;	 (v (dereference (third triple)))
;	 (f-clones (node-cloned-to f))
;	 (v-clones (node-cloned-to v)))
;    (cond
;     ((in-prototype triple)		; includes checks the triple exists and is part of a prototype
;      (mapcan #'(lambda (f-clone)
;	        (let ((vals (get-vals f-clone s)))		; is this ok?
;		  (mapcar #'(lambda (val)
;			      (list f-clone s val))
;			  (intersection vals (cons v v-clones)))))	; allow for v to be named instances also
;	      f-clones)))))

;;; [1] If A clones to B clones to C, then (triple-cloned-to C) -> (A B)
(defun triple-cloned-to (triple)
  (let* ((f (dereference (first triple)))
	 (s (second triple))
	 (v (dereference (third triple))))
    (if (and (consp v) (some #'anonymous-instancep (flatten v)))
	(triple-cloned-to-complex* f s v)
	(triple-cloned-to-simple* f s v))))

(defun triple-cloned-to-simple* (f s v)
  (let* ((f-clones (node-cloned-to f))
	 (v-clones (if (anonymous-instancep v) ; allow for v to be non-anonymous instances
		       (node-cloned-to v)
		       (list v))))
    (select-real-triples f-clones s v-clones)))

(defun triple-cloned-to-complex* (f s v)
  (let* ((f-clones (node-cloned-to f))
	 (v-content (remove-duplicates (remove-if-not #'anonymous-instancep (flatten v))))
	 (v-content-substs (mapcar (lambda (v-node)
				     (mapcar (lambda (v-node-clone) (cons v-node v-node-clone))
					     (node-cloned-to v-node)))
				   v-content))
	 (v-content-permutations
	  (cond ((or (<= (length v-content) 5) ; quick lookahead
		     (let ((n-permutations (apply #'* (mapcar #'length v-content-substs))))
		       (cond ((<= n-permutations 30000) t)
			     (t (km-format t "DEBUG: Too many permutations to check doing:~% (triple-cloned-to-complex* ~a ~a ~a)
  Assuming result is NIL...~%" f s v)))))
		 (permute v-content-substs))))
	 (v-clones (mapcar (lambda (v-permutation)
;			     (sublis  v-permutation v))
			     (sublis* v-permutation v)) ; smh 2012-06-19
		   v-content-permutations)))
    (select-real-triples f-clones s v-clones)))

;; ======================================================================

;;; ----------------------------------------------------------------------

#|
(triple-cloned-from-originally <triple>):
We find the triples Ts that <triple> was triple-cloned-from, and remove all the "pass through" triples that:
 a. themselves rely on another triple in Ts
 b. have no added-at supports themselves

ALGORITHM for (triple-cloned-from-originally <triple>):
 1. Find all the (triple-cloned-from <triple>) -> (<t1> <t2> ...). (<t1> etc. is an originating triple for <triple>)
 2. If <t1> was itself triple-cloned-from <t2>, then drop <t1> (providing <t1> wasn't also locally added-at in its containing prototype).
    Check this for all the <t1> ... <tn>.
    As a result, we are left with:
        a. just the "root" triples of the triple-cloned-from tree, PLUS
	b. any intermediate triples that were locally asserted (added-at)

[1] If A clones to B clones to C, then (triple-cloned-from-originally C) -> (A), as B is an intermediate triple
SUPPOSE: (f s v) -clone-> (f1 s1 v1) -clone-> (f2 s2 v2)
THUS: (triple-cloned-from (f2 s2 v2)) -> (f s v) (f1 s1 v1)
      (triple-cloned-from (f1 s1 v1)) -> (f s v)

[2] - This doesn't work if there's a cycle in the KB (as can easily arise - see
	my notes in directory km/knowledge-revision/triple-expanded-from/). It also doesn't
	take account of triples which may be clones of clones, but are also supported by a SME add action,
	or a unification, or from the base KB. For now let's ignore all these "intermediate supports".
[4]	8/25/08 - No, got bitten directly by this HLO-2362 - so fix it!!!
[5]    A (<triple> (added-at Foo "string")) explanation may be (i) about <triple> in Foo, or (ii) be about
       a CLONE in Bar of a <triple>' in Foo, with the explanation copied AND a separate (cloned-from <triple> <triple>')
       explanation stored. In this latter case, we don't want Bar to be labelled as an origination of <triple>,
       so we skip it and instead use the earlier ancestor (also collected in this function) in Foo.

[3]	If there's a cycle then include all the triples (except self).
SUPPOSE: (a b c) -clone-> (a1 b1 c1) -clone-> (a2 b2 c2) -clone-> (a b c)
THUS: (triple-cloned-from (a2 b2 c2)) -> (a b c) (a1 b1 c1)
      (triple-cloned-from (a1 b1 c1)) -> (a b c) (a2 b2 c2)
      (triple-cloned-from (a b c)) -> (a1 b1 c1) (a2 b2 c2)
RESOLUTION: Ignore source triples IF they're themselves cloned from something else AND they are not part of a cycle.
		(Thus for cycles, include all triples in the cycle as there's no notion of "most distant")

[6] New addition 7/21/11: If we are unable to find any Ts that meet this requirement (i.e., there is looping), we return all of them.
This occurred in AURA for some bizarre combination of cloning and inheritance. I don't remember the details but it was of the form:
	t1 cloned from t2 t3
	t2 cloned from t4
	t3 cloned from t4 t5
	t5 cloned from t1
	t4 cloned from t1 t2
The result is that [4] is not sufficient to find a "source" triple, so the fallback [6] collects more.

[7] There is a special case to consider:
    t1 in Cell: Cell has-part Plasma-membrane
    t2 in Animal-Cell: Animal-Cell has-part Animal-Plasma-membrane
t2 is triple-cloned-from t1. Question: Should (get-supports <t2>) -> Cell or not?
(a) From the official documentation of get-supports - return classes which prevent deletion of t2 - then
    we should return Cell
(b) But if get-supports is naively used to determine if t2 is local or inherited, it would cause
    problems as "What are the parts of an animal cell?" would list
	Parts common to all cells:
	    Animal-plasma-membrane
In fact, to avoid the problem (b), answer presentation uses some extra special processing to avoid
this problem, authored in get-hierarchy-information in pdqa/ap-knowledge.lisp. This filters out Cell
as the most general originating class.

Note the correct behavior here is (get-supports <t2>) -> Cell, Animal-Cell as in Animal-Cell there's
been some additional specialization - Animal-Cell is not just a "pass through" of a triple from Cell,
it adds in info.

KM(69): (let ((*old* nil)) (triple-cloned-from-originally '#$(_Plant-Cell58332 has-part _Cytoplasm58395) :silentp nil))
Keeping (_Cell82325 has-part _Cytoplasm604) (no sources-source-triples)
Discarding (_Plant-cell5965 has-part _Cytoplasm42728) (has sources-source-triple and no added-at info
Discarding (_Cell47942 has-part _Cytoplasm43950) (has sources-source-triple and no added-at info
Discarding (_Cell60339 has-part _Cytoplasm44340) (has sources-source-triple and no added-at info
Discarding (_Eukaryotic-Cell36856 has-part _Cytoplasm35755) (has sources-source-triple and no added-at info
Discarding (_Cell847 has-part _Cytoplasm68239) (has sources-source-triple and no added-at info
Discarding (_Cell325 has-part _Cytoplasm689) (has sources-source-triple and no added-at info
Discarding (_Cell64548 has-part _Cytoplasm64547) (has sources-source-triple and no added-at info
Discarding (_Eukaryotic-cell2547 has-part _Cytoplasm77704) (has sources-source-triple and no added-at info
|#
(defvar *new-triple-cloned-from-originally* t)	; Now switch it on

(defun triple-cloned-from-originally (triple &key (ignore-added-at-explanations *default-ignore-added-at-explanations*) (silentp t))
  (let ((source-triples (cond (*new-triple-cloned-from-originally* (triple-cloned-from* triple)) ; [1]	; purely for backwards compatibility testing
			      (t (triple-cloned-from triple))))) ; [1]
    (cond ((and (member triple source-triples :test #'equal)
		(not *new-triple-cloned-from-originally*))		; disable this for new version
	   (cond ((not silentp)
		  (km-format t "Cycle! ~a depends on itself! Returning all supporting triples (except self)...~%" triple)
		  (let* ((numbers (counts-to (length source-triples)))
			 (numbered-triples (transpose (list numbers source-triples))))
;		    (km-format t "numbered-triples = ~a~%" numbered-triples)
		    (mapc #'(lambda (n+tr)
			      (km-format t "	~a~13t~a [in ~a]~%" (first n+tr) (second n+tr) (protoclass (first (second n+tr)))))
			  numbered-triples)
		    (mapc #'(lambda (n+tr)
			      (let* ((n (first n+tr))
				     (tr (second n+tr))
				     (source-trs (triple-cloned-from tr))
				     (source-ns (mapcar #'(lambda (source-tr) (or (first (inv-assoc source-tr numbered-triples :test #'equal)) source-tr)) source-trs)))
				(cond ((null source-ns)
				       (km-format t "~a~3t(Not triple-cloned-from anything)~%" n))
				      (t (km-format t "~a~3t triple-cloned-from: ~a~%" n source-ns)))))
			  numbered-triples))))
	   (remove triple source-triples :test #'equal)) ; Cycle! [2,3]
#|[4]|#	  (t (let ((reduced-source-triples			; given (T1 T2 T3), remove T1 if it itself was cloned-from T2 or T3 etc.
		    (remove-if #'(lambda (source-triple)
				   (let ((sources-source-triples (triple-cloned-from source-triple)))
				     (cond
				      ((null sources-source-triples)
				       (cond ((not silentp) (km-format t "Keeping ~a [in ~a] (no sources-source-triples)~%" source-triple (protoclass (first source-triple))))))
				      ((or ignore-added-at-explanations ; (c) user didn't explicitly (re-)add this triple at this prototype
					      (let* ((f (first source-triple))
						     (s (second source-triple))
						     (v (third source-triple))
						     (explanations (append (get-explanations1 f s v)
									   (get-explanations1 v (invert-slot s) f))))
						(notany #'(lambda (explanation) ; (c) not explicitly (re-)added at this prototype
							    (and (eq (explanation-type explanation) '#$added-at)
								 (member (second explanation) ; avoid cloned added-at explns [5]
									 (prototype-classes source-triple))))
							explanations)))
				       (cond ((not silentp) (km-format t "Discarding ~a [in ~a] (has sources-source-triple and no added-at info)~%" source-triple (protoclass (first source-triple)))))
				       t)
				      (t (cond ((not silentp) (km-format t "Keeping ~a [in ~a] (has sources-source-triple but ALSO has local added-at info)~%" source-triple
									 (protoclass (first source-triple)))))))))
			       source-triples)))
#|[6]|#	       (cond ((null reduced-source-triples)
;		      (km-format t "source-triples = ~a, but no reduced source triples!~%" source-triples)
		      (let ((supported-source-triples
			     (cond (ignore-added-at-explanations source-triples)		; return the lot in this pathological case
				   (t (remove-if #'(lambda (source-triple)
						     (let* ((f (first source-triple))
							    (s (second source-triple))
							    (v (third source-triple))
							    (explanations (append (get-explanations1 f s v)
										  (get-explanations1 v (invert-slot s) f))))
						       (notany #'(lambda (explanation) ; (b) not explicitly (re-)added at this prototype
								   (and (eq (explanation-type explanation) '#$added-at)
									(member (second explanation) ; avoid cloned added-at explns [5]
										(prototype-classes source-triple))))
							       explanations)))
						 source-triples)))))
;			   (km-format t "supported-source-triples = ~a~%" supported-source-triples)
			(cond ((not silentp)
			       (cond (supported-source-triples (km-format t "Yikes! All supporting triples are themselves supported! Just returning those that have local added-at info...~%"))
				     (t (km-format t "Yikes! All supporting triples are themselves supported and none have local added-at info! Returning the lot...~%")))))
			(or supported-source-triples ; if looping, but >= 1 of the supported-source-triples are added-at, return those.
			    (remove-if-not #'self-reachable-triple source-triples))))  ; return the triples in the cycle if none are added-at (?).
		     (t reduced-source-triples)))))))

;;; ------------------------------

(defun self-reachable-triple (triple)
  (member triple (triple-cloned-from* triple) :test #'equal))

;;; (triple-cloned-from* <triple>) doesn't return <triple> itself UNLESS there's a cycle in the supports info, in which case it does
(defun triple-cloned-from* (triple)
  (triple-cloned-from0* (triple-cloned-from triple)))

(defun triple-cloned-from0* (triples &key done)
  (let ((triple (first triples)))
    (cond
     ((endp triples) done)
     ((member triple done :test #'equal)
      (triple-cloned-from0* (rest triples) :done done))
     (t (let* ((source-triples (triple-cloned-from triple))
	       (new-done (triple-cloned-from0* (rest triples) :done (cons triple done))))
	  (triple-cloned-from0* source-triples :done new-done))))))

;;; ------------------------------

;;; Returns the immediate classes (if any) of the triple arguments
(defun triple-classes (triple)
  (let* ((f (first triple))
	 (v (third triple))
	 (f-classes (cond ((kb-objectp f) (immediate-classes f))))
	 (v-classes (cond ((kb-objectp v) (immediate-classes v)))))
    (list f-classes v-classes)))

;;; ======================================================================

;;; INPUT: a triple which is in a prototype, or the root node of the prototype
;;; RETURNS: A list of the class(es) which the prototype is in.
;;; Strictly we should look at prototype-scope rather than instance-of links, but instance-of is ok.
;;; In any case, they should be the same, except when the prototype-scope is a structured class, .e.g,
;;     (instance-of (Car)) (prototype-scope ((the-class Car with (speed (*fast)))))
(defun prototype-classes (node-or-triple0)
  (let ((node-or-triple (dereference node-or-triple0)))
    (cond ((triplep node-or-triple) (prototype-classes (in-prototype node-or-triple))) ; includes error checking
	  ((not (prototypep node-or-triple))
	   (report-error 'user-error "(prototype-classes ~a): argument should be a prototype root node or a prototype triple but was not!~%" node-or-triple))
	  (t
	;  (get-vals node-or-triple '#$prototype-scope)
	;  (immediate-classes node-or-triple)
	; NO: immediate-classes may contain redundant classes in AURA as *built-in-remove-subsumers-slots* = nil
	   (get-vals node-or-triple '#$prototype-of)))))
#|
;;; This version uses the explanation database. However, I think it's possible to instead
;;; do this using the cloned-from tags instead, thus simplifying the explanation database.
;;; In this case, we can set *record-explanations-from-clones* to nil and save some explanation space.
(defun triple-cloned-from (f s v)
  (let* ((explanations (my-mapcan #'fourth (get-explanations f s v *global-situation*)))
	 (source-prototypes (mapcar #'second (remove-cloned-from-explns explanations)))
;	 (f-protoinstances0 (km-int `#$(the cloned-from of ,F)))
;	 (v-protoinstances0 (km-int `#$(the cloned-from of ,V)))
	 (f-protoinstances0 (get-vals f '#$cloned-from))
	 (v-protoinstances0 (get-vals v '#$cloned-from))
	 (f-protoinstances (remove-if-not #'(lambda (f-protoinstance)
					      (intersection (get-vals f-protoinstance '#$prototype-participant-of)
							    source-prototypes))
					  f-protoinstances0))
	 (v-protoinstances (remove-if-not #'(lambda (v-protoinstance)
					      (intersection (get-vals v-protoinstance '#$prototype-participant-of)
							    source-prototypes))
					  v-protoinstances0)))
;    (km-format t "explanations = ~a~%" explanations)
;    (km-format t "source-prototypes = ~a~%" source-prototypes)
;    (km-format t "f-protoinstances0 = ~a~%" f-protoinstances0)
;    (km-format t "v-protoinstances0 = ~a~%" v-protoinstances0)
;    (km-format t "f-protoinstances = ~a~%" f-protoinstances)
;    (km-format t "v-protoinstances = ~a~%" v-protoinstances)
    (mapcan #'(lambda (f-protoinstance)
		(let ((vals (get-vals f-protoinstance s :situation *global-situation*)))
		  (mapcar #'(lambda (val)
			      (list f-protoinstance s val))
			  (intersection vals (cons v v-protoinstances))))) ; allow for v to be named instances also
	    f-protoinstances)))
|#

#|
(save-prototype <protoroot>)
If :stream argument given, the caller must take responsibility for opening and closing the stream.
If :file argument given, the file is created and closed after writing.
If no keyword arguments are given, output is to standard-output.
If both :stream and :file are given, :stream takes precidence and :file is ignored.

RETURNS: TWO values:
  - The nodes in the prototype whose clone-built-from values changed, i.e., where recloning (reexpansion) is needed
    This may validly be NIL, if no clone-built-from values changed
  - If an error occurred, a string describing the error. To test for success, make sure this value in NIL

SIDE EFFECTS: None (the KB in memory is *not* changed - use trim-prototype to change the in-memory KB)

[1] The (cons ... (remove ...)) is to ensure that prototype is at the front of the list

NOTE:
For "normal" slots: only slot values which are also prototype-participant instances are written out.
For *prototype-bookkeeping-slots*, only values which are ALSO prototype participants (of some prototype, not
      necessarily this one) are written out (HLO-1690); Skolem instances (simple clones) are not.
(write-slotvals in writer.lisp implements the response to vals-to-show and *prototype-bookkeeping-slots*)

Example with essentials:
(save-prototype '#$_Car1 :essential-participants '#$(_Car1 _Engine1 _Cylinder1))
(save-prototype '#$_Cell161 :essential-participants
	'#$(_Cell161 _Ribosome195 _Cytoplasm193 _Chromosome186 _Organism185 _Plasma-membrane184))

[2] Are there any non-essential individuals cloned-from a prototype?
    If so, drop the clone-built-from link for that prototype to allow re-cloning. Otherwise, keep the
    clone-built-from link.
|#
(defvar *prototype-explanation-types-to-save* nil)

(defun save-prototype (prototype0 &key stream (file t) extra-assertions essential-participants (include-explanationsp t))
  (let ((prototype (dereference prototype0)))
  (cond
   ((not (prototypep prototype))
    (report-error 'user-error "(save-prototype ~a): ~a is not a prototype!~%" prototype prototype)
    (values nil (km-format nil "(save-prototype ~a): ~a is not a prototype!" prototype prototype)))
   ((and essential-participants (not (member prototype essential-participants)))
    (report-error 'user-error "(save-prototype ~a :essential-participants ...):~%   The root ~a must be a member of the essential-participants list, but wasn't!~%" prototype prototype)
    (values nil (km-format nil "(save-prototype ~a :essential-participants ...):~%   The root ~a must be a member of the essential-participants list, but wasn't!" prototype prototype)))
   (t (let*
        ((stream0 (or stream (tell file)))
;	 (classes (km `#$(the classes of ,PROTOTYPE)))
;	 (scope (km `#$(the prototype-scope of ,PROTOTYPE)))
	 (scope (get-vals prototype '#$prototype-scope))
	 (participants0 (get-vals prototype '#$prototype-participants))
;	 (participants0 (km `#$(the prototype-participants of ,PROTOTYPE))))
;;; NEW: Add warning and error recovery if this procedure is passed some invalid essentials
	(essential-participants0
	 (cond ((not (set-difference essential-participants participants0)) ; good! all essentials are participants
		essential-participants)
	       (t (report-error 'user-warning
			"(save-prototype ~a :essential-participants ~a):~%   ~a is/are not prototype-participant(s) of ~a, but should be!~%   Continuing, dropping those non-participants...~%"
			prototype0 essential-participants prototype
			(delistify (set-difference essential-participants participants0)) prototype)
		  (intersection essential-participants participants0)))))
;;; end NEW (except for 3 essential-participants -> essential-participants0 later)
	(multiple-value-bind
	 (new-essentials error-message)	; nil, if essential participants not given
	    (cond (essential-participants0 (find-essentials essential-participants0 :protoroot prototype
							   :participants participants0)))
	  (cond
	   (error-message (values nil (concat "Doing save-prototype: " error-message)))
	   (t (let*
		  ((participants (get-vals prototype '#$prototype-participants))
;		   (partitipants (km `#$(the prototype-participants of ,PROTOTYPE))) ; redo incase find-essentials patched buggy file
		   (participants-to-write-out ; [1] put prototype root first
		    (cons prototype (remove prototype (or new-essentials participants)))) ; write out either essentials or all
		   (non-essentials (ordered-set-difference participants new-essentials))
		   (partially-cloned-from ; nil if no essential participants given.
       ; partially-cloned-from = roots of prototypes cloned into prototype0 which are now only partially cloned in.
		    (cond (essential-participants0
;			   (km `#$(the prototype-participant-of of (the cloned-from of ,(VALS-TO-VAL NON-ESSENTIALS))))))) ; [2]
			   (remove-duplicates ; -> protoroots
			    (my-mapcan #'(lambda (prototype-participant)
					   (get-vals prototype-participant '#$prototype-participant-of))
				       (my-mapcan #'(lambda (non-essential)  ; -> protoinstances
						      (get-vals non-essential '#$cloned-from))
						  non-essentials)))))) ; [2]
	   ; partial-clone-roots = nodes that need to be re-expanded (participants built from partially cloned prototypes)
		   (partial-clone-roots
		    (remove-if-not #'(lambda (participant)
				       (intersection (get-vals participant '#$clone-built-from) partially-cloned-from))
				   new-essentials))
	   ; trimmed-expanded-from = additional essential nodes that need to be re-expanded (because some non-essential,
		; i.e., trimmed, node was derived from these essential nodes
		   ; NOTE: These were added per HLO-2608
		   (trimmed-expanded-from (remove-duplicates
					   (intersection (remove-duplicates (my-mapcan #'node-expanded-from non-essentials))
							 new-essentials)))
		   )
;		(km-format t "non-essentials = ~a~%" non-essentials)
		(cond
		 (essential-participants0 ; the below messages are meaningless if no essentials are given (= all nodes are treated as essential)
		  (cond (partially-cloned-from
			 (km-format t "save-prototype: This save includes only partial clones of the following prototypes,
   so the clone-built-from links to these prototypes will NOT be saved (to allow re-cloning):~%   ~a~%"
				    partially-cloned-from))
			(t (km-format t "save-prototype: This trimmed prototype includes only full clones.~%")))
		  (cond (partial-clone-roots
			 (km-format t "save-prototype: These nodes need to be re-expanded (have the above prototypes re-cloned onto):~%   ~a~%"
				    partial-clone-roots)))
		  (cond ((set-difference trimmed-expanded-from partial-clone-roots)
			 (km-format t "save-prototype: Also, these nodes need to be re-expanded (have BaseKb assertions re-applied to):~%   ~a~%"
				    (set-difference trimmed-expanded-from partial-clone-roots))))
		  (cond ((and (null trimmed-expanded-from) (null partial-clone-roots))
			 (km-format t "save-prototype: No nodes need to be re-expanded.~%")))))

		(km-format stream0 "~%;;; ---------- Definition of prototype for ~a ----------~%~%" (delistify scope))
;    (mapc #'(lambda (class)
;	      (km-format stream0 "(~a has (superclasses ~a))~%~%" class (immediate-superclasses class)))
;	  (remove '#$Thing classes))
		(mapc #'(lambda (participant)
			  (save-frame participant :stream stream0
				      :situations `(,*global-situation*) :save-prototypep t
				      :essentials participants-to-write-out :partially-cloned-from partially-cloned-from))
		      participants-to-write-out)
		(mapc #'(lambda (extra-assertion)
			  (km-format stream0 "~a~%" extra-assertion))
		      extra-assertions)
		(cond (extra-assertions (km-format stream0 "~%")))
		(cond (include-explanationsp
		       (mapc #'(lambda (participant)
				 (save-explanations participant :stream stream0 :explanation-types *prototype-explanation-types-to-save*
						    :essentials participants-to-write-out))
			     participants-to-write-out)
		       (km-format stream0 "~%")))
		(km-format stream0 ";;; ---------- end of prototype definition ----------~%~%")
		(cond ((and (not stream) ; i.e., file keyword given
			    (streamp stream0)) (close stream0)))
;    '#$(t)
		(cond ((set-difference partial-clone-roots trimmed-expanded-from)
		       (km-format t "WARNING: trimmed parts of prototypes cloned onto nodes ~a were missing explanations.~%" (set-difference partial-clone-roots trimmed-expanded-from))
		       (km-format t "WARNING: Not a problem but this shouldn't happen!~%")))
;		(km-format t "partial-clone-roots = ~a~%" partial-clone-roots)
;		(km-format t "trimmed-expanded-from = ~a~%" trimmed-expanded-from)
		(cond
		 (essential-participants0   ; trimming only happens if essential participants was given
		  (cond ((null non-essentials) (km-format t "~a: Prototype size unchanged at ~a nodes.~%" prototype (length participants)))
			(t (km-format t "~a: Prototype size reduced from ~a to ~a nodes.~%" prototype (length participants) (length new-essentials)))))
		 (t (km-format t "Prototype ~a (~a nodes) saved.~%" prototype (length participants))))
		(remove-duplicates
		 (append partial-clone-roots ; may be NIL of course
			trimmed-expanded-from)) ; this should be a superset of partial-clone-roots, unless
					; explanations are missing for some reason, hence do intersection
		)))))))))

;;; ======================================================================
;;;		TRIM PROTOTYPE
;;; ======================================================================

;;; Similar to save-prototype: trim prototype in-memory
;;; Some participants will be UNCHANGED, some will be MODIFIED, and some will be completely DELETED (the NON-ESSENTIALS)
;;; Trim prototype now returns the list of MODIFIED participants.
;;; RETURNS: TWO values
;;;   - The nodes in the prototype whose clone-built-from values changed, ie, where recloning (reexpansion) is needed
;;;   - If an error occurred, a string describing the error. To test for success, make sure this value in NIL
;;;
;;; The basic idea is that the essential participants are the visible ones, the others are inferred but never viewed
;;;    by the SME, so can be dropped
(defun trim-prototype (prototype0 &key essential-participants)
  (let* ((prototype (dereference prototype0))
	 (prototype-classes (remove-subsumers (get-vals prototype '#$prototype-of))))
  (cond
   ((not (prototypep prototype))
    (report-error 'user-error "(trim-prototype ~a): ~a is not a prototype!~%" prototype prototype)
    (values nil (km-format nil "(trim-prototype ~a): ~a is not a prototype!" prototype prototype)))
   ((null essential-participants)
    (report-error 'user-error
		  "(trim-prototype ~a :essential-participants nil): You must provide some essential participants!~%"
		  prototype)
    (values nil (km-format nil
		   "(trim-prototype ~a :essential-participants nil): You must provide some essential participants!"
		  prototype)))
   ((not (member prototype essential-participants))
    (report-error 'user-error "(trim-prototype ~a :essential-participants ...):~%   The root ~a must be a member of the essential-participants list, but wasn't!~%" prototype prototype)
    (values nil (km-format nil "(trim-prototype ~a :essential-participants ...):~%   The root ~a must be a member of the essential-participants list, but wasn't!" prototype prototype)))
   (t (let* ((participants0 (get-vals prototype '#$prototype-participants))
;;; NEW: Add warning and error recovery if this procedure is passed some invalid essentials
	    (essential-participants0
	     (cond ((not (set-difference essential-participants participants0)) ; good! all essentials are participants
		    essential-participants)
		   (t (report-error 'user-error
		        "(trim-prototype ~a :essential-participants ~a):~%   ~a is/are not prototype-participant(s) of ~a, but should be!~%   Continuing, dropping those non-participants...~%"
			prototype0 essential-participants prototype
			(delistify (set-difference essential-participants participants0)) prototype)
		      (intersection essential-participants participants0)))))
;;; end NEW (except for 1 essential-participants -> essential-participants0 later)
	(multiple-value-bind
	    (new-essentials error-message)
	    (find-essentials essential-participants0 :protoroot prototype :participants participants0)
	  (cond
	   (error-message (values nil (concat "Doing trim-prototype: " error-message)))
	   (t (let*
	       ((participants (get-vals prototype '#$prototype-participants)) ; redo incase find-essentials patched buggy file
		(non-essentials (ordered-set-difference participants new-essentials))
; partially-cloned-from = roots of prototypes cloned into prototype0 which are now only partially cloned in.
		(partially-cloned-from
;		 (km `#$(the prototype-participant-of of (the cloned-from of ,(VALS-TO-VAL NON-ESSENTIALS))))) ; [2]
;		 This returns the ROOTS of prototypes cloned into the current one. If the root is non-essential,
;		 we better delete the clone-built-from tags later.
		           (remove-duplicates	; -> protoroots
			    (my-mapcan #'(lambda (prototype-participant)
					   (get-vals prototype-participant '#$prototype-participant-of))
				       (my-mapcan #'(lambda (non-essential)  ; -> protoinstances
						      (get-vals non-essential '#$cloned-from))			; these are the sources of the participants to be completely deleted
						  non-essentials)))) ; [2]
; partial-clone-roots = the nodes that the above partially-cloned prototypes were cloned onto
; Sunil wants these to change their expansion status (HLO-2250)
		(partial-clone-roots
		 (remove-if-not #'(lambda (participant)
				    (intersection (get-vals participant '#$clone-built-from) partially-cloned-from))
				new-essentials))
	        (trimmed-expanded-from (remove-duplicates
					(intersection (remove-duplicates (my-mapcan #'node-expanded-from non-essentials))
						      new-essentials))))

	       (cond (partially-cloned-from
		      (km-format t "trim-prototype: This trimmed prototype includes partial clones of the following prototypes,~%
   so the clone-built-from links to these prototypes will be removed (to allow re-cloning):~%   ~a~%"
				 partially-cloned-from))
		     (t (km-format t "trim-prototype: This trimmed prototype includes only full clones.~%")))

	       (cond (partial-clone-roots
		      (km-format t "trim-prototype: These nodes need to be re-expanded (have the above prototypes re-cloned onto):~%   ~a~%"
				 partial-clone-roots)))
		(cond ((set-difference trimmed-expanded-from partial-clone-roots)
		       (km-format t "trim-prototype: Also, these nodes need to be re-expanded (have BaseKb assertions re-applied to):~%   ~a~%"
				  (set-difference trimmed-expanded-from partial-clone-roots))))
		(cond ((and (null trimmed-expanded-from) (null partial-clone-roots))
		       (km-format t "trim-prototype: No nodes need to be re-expanded.~%")))

	       (km-format t "Trimming ~a essential frames in memory..." (length new-essentials))
	       (let
		 ((modified-participants
  	          (remove-duplicates
		   (mapcan #'(lambda (participant) ; these are all the participants that will be LEFT after trimming
		    (mapcan #'(lambda (slotvals)
			    (let* ((slot (slot-in slotvals))
				   (vals0 (vals-in slotvals))
				   (vals (cond ((single-valued-slotp slot) (un-andify vals0))
					       (t vals0)))
				   (skolem-vals (remove-if-not #'anonymous-instancep (flatten vals)))) ; flatten is unnecessary for deletion, but is useful for checking all participants are declared
			      (cond
			       ((eq slot '#$clone-built-from) ; DROP clone-built-from flags for prototypes whose clones
				(let ((clone-built-from-to-drop		; are only being partially saved
				       (intersection vals partially-cloned-from)))
				  (mapc #'(lambda (val)
					    (let ((*trace-prototype-assertions* nil)) ; ok to update prototypes
					      (delete-val participant '#$clone-built-from val :situation *global-situation*)))
					clone-built-from-to-drop))
				nil)
			       ((member slot *slots-with-nonparticipant-skolems*) nil) ; no action

; REVISED: Still may trim non-local constraints, even if all the vals are essential, hence we can't skip this step.
;			       ((not (set-difference skolem-vals new-essentials)) nil) ; all vals are essential, so keep them!

			       (vals (cond
				      ((set-difference skolem-vals participants)
				       (report-error 'user-warning "(the ~a of ~a) includes~%   ~a in prototype ~a,~%   but ~a isn't/aren't declared as prototype-participants)!~% I will drop these values on this slot."
						     slot participant
						     (remove-if-not #'(lambda (val)
									(set-difference
									 (remove-if-not #'anonymous-instancep (flatten val))
									 participants))
								    vals)
						     prototype
						     (set-difference skolem-vals participants))))

				     (let* ((deletions-p
					     (mapcar #'(lambda (val)
							 (let* ((*trace-prototype-assertions* nil) ; ok to update prototypes
								(val-skolems (remove-if-not #'anonymous-instancep (flatten val)))) ; flatten is probably unnecssary
							   (cond ((constraint-exprp val)
								  (let* ((isv-explanations (get-explanations participant slot val *global-situation*))
									 (explanations (my-mapcan #'explanations-in isv-explanations)))
;								    (km-format t "explanations for ~a = ~a~%" val explanations)
								    (cond
								     ((every #'(lambda (explanation)	; No local support for constraint, so delete it
										 (or (eq (explanation-type explanation) '#$cloned-from)
										     (and (eq (explanation-type explanation) '#$added-at)
											  (not (member (second explanation) prototype-classes)))))	; added at superclass, not current class
									     explanations)
								      (mapc #'(lambda (explanation) ; (cloned-from _ProtoCar1 _Car2 _ProtoWheel1)  -> source was ProtoCar1, cloned onto _Car2
										(cond ((eq (explanation-type explanation) '#$cloned-from)
										       (let ((originating-protoroot (second explanation))
											     (cloned-onto (third explanation)))
;										  (km-format t "~a -> ~a~%" originating-protoroot cloned-onto)
											 (cond ((member originating-protoroot
													(get-vals cloned-onto '#$clone-built-from :situation *global-situation*))
												(delete-val cloned-onto '#$clone-built-from originating-protoroot :situation *global-situation*)))))))
									    explanations)
								      (km-format t "DEBUG: Trimming inherited constraint (~a has (~a (~a))) [not locally asserted]~%"
										 participant slot val)
								      (delete-val participant slot val :situation *global-situation*)
								      t))))
							         ((null (set-difference val-skolems new-essentials)) ; [1] no non-essential val-skolems, so keep it (includes constants)
								  nil)
								 (t (delete-val participant slot val :situation *global-situation*) t))))
						     vals)))
				       (cond ((member t deletions-p)
					      (list participant))))) ; return the id of the modified participant
			       )))
			    (get-slotsvals participant :situation *global-situation*)))
		       new-essentials))))
;		 (km-format t "DEBUG: modified-participants = ~a~%" modified-participants)
		 (km-format t "~a were modified, ~a remain unchanged...~%" (length modified-participants)
			   (- (length new-essentials) (length modified-participants)))
		(km-format t "Deleting ~a non-essential frames from memory...~%" (length non-essentials))
		(let ((*trace-prototype-assertions* nil)) ; ok to update prototypes
		  (mapc #'delete-frame non-essentials))

		(let ((n-deleted
		       (apply #'+ (mapcar #'(lambda (essential)
					     (delete-nonessential-explanations essential :essentials new-essentials))
					 new-essentials))))
		  (km-format t "Deleted ~a explanations for essentials that involve non-essentials...~%" n-deleted))

		(cond ((set-difference partial-clone-roots trimmed-expanded-from)
		       (km-format t "WARNING: trimmed parts of prototypes cloned onto nodes ~a were missing explanations.~%" (set-difference partial-clone-roots trimmed-expanded-from))
		       (km-format t "WARNING: Not a problem but this shouldn't happen!~%")))

		(cond ((null non-essentials) (km-format t "~a: Prototype size unchanged at ~a nodes.~%" prototype (length participants)))
		      (t (km-format t "~a: Prototype size reduced from ~a to ~a nodes.~%" prototype (length participants) (length new-essentials))))
		(remove-duplicates
		 (append partial-clone-roots
			trimmed-expanded-from)) ; should be a superset of partial-clone-roots, but do a union
		 				; in case explanations are missing
		))))))))))

;;; ======================================================================

;;; Returns the number of deletions done
(defun delete-nonessential-explanations (concept &key essentials)
  (length (remove nil (mapcar #'(lambda (isv-explanation)
				  (delete-nonessential-explanation isv-explanation :essentials essentials))
			      (get-all-explanations concept nil)))))

;;; [1] Note: all prototype explanations are in *Global
(defun delete-nonessential-explanation (isv-explanation &key essentials)
  (let ((nonessentials (nonessentials-in isv-explanation :essentials essentials)))
    (cond
     (nonessentials
;      (km-format t "DEBUG: Dropping explanation containing a non-essential ~a:~%  ~a~%"
;		 (delistify (remove-duplicates nonessentials)) isv-explanation)
      (let ((i (first isv-explanation))
	    (s (second isv-explanation))
	    (v (third isv-explanation))
	    (explanation (explanation-in isv-explanation)))
	(delete-explanation i s v :explanation-to-delete explanation :situation *global-situation*)	; [1]
	t)))))

;;; ======================================================================

(defparameter *expand-essentials* t)

#|
----------------------------------------
find-essentials: Given an initial list of essential participants, iteratively expand the list
so that each slot's values are either ALL essential or NONE are. Then (in save-prototype) just
write out the slots where ALL the slot's values are essential.

RETURNS: TWO values
 - The list of essential participants, or NIL if an error occurred
 - If an error occurred, a string reporting the error

ALGORITHM:
GATHER PROCESS:
foreach essential individual [a subset of participants]
  foreach slot+vals of essential individual
    IF none of the vals are essential individuals, skip the slot
    ELSE add any vals which AREN'T essential individuals to the essential individuals list
ITERATE until the list of essential participants is stable
----------------------------------------
|#
;;; Iterate until no more essentials found
;;; (find-essentials '#$(_Car1 _Engine1 _Cylinder1) :protoroot '#$_Car1)
(defun find-essentials (essentials &key protoroot (participants (get-vals protoroot '#$prototype-participants)) (n 1))
;  (km-format t "DEBUG: Iteration ~a: ~a essentials of ~a~%" n (length essentials) (length participants))
;  (km-format t "participants = ~a~%" participants)
  (cond
   ((not *expand-essentials*) essentials)		; conditionally disable this functionality
   ((> n 30)
    (report-error 'system-error "find-essentials for ~a seems stuck in a loop (iterated 30 times)!~%" protoroot)
    (values nil (km-format "find-essentials for ~a seems stuck in a loop (iterated 30 times)!" protoroot)))
   ((set-difference essentials participants)  ; bad! Some essentials aren't participants...
    (cond ((not (set-difference essentials ; ...but false alarm; participants doesn't reflect the (up to date)
					   ; list of participants (they were augmented), so recompute and retry:
				(get-vals protoroot '#$prototype-participants)))
	   (find-essentials essentials :protoroot protoroot :n n))   ; no :participants -> will be recomputed (defun above)
;;; 1/16/10 Change this to a warning...
;	  (t (report-error 'user-error
;		  "(find-essentials ~a :protoroot ~a):~%   ~a is/are not prototype-participant(s) of ~a, but should be!~%"
;		  essentials protoroot (delistify (set-difference essentials participants)) protoroot)
;	     (values nil
;	      (km-format nil
;		"(find-essentials ~a :protoroot ~a):~%   ~a is/are not prototype-participant(s) of ~a, but should be!"
;		essentials protoroot (delistify (set-difference essentials participants)) protoroot)))))
	  (t (report-error 'user-warning
		  "(find-essentials ~a :protoroot ~a):~%   ~a is/are not prototype-participant(s) of ~a, but should be!~%   Continuing, dropping those non-participants...~%"
		  essentials protoroot (delistify (set-difference essentials participants)) protoroot)
	     (find-essentials (ordered-intersection essentials ; retry with just those essentials that are participants
						    (get-vals protoroot '#$prototype-participants))
			      :protoroot protoroot :n n))))
   (t (let ((new-essentials (find-essentials0 essentials :protoroot protoroot :participants participants)))
	(cond ((set-equal essentials new-essentials)
	       (km-format t
  "find-essentials: The following ~a of ~a participants are not essential to the prototype ~a:~%   ~a~%"
  		(length (set-difference participants essentials)) (length participants) protoroot
		(set-difference participants essentials))
	       new-essentials)		; reached quiescence
	      (t (find-essentials new-essentials :protoroot protoroot :participants participants :n (1+ n))))))))

#|
(_Car1 parts (_Engine1 _Wheel1))
If _Car1 and _Engine1 are essential, _Wheel1 will be added as essential also

(_Car1 parts ((:pair _Engine1 *red)))
_Engine1 will be MADE essential because there are some non-anonymous elements in the structure
When writing, if there are ever non-anonymous elements, write them out.
|#
(defun find-essentials0 (essentials-to-check &key protoroot participants (essentials essentials-to-check))
  (cond
   ((endp essentials-to-check) essentials)
   (t (let* ((essential (first essentials-to-check))
	     (slotsvals (get-slotsvals essential :situation *global-situation*))
;	     (bad-instances-list nil) ; hacky way of catching bad-instances in procedure below
	     (extra-essentials
	      (remove-duplicates
	       (my-mapcan #'(lambda (slotvals)
			  (let ((slot (slot-in slotvals))
				(vals (vals-in slotvals)))
			    (cond
			     ((member slot *unclonable-slots*) nil)	; important! Skip these
			     ((member slot '#$(cloned-from clone-built-from)) nil)
			     (t (let* ((instances (remove-if-not #'anonymous-instancep (flatten vals)))
				       (good-instances (intersection instances participants))
;				       (bad-instances (set-difference instances (append bad-instances-list participants)))
				       )
; No: it would be better to *drop* the bad value (done later by trim-prototype and save-prototype)
;				  (cond
;				   (bad-instances
;				    (report-error 'user-warning
;		  "(the ~a of ~a) includes~%   ~a in prototype ~a,~%   but ~a isn't/aren't declared as prototype-participants)! I will patch the prototype and add them as participants...~%"
;		  slot essential (delistify bad-instances) protoroot (delistify bad-instances))
;				    (mapc #'(lambda (bad-instance)
;					      (push bad-instance bad-instances-list)
;					      (let ((*trace-prototype-assertions* nil))
;						(add-val bad-instance '#$prototype-participant-of protoroot)))
;					  bad-instances)))
				  (cond
				   ((or (intersection instances essentials) ; if ANY instance is essential...
					(notevery #'anonymous-instancep (flatten vals))) ; OR there's a non-Skolem...
;				    (ordered-set-difference instances ; ...then ALL instances are essential
;							    essentials))))))))
				    (ordered-set-difference good-instances ; ...then ALL (good) instances are essential
						    essentials))))))))
			  slotsvals))))
;	(km-format t "extra-essentials = ~a~%" extra-essentials)
	(find-essentials0 (append (rest essentials-to-check) extra-essentials)
			 :protoroot protoroot :participants participants ; (append bad-instances-list participants)
			 :essentials (append essentials extra-essentials))))))

;;; Force (re-)evaluation of all edges in the prototype
;(defun eval-prototype (protoinstance)
;  (let ((participants (km-int `#$(the prototype-participants of ,PROTOINSTANCE))))
;    (eval-instances participants :recursivep nil)))

;;; ======================================================================
;;; 		DELETE PROTOTYPE TRIPLE
;;; NOTE: This implementation is broken a little, as prototype supports are now (<f> <s> <v>) rather
;;; then (cloned-from <...>) structures ([1] needs modifying).
;;; 3/4/08: ALSO: For dependent triples that are NOT deleted [2] (as they are supported by other
;;;         things also), this function needs to at least UPDATE their supports to no longer include
;;;	    the prototype.
;;; ======================================================================
(defun delete-prototype-triple (triple)
  (cond
   ((or (and (anonymous-instancep (first triple)) (not (protoinstancep (first triple))))
	(and (anonymous-instancep (third triple)) (not (protoinstancep (third triple))))
	(and (not (anonymous-instancep (first triple))) (not (anonymous-instancep (third triple)))))
    (report-error 'user-error "ERROR! ~a is not part of a prototype!~%" triple))
   (t (let*
        ((classes (prototype-classes triple))
	 (prototype-root (in-prototype triple))
	 (supports (get-support-details triple))
	 (external-supports (remove-if-not #'(lambda (support)
					       (or (eq (first support) '#$every)
						   (and (eq (first support) '#$added-at)
							(not (member (second support) classes)))
						   (and (triplep support)
							(not (eq (first support) '#$added-at))
							(set-difference (prototype-classes support) classes))))
					   supports))
	 (internal-supports (ordered-set-difference supports external-supports :test #'equal)))
    (km-format t "(~a is part of the prototype for ~a)~%" triple (delistify classes))
    (cond (external-supports
	   (km-format t "Can't delete this triple! It is supported by:~%")
	   (mapc #'show-support external-supports)
	   nil)
	  (t (cond (internal-supports
		    (km-format t "Can delete this triple. It only has local supports as follows:~%")
		    (mapc #'show-support internal-supports))
		   (t (km-format t "Can delete this triple~%")))
	     (let ((dependent-triples (triple-cloned-to triple)))
	       (cond (dependent-triples
		      (km-format t "Deleting dependent triples:~%")
		      (mapc #'(lambda (dependent-triple)
				(let* ((dependent-supports (get-support-details dependent-triple))
				       (new-dependent-supports0 (remove triple dependent-supports :test #'equal))
				       (new-dependent-supports (remove-if #'(lambda (triple)
									      (and (eq (first triple) '#$added-at)
										   (member (second triple) classes)))
									  new-dependent-supports0)))
				  (cond (new-dependent-supports ; [2]
					 (km-format t "   ~a: not deletable: still supported by ~a (not deleted).~%"
						    dependent-triple new-dependent-supports)
					 (delete-support-by-prototypes dependent-triple (list prototype-root)))
					(t (km-format t "   ~a: deletable, so deleting it.~%" dependent-triple)
					   (delete-triple dependent-triple)))))
			    dependent-triples))
		     (t (km-format t "(No dependent triples to try and delete)~%"))))
	     (km-format t "Finally deleting main triple (done).~%")
	     (delete-triple triple)
	     t))))))

(defun delete-triple (triple)
  (let ((f (first triple))
	(s (second triple))
	(v (third triple)))
    (delete-val f s v)))

(defun show-support (support)
  (cond ((eq (first support) '#$every) (km-format t "   ~a~%" support))
	((eq (first support) '#$added-at) (km-format t "   A user-added assertion at ~a (~a)~%"
						     (second support) (third support)))
	((triplep support) (km-format t "   ~a, stored at ~a~%" support (delistify (prototype-classes support))))))


;;; ----------------------------------------

(defun raise-prototype (prototype)
  (cond ((not (prototypep prototype))
	 (report-error 'user-error "ERROR! (raise-prototype ~a): ~a is not the root of a prototype!~%"
		       prototype prototype))
	(t ; (mapc #'raise-participant (km-int `#$(the prototype-participants of ,PROTOTYPE)))
	     (mapc #'raise-participant (get-vals prototype '#$prototype-participants))
	 t)))

(defun raise-participant (participant)
  ;;; Raise slot values
  (mapc #'(lambda (situation)
	    (add-slotsvals participant (get-slotsvals participant :situation situation)
			   :situation *global-situation* :combine-values-by 'appending))
	(remove *global-situation* (all-situations)))
  ;;; Raise explanations
  (put-explanation-data participant (remove-duplicates
				     (my-mapcan #'(lambda (situation)
						    (get-explanation-data participant :situation situation))
						(all-situations))
				     :test #'equal)
			:situation *global-situation*))

;;; ======================================================================

#|
triple-expanded-from returns the node(s) in the CMap which led to <triple> being concluded.
node-expanded-from does the same thing for a specific node. If <node> was part of a prototype whose root
  was cloned onto <root-clone>, then <root-clone> is returned.
  Or more specifically, like triple-expanded-from, TWO values are returned:
	(i) a list of <root-clone> nodes
	(ii) a list of (<root-clone> <source> <source-class>), as documented for triple-expanded-from.

ALGORITHM:
The supports for <node> are the union of the supports for the triples in which <node> participates.

Question: We find the triples then look at their explanations via triple-expanded-from...  Why not simply
look at ALL explanations directly on node via get-explanation-data? I guess the only reason is that
triple-expanded-from looks at not just the forward links, but also the inverse direction: Suppose
N-r-X, and the explanation database says (X-invr-N (cloned-from ...)); then we want to get that inverse
explanation as part of the node-expanded-from data. However: I *think* KM records explanations in both
directions anyway so strictly such reversing may not be necessary. However, we'll leave it for now.
|#
(defun node-expanded-from (node0 &key ignore-prototypes)
  (let* ((node (dereference node0))
	 (incoming-triples
	  (mapcan #'(lambda (slotvals)
		      (let ((slot (slot-in slotvals))
			    (vals (vals-in slotvals)))
			(mapcan #'(lambda (val)
				    (cond
				     ((eq slot '#$cloned-from) nil)
				     ((or (&-exprp val) (&&-exprp val))		; (x & y) or ((x) && (y))
				      (mapcar #'(lambda (val0)
						  `(,node ,slot ,val0)) 	  ; (find-exprs '(x & y) -> (x y)
					      (find-exprs val :expr-type 'any)))  ; (find-exprs '((x) && (y))) -> (x y)
				     (t `((,node ,slot ,val)))))
				vals)))
		  (append (get-slotsvals node)
			  (cond ((am-in-local-situation) (get-slotsvals node :situation *global-situation*))))))
	 (node+rule-pairs (remove-duplicates
			   (mapcar #'(lambda (triple)
; Ug, why did I do :both-directions nil? It leads to errors (HLO-1617). Remove it!
;				       (multiple-value-list (triple-expanded-from triple :both-directions nil)))
; RETURNS: ((_Foo3) ((_Foo3 (cloned-from _ProtoFoo3) (Foo))))   for cloned nodes, NIL otherwise
				       (multiple-value-list (triple-expanded-from triple
										  :ignore-prototypes ignore-prototypes)))
				   incoming-triples)
			   :test #'equal))
	 (nodes+rules (transpose node+rule-pairs))
	 (nodes (remove-duplicates (append-lists (first nodes+rules))))
	 (rules (remove-duplicates (append-lists (second nodes+rules)) :test #'equal)))
;    (km-format t "nodes+rule-pairs = ~%~{   ~a~%~}" node+rule-pairs)
    (values nodes rules)))

#|
MAPCAN-SAFE
(triple-expanded-from <triple>)
(triple-expanded-from '#$(_Move5 agent _Person8))
	-> (_Foo3)
     AND   ((_Foo3 (cloned-from _ProtoFoo3) (Foo)))

This function takes a triple in a CMap, and returns TWO values, namely TWO
lists whose members are respectively:
 - the individual in the same CMap from which it was expanded
 - the (same) individual + source + classes
   where source is EITHER:
   (cloned-from prototype-root), where prototype-root is the root of the
         prototype which was cloned onto the individual to produce
	 (among other things) <triple>.
   (every class has ...), an expression which when evaluated resulted in
         _Foo3.
   classes are either the class(es) of this prototype or the (listified)
   class on which the (every ...) expression resides.

   Each source contributing to <triple> will be denoted by a different
   element in this second list, even if they both were applied onto the same
   individual node in the CMap.

See aura-api.txt for further documentation
|#
(defun triple-expanded-from (triple &key ignore-prototypes)
  (cond
   ((not (triplep triple))
    (report-error 'user-error
		  "expanded-from ~a: Need a triple as an argument, e.g., (expanded-from '#$(_Move5 agent _Person8))~%"
		  triple))
   (t (let* ((expln-struct1 (get-explanations0 (first triple) (second triple) (third triple)))
	     (expln-struct2 (get-explanations0 (third triple) (invert-slot (second triple)) (first triple)))
	     (expln-structs (remove nil (list expln-struct1 expln-struct2))))
	(item-expanded-from expln-structs :ignore-prototypes ignore-prototypes)))))

;;; MAPCAN-SAFE
(defun item-expanded-from (expln-structs &key ignore-prototypes)
  (let* ((explanations (my-mapcan #'fourth expln-structs))
	 (instance+root/rule+classes-list
	                  (remove-duplicates
			   (remove nil
			    (mapcar #'(lambda (explanation) ; [1] e.g., (cloned-from <protoroot> <clone-root>)
					(cond ((and (listp explanation)
						    (eq (first explanation) '#$cloned-from)
						    (known-frame (third explanation)) ; root of expansion
						    (not (member (second explanation) ignore-prototypes)))
					       (list (third explanation) 		; clone-root
						     `(#$cloned-from ,(second explanation)) ; prototype-root
						     (prototype-classes (second explanation)))) ; prototype-classes
					      ((and (listp explanation)
						    (let* ((source (first (sources explanation)))) ; should never be > 1
;						      (km-format t "source = ~a~%" source)  ; e.g., (@ _Cell1 Cell has-part)
						      (cond (source
							     (let ((class (originated-from-class source))	; Cell
								   (instance (inherited-to-instance source))	; _Cell1
								   (rule (build-rule explanation)))
							       (list instance rule (list class))))))))))
				    explanations))
			   :test #'equal))
	 (instances (remove-duplicates (mapcar #'first instance+root/rule+classes-list))))
;    (km-format t "instance+root/rule+classes-list = ~a~%" instance+root/rule+classes-list)
;    (km-format t "triple-expanded-from: explanations = ~a~%" explanations)
    (values instances instance+root/rule+classes-list)))

;;; ======================================================================

(defun add-triple (triple)
  (let* ((f (first triple))
	 (s (second triple))
	 (v (third triple)))
    (km `#$(,F also-has (,S (,V))))))

#|
(add-triple-asif-cloned <triple> <n> <source-triple> <source-root>)
(add-triple-asif-cloned
     '#$(_Hand2 parts _Finger2) '#$_Arm2 '#$(_Hand1 parts _Finger1) '#$_Arm1)

Assert <triple>, but make it LOOK as if <triple> was cloned from
<source-triple> in the prototype rooted at <source-root>.

Imagine the prototype rooted at <source-root> was cloned onto the node <n>,
resulting in, among other things, <triple> being asserted as a clone
of <source-triple>. add-triple-asif-cloned makes it *look* as if this
is what happened, although in practice it asserts <triple> explicitly.

For example, given:

  Prototype of Arm: [Arm1]-parts->[Hand1]

  Prototype of Body: [Body2]-parts->[Arm2]-parts->[Hand2]
        where [Arm2]-parts->[Hand2] was cloned from [Arm1]-parts->[Hand1]

Suppose we now extend Arm's prototype to be:

  Prototype of Arm: [Arm1]-parts->[Hand1]-parts->[Finger1]

If we want to add the equivalent triple to the Body prototype AS IF IT
WAS CLONED from Arm, do:

  ;;; Create a finger
  (km '#$(a Finger)) -> [Finger2]

  ;;; Now do:
  (add-triple-asif-cloned
        '(Hand2 parts Finger2) 'Arm2 '(Hand1 parts Finger1) 'Arm1)

This also works for adding onto a CLONE of a prototype (e.g., of Body)
as well as to a prototype itself (as above).

Footnotes below:
[1] Normally this will be a redundant call if Arm is already cloned into Body.
[2] To tolerate (add-triple-asif-cloned '(_Vic1 subevent (must-be-a OtherEvent)) '_Vic1
					'(_Vic168 subevent (must-be-a OtherEvent)) '_Vic168)
|#
(defun add-triple-asif-cloned (triple n source-triple source-root)
  (let* ((f (first triple))
	 (s (second triple))
	 (v (third triple))
	 (source-f (first source-triple))
	 (source-v (third source-triple)))
  (km `#$(,F also-has (,S (,V))))
  (cond ((kb-objectp f) (km `#$(,F also-has (cloned-from (,SOURCE-F))))))
  (cond ((kb-objectp v) (km `#$(,V also-has (cloned-from (,SOURCE-V)))))) ; [2]
  (cond ((kb-objectp f) (km `#$(explanation (:triple ,F ,S ,V) ((cloned-from ,SOURCE-ROOT ,N ,SOURCE-F))))))
;;; Soon hopefully we can drop this, when the explanation API is extended
  (cond ((kb-objectp v) (km `#$(explanation (:triple ,V ,(INVERT-SLOT S) ,F) ((cloned-from ,SOURCE-ROOT ,N ,SOURCE-V))))))
  (km `#$(,N also-has (clone-built-from (,SOURCE-ROOT)))))) ; [1]

;;; --------------------------------------------------

;;; Could probably make this more efficient with a lookahead but doesn't matter I think
(defun remove-clone-cycles (explanation-structs)
;  (break)
  (cond ((endp explanation-structs) nil)
	(t (let* ((explanation-struct (first explanation-structs)) ; (f s v explns)
		  (explanation (fourth explanation-struct)))
	     (cond ((clone-cycle explanation)
;		    (km-format t "CLONE CYCLE DETECTED! Removing explanation...~%  ~a~%" explanation-struct)
		    (remove-clone-cycles (rest explanation-structs)))
		   (t (cons explanation-struct (remove-clone-cycles (rest explanation-structs)))))))))

#|
HLO-1770: [1] check for clone-cycle not general enough: When doing (clone P) to CP, the cloned explanations might
not only have (N (cloned-from CP CP), but also (N (cloned-from CP N2)) where N2 is a different node in the clone.
In prototype _Cell161, participant _Polymer10255 has:
    (explanation (:triple _Polymer10255 has-part _Amino-Acid10256) ((cloned-from _Cell161 _Dividing-cell10269)))
(where of course _Dividing-cell10269 is also a participant of _Cell161).

Strictly to spot this, we only need to look for (cloned-from CP *). However, to be safe we could check for
(cloned-from CX *) where CX is clone of ANY node in the original prototype. Or, to do the same thing,
simply test that CX is a prototype, i.e., hasn't been sublis'ed from a prototype to a non-prototype
through mapping-alist. In principle, the only case I can see where CX might be a non-prototype is when
CX is the clone of CP, but we may as well just check in general.

One can see how this issue can arise, if we have:

	[[Cell]] -similar-to-> [Dividing-Cell]
	     \-has-part-> [Amino-Acid]

which then becomes

	[[Cell]] -similar-to-> [Dividing-Cell] -similar-to-> [Dividing-Cell']
	     \-has-part-> [Amino-Acid]        \-has-part-> [Amino-Acid']

here we'll have
    (explanation (:triple Dividing-Cell has-part Amino-Acid' ((cloned-from [Cell] [Dividing-Cell]))))
|#
;;; (cloned-from _Car1 _Car1)
;;; (cloned-from _Car1 _Car2)
;;; I think really we just need to make sure that _Car1 isn't the clone of the prototype root, but for safety
;;; let's check it isn't a clone of *anything* in the original prototype
(defun clone-cycle (explanation)
  (and (listp explanation)
       (eq (first explanation) '#$cloned-from)
;      (eq (second explanation) (third explanation))	 [1]
       (not (prototypep (second explanation))) ; No! Due to load order, may not YET be asserted a prototype (HLO-1859)
       ))				       ; We'll handle this by suppressing the check during file loading

;;; (cloned-from _Foo1 _Foo2 _Bar1 2) ->  (cloned-from _Foo1 _Foo2)
(defun simplify-cloned-from (explanation) (first-n explanation 3))

;;; ======================================================================

;;; Create new slot, the cloned version of prototype-participants.
;;; For an instance I, with prototype P cloned onto it, participants are the
;;; CLONES in the graph of P that were asserted (either directly or indirectly)
;;; about I. In other words, they are objects "related" to I via some chain of slots.
;;; We could alternatively have simply collected all the objects within depth <n> of I,
;;; but that might return a lot of things, some of which may be pretty irrelevant.
;;; This is a procedural attachment, defined in KM. We depth-limit it to depth 10 in KM
;;; (perhaps unnecessarily).
(defun participants (instance &key (depth 10))
  (let* ((classes (remove-subsumers (immediate-classes instance)))
	 (protoroot (some #'(lambda (class) (first (get-vals class '#$prototypes))) classes)))
;   (format t "protoroot = ~a~%" protoroot)
    (cond (protoroot
	   (cond ((not (member protoroot (get-vals instance '#$clone-built-from))) (unify-in-prototype instance protoroot)))
	   (participants0 (list instance) :depth depth :protoroot protoroot)))))

(defun participants0 (instances &key (depth 10) done protoroot)
  (cond
   ((<= depth 0) done)
   ((null instances) done)
   (t (let* ((vals (remove-duplicates
		    (my-mapcan #'(lambda (instance)
				   (let* ((source-protoinstances2 (get-vals instance '#$cloned-from))
					  (source-protoroots2 (remove-duplicates (my-mapcan #'(lambda (i)
												(get-vals i '#$prototype-participant-of))
											    source-protoinstances2))))
				      (cond ((member protoroot source-protoroots2) ; cloned from same prototype
					     (let ((slotsvals (append (get-slotsvals instance :situation *global-situation*)
								      (cond ((am-in-local-situation) (get-slotsvals instance))))))
					       (my-mapcan #'(lambda (slotvals)
							      (cond ((not (member (slot-in slotvals) '#$(cloned-from clone-built-from)))
								     (remove-if-not #'anonymous-instancep (vals-in slotvals)))))
							  slotsvals))))))
				instances)))
	     (new-vals (set-difference vals done)))
	(participants0 new-vals :depth (1- depth) :done (append done new-vals) :protoroot protoroot)))))

#| Simpler version - doesn't use :protoroot in the code
(defun participants (instance &key (depth 10))
  (cond ((not (get-vals instance '#$cloned-from))
	 (let* ((classes (remove-subsumers (immediate-classes instance)))
		(protoroot (some #'(lambda (class) (first (get-vals class '#$prototypes))) classes)))
	   (cond (protoroot (unify-in-prototype instance protoroot))))))
  (participants0 (list instance) :depth depth))

(defun participants0 (instances &key (depth 10) done)
  (cond
   ((<= depth 0) done)
   ((null instances) done)
   (t (let* ((vals (remove-duplicates
		     (my-mapcan #'(lambda (instance)
				    (let ((slotsvals (append (get-slotsvals instance :situation *global-situation*)
							     (cond ((am-in-local-situation) (get-slotsvals instance))))))
				      (my-mapcan #'(lambda (slotvals)
						     (cond ((not (member (slot-in slotvals) '#$(cloned-from clone-built-from)))
							    (remove-if-not #'anonymous-instancep (vals-in slotvals)))))
						 slotsvals)))
				instances)))
	     (new-vals (set-difference vals done)))
	(participants0 new-vals :depth (1- depth) :done (append done new-vals))))))
|#



