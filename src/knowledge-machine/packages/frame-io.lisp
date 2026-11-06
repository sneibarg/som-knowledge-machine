
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: frame-io.lisp
;;; Author: Peter Clark
;;; Date: August 1994
;;; Purpose: Low-level interface to the KM data structures

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; ======================================================================
;;; Active situations - a little trick for adding efficiency.
;;; Normally, when unifying, KM will unify in ALL situations, including defunct ones.
;;; With *deactivate-old-situations* = t, a (new-situation) will reset the active situation list
;;; and thus (hopefully!) speed up unification when many situations are being used.
;;; Actually - it's hopelessly slow! Let's ignore this.
;;; ======================================================================

;; No longer used
; (defparameter *deactivate-old-situations* nil)
;(defvar *all-active-situations* nil)
(defvar *classify-slotless-instances* t)

;;; *coerce-undeclared-slot* = t: If see a slot that isn't declared, assert it as (instance-of (Slot))
; (defvar *coerce-undeclared-slots* nil) - in header.lisp

(defun add-to-active-situations (situation) (declare (ignore situation)))
;(defun add-to-active-situations (situation)
;  (km-setq '*all-active-situations* (cons situation *all-active-situations*)))

;(defun all-active-situations ()
;  (cond (*deactivate-old-situations* (remove-duplicates (dereference *all-active-situations*)))
;	(t (all-situations))))

(defun all-active-situations () (all-situations))

#|
======================================================================
	PRIMARY EXPORTED FUNCTIONS (incomplete list)
======================================================================

set/get functions all operate on the *local* situation *only*. They
  are low-level calls to be used by the KM system, and should never be
  used directly unless you are *sure* you're only going to be ever working
  in the Global situation.
 	(add-val instance slot val [install-inversesp situation])
 	(delete-val instance slot val [uninstall-inversesp situation])	 ; not used by KM, but by auxiliary s/w
 	(delete-slot instance slot [facet situation])

	(get-vals instance slot [&key facet situation])
 	(put-vals instance slot vals [&key facet situation install-inversesp])

	(add-slotsvals instance slotsvals [facet situation install-inversesp combine-values-by bind-selfp])

	(get-slotsvals frame [&key facet situation dereferencep])
	(put-slotsvals frame slotsvals [&key facet situation install-inversesp])
	(point-parents-to-defined-concept frame slotsvals facet)
	(create-instance class slotsvals [&key prefix-string bind-selfp target])

scan all supersituations and classes for rules:
	(own-rule-sets instance slot [start-situation retain-commentsp])
	(supersituation-own-rule-sets instance slot [start-situation retain-commentsp])	[- not used]
	(inherited-rule-sets instance slot [start-situation retain-commentsp])
	(inherited-rule-sets-on-classes classes slot [start-situation retain-commentsp])
	(collect-constraints-on-instance instance slot [start-situation retain-commentsp])
	(local-constraints instance slot [situation retain-commentsp])

other:
;	(exists frame [start-situation])	       ; look in local + accessible situations
	(known-frame frame)			       ; Replace "exists", to be more explicit about what exists means
	(has-situation-specific-info frame situation)  ; look in local situation only
	(instance-of instance class)
	(is-subclass-of subclass class)
	(immediate-classes instance)
	(immediate-superclasses class)
	(immediate-subclasses class)
	(immediate-supersituations situation)
	(immediate-subslots slot)
	(all-instances class)
	(all-prototype class)
	(all-classes instance)
	(all-superclasses class)
	(all-subclasses class)
	(all-supersituations situation)
	(all-subslots slot)

======================================================================
|#

;;; [1] Intent below is defconstant, but SBCL doesn't like defconstants on lists
(defparameter *all-facets* '(own-properties member-properties own-definition member-definition))
(defparameter *valid-cardinalities* '#$(1-to-N 1-to-1 N-to-1 N-to-N))
(defparameter *default-cardinality* '#$N-to-N)

(defparameter *inequality-relations* '(< > <= >= /=))	; for km-assert etc.
(defparameter *equality-relations* '(= &?))

(defun invert-inequality-relation (inequality)
  (case inequality
	(< '>=)
	(> '<=)
	(>= '<)
	(<= '>)
	(/= '=)))

;;; ======================================================================
;;;	These classes/instances have delayed evaluation assertions
;;;	attached, listed on their "assertions" slot. When a new
;;;	instance is created, the assertions are made. Typically, it
;;;     will be just Situation classes that have this property.
;;; ======================================================================

;;; Instances of these classes will have their assertions made at creation time
; (defvar *classes-using-assertions-slot* nil) now in header.lisp

;;; ======================================================================
;;; 		DECLARE BUILT-IN OBJECTS
;;; ======================================================================

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-bag-aggregation-slots* '#$(min max sum average difference product quotient))  ; maps (:bag ...) -> value
)

;;; Francis Leboutte - need an eval-when for LispWorks as this defconstant has a non-evaluated argument and is used in a subsequent
;;; defconstant, so we have to force evaluation.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant *built-in-seq-aggregation-slots* nil)		; maps (:seq ...) -> value
)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-set-aggregation-slots*  				  ; maps (:set ...) -> value
  '#$(first second third fourth fifth
      last unification set-unification append number))
)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-aggregation-slots*
  (remove-duplicates
   (append *built-in-bag-aggregation-slots*
	   *built-in-seq-aggregation-slots*
	   *built-in-set-aggregation-slots*)))
)

;;; These slots are ONLY placed on slot frames, and are used as a cue that a slot is being described
(defparameter *slots-slots* '#$(domain range cardinality inverse inverse2 inverse3 inverse12
			      fluent-status inherit-with-overrides simple-inherit-with-overrides aggregation-function))

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-single-valued-slots*
  (append
   '#$(#|domain range|# cardinality aggregation-function #|complete|# ignore-inverses
			inverse inverse2 inverse3 remove-subsumers remove-subsumees inherit-with-overrides
			simple-inherit-with-overrides fluent-status seq-length bag-length
	      #|prev-situation|# ; but not next-situation (S can have multiple S'-A pairs)
	      after-situation-of ; but not before-situation-of (S can be before multiple A-S' pairs)
; NEW: Now allow actions to be performed more than once, so these are now multivalued
;	      before-situation
;             after-situation
	      prototype-participant-of #|prototype-of prototype-scope |#
	      combine-values-by-appending uniquely-called dont-cache-values nowexists
	      abs log exp sqrt floor)
   *built-in-aggregation-slots*))
)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-multivalued-slots*
  '#$(domain range #|M-new|# element-type element-type-of
      superclasses subclasses instances instance-of locked-instance-of locked-instances add-list del-list pcs-list ncs-list
      supersituations subsituations subslots superslots
      slots-to-opportunistically-evaluate
;	      as views useful-views				; for view mechanism
      prev-situation		; modified for Andreas
      next-situation block-projection-for
	      before-situation-of
; NEW: Now allow actions to be performed more than once, so these are now multivalued
	      before-situation
	      after-situation
      domain-of range-of fluent-status-of called
      prototype-participants prototypes prototype-of cloned-from clone-built-from has-built-clones
      has-clones prototype-scope
      #|text|# #|name print-name <-- should be single-valued!!|#
      name		; 3.6.00 now allow structures for name, to be stringified later by make-sentence
      #|terms <- no longer built-in |#
      elements ;;; for busting up sequences into their elements
      member-of members  ;;; (used for defining Partitions)
      classes all-instances all-prototypes all-classes all-superclasses all-subclasses all-supersituations all-subslots
      most-specific most-general
      assertions
      == /== 			; NEW 10/3/00 for recording equality and inequality constraint
      < > ))			; NEW 11/6/00 for numeric inequality constraints
)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-slots*
  (append *built-in-single-valued-slots*
	  *built-in-multivalued-slots*))
)

;;; Ug, AURA uses "not-equal" as a synonym for /==, so let's allow AURA to push "not-equal" into the *neq-slots* list
(defparameter *neq-slots* '#$(/==))

;;; ======================================================================

#|
(defparameter *built-in-complete-slots* '#$(add-list del-list))
PROBLEM! if make them complete, then we get into trouble with
do-script, which with multiple actions assumes the actions (hence the
add-list and del-lists) will be projected accross multiple situations! |#

(defparameter *default-built-in-inertial-fluent-slots*
    (cond ; ((not *clones-are-global*) '#$(nowexists cloned-from))
	  (t '#$(nowexists))))
(defparameter *built-in-inertial-fluent-slots* *default-built-in-inertial-fluent-slots*)

;;; This can be over-ridden...
;;; cloned-from = new!
(defparameter *built-in-non-inertial-fluent-slots*  '#$(add-list del-list pcs-list ncs-list block-projection-for #|cloned-from|#))
;;; the rest are all non-fluents

;;; Thank you to Roger Corman for this nice bit of code!
;;; Computes the list of non-fluent slots.
;;; As a side effect, it adds the non-fluent slots to the property list of
;;; all the slot names, under the property NON-FLUENT-SLOT (set to true).
;;;
(defun compute-built-in-non-fluent-slots ()
  (let ((ht (make-hash-table :test 'eq :size 200))
        (slots (set-difference *built-in-slots*
                               (append *built-in-inertial-fluent-slots* *built-in-non-inertial-fluent-slots*))))
    (dolist (x slots)
      (setf (gethash x ht) t))
    ht))

;;; May be recomputed if built-in-inertial-fluent-slots changes (see instance-of-is-fluent)
(defparameter *built-in-non-fluent-slots*
    (compute-built-in-non-fluent-slots))

;;; Let's allow the user to toggle these...
(defun instance-of-is-nonfluent ()
  (km-setq '*instance-of-is-fluent* nil)
  (km-setq '*built-in-inertial-fluent-slots* *default-built-in-inertial-fluent-slots*)
  (km-setq '*built-in-non-fluent-slots*
	(compute-built-in-non-fluent-slots)))

(defun instance-of-is-fluent ()
  (km-setq '*instance-of-is-fluent* t)
  (km-setq '*built-in-inertial-fluent-slots* (append  *default-built-in-inertial-fluent-slots* '#$(instance-of instances)))
  (km-setq '*built-in-non-fluent-slots*
	(compute-built-in-non-fluent-slots)))

;;; ----------

;;; For instances of these classes, KM *assumes* that the instances/instance-of relation will *not*
;;; vary between situations, and thus will only read and write to the global situation.
; NOTE: put in interpreter.lisp, so it can be loaded before use
;(defparameter *built-in-classes-with-nonfluent-instances-relation* '#$(Situation Slot Theory Partition))

;;; the rest are all non-fluents

;;; EXPRESSIONLESS SLOTS:
;;; The following slots can't have KM expressions as values, only
;;; atomic values. This is because they are accessed by optimized access methods
;;; (get-vals) which assume atomic values and make no attempt to
;;; evaluate any expressions found there. Also, their values are not unified together,
;;; they are set unioned, which means that find-vals will encounter a list of values,
;;; not a to-be-unifed value expression.
;;; NOTE: KM doesn't actually make the test of built-in-atomic-vals-only -- rather the assumptions of expressionlessness
;;; 	  are hard-wired into the code itself.
(defparameter *built-in-atomic-vals-only-slots*
; no longer used  (cons *tag-slot*
	'#$(domain range cardinality #|complete|# arity slots-to-opportunistically-evaluate locked-instances locked-instance-of
		   inverse inverse2 inverse3 inherit-with-overrides simple-inherit-with-overrides
		   superclasses subclasses instances
		   instance-of 		; (in fact may have constraints, but is handled in immediate-classes so it's as if atomic)
		   locked-instance-of locked-instances
		   supersituations members member-of
		   prototypes prototypes-of
		   prototype-participants prototype-participant-of
		   clone-built-from has-built-clones
		   cloned-from has-clones
		   domain-of range-of remove-subsumers remove-subsumees
		   subsituations subslots superslots id combine-values-by-appending dont-cache-values ignore-inverses
		   fluent-status called uniquely-called block-projection-for
		   ; assertions - no, needs to be processed, could have an arbitrary structure including #, etc.
		   ))

;;; DON'T attempt reasoning for these slots, just do a get-vals in the GLOBAL situation and you're done!
;;; They're essentially the *built-in-atomic-vals-only-slots* where inheritance is never expected.
;;; (Note: we might expect domain/range to inherit from slot classes, but let's assume not).
;;; NOTE: if instance-of is fluent, then we'd need to remove it from this list.
;;; (defparameter it earlier, as it's used earlier)
(setq *built-in-nonfluent-lookup-only-slots*
  (cons '#$prototype-scope
	(set-difference *built-in-atomic-vals-only-slots*
			'#$(members	   ; may be computed (e.g., in test-suite/constraints.km)
			    assertions)))) ; test-suite.km includes a assertion using #, so must process

;;; (every f has (s (v))), (every f has (s (v'))) -> (every f has (s (v v'))) NOT (every f has (s ((v) && (v'))))
;;; Also - all INVERSE assertions are automatically by appending; sigh and urgh!
(defparameter *built-in-combine-values-by-appending-slots*
  (append '#$(> < /== == add-list del-list pcs-list ncs-list prototype-scope) *built-in-atomic-vals-only-slots*))

;;; REMOVE-SUBSUMERS-SLOTS:
;;; These slots have classes as their values. For these slots, KM considers any subsuming values to
;;; be redundant and remove them, eg. (Car Vehicle) -> (Car).
(defparameter *built-in-remove-subsumers-slots* '#$(instance-of classes superclasses member-type))

;;; REMOVE-SUBSUMEES-SLOTS:
;;; These slots have classes as their values. For these slots, KM considers any subsumed values to
;;; be redundant and remove them, eg. (Car Vehicle) -> (Vehicle).
(defparameter *built-in-remove-subsumees-slots* '#$(subclasses prototype-of domain range))	; latter new (8/14/02)

;;; These better be complete!
;(defparameter *built-in-complete-slots* '#$(prev-situation next-situation)

;(defparameter *built-in-situation-specific-slots* '#$(add-list del-list pcs-list ncs-list))

;;; Only these built-in slots are allowed to have constraint expressions on them
(defparameter *built-in-slots-with-constraints* '#$(instance-of == < > called uniquely-called))

(defparameter *built-in-classes*
  '#$(Integer Number Thing Slot Aggregate Aggregation-Slot
	      Seq-Aggregation-Slot Bag-Aggregation-Slot Set-Aggregation-Slot
	      String Class Situation Boolean Partition
	      Exhaustive-Partition Cardinality Fluent-Status
	      Pair Triple Sequence Bag Theory Function))

;;; Note: Validation check: (length (remove-duplicates (flatten *built-in-superclass-links*))) = (length *built-in-classes*)
(defparameter *built-in-superclass-links*
    '#$((Integer Number)
	(Number Thing)
	(Pair Sequence)
	(Triple Sequence)
	(Sequence Thing)
	(Exhaustive-Partition Partition)
	(Partition Thing)
	(Set-Aggregation-Slot Aggregation-Slot)
	(Seq-Aggregation-Slot Aggregation-Slot)
	(Bag-Aggregation-Slot Aggregation-Slot)
	(Aggregation-Slot Slot)
	(Slot Thing)
	(Aggregate Thing)
	(Class Thing)
	(String Thing)
	(Boolean Thing)
	(Situation Thing)
	(Cardinality Thing)
	(Fluent-Status Thing)
	(Bag Thing)
	(Theory Thing)
	(Function Thing)
	))

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *built-in-instance-of-links*	; in addition to built-in Slots, which are instance-of Slot
    `#$((t Boolean)
	(f Boolean)
;	(T Boolean)		; no, this conflicts with the fassoc macro in immediate-classes so let's leave this out. We'll simply define T as a built-in-instance (only)
;	(F Boolean)		; no, let's leave F out, just use f lower-case
	(*Fluent Fluent-Status)
	(*Non-Fluent Fluent-Status)
	(*Inertial-Fluent Fluent-Status)
	(,*GLOBAL-SITUATION* Situation)))
)

;;; Make a fn to allow reference in an earlier file without problem
(defun built-in-instance-of-links () *built-in-instance-of-links*)

(defparameter *valid-fluent-statuses* '#$(*Fluent *Inertial-Fluent *Non-Fluent))

(defparameter *built-in-instances*
  (append *valid-cardinalities* *valid-fluent-statuses* `#$(t f T #|F|# ,*GLOBAL-SITUATION*)))

(defparameter *built-in-frames*
  (append *built-in-slots*
	  *built-in-classes*
	  *built-in-instances*))

;;; don't track inverses of these slots:
;;; [1] This is important, to stop the clone source being added to the object stack as a side-effect.
(defparameter *non-inverse-recording-slot*
; no longer used  (cons *tag-slot*
	'#$(prototype-scope cardinality aggregation-function #|complete|# add-list del-list pcs-list ncs-list
	     #|cloned-from|# #|label|# 							; [1]
	     inherit-with-overrides simple-inherit-with-overrides #|duplicate-valued|#
	     called uniquely-called arity nowexists
	     block-projection-for remove-subsumers remove-subsumees :incomplete
	     combine-values-by-appending dont-cache-values ignore-inverses
	     name == #|text print-name terms|#)) ;;; no! inverse2 inverse3

;;; eg. DON'T record inverses for T, eg. (T has (open-of (Box1))
(defparameter *non-inverse-recording-concept* *built-in-instances*)

;;; Return a string
(defun built-in-concept (concept) (member concept *built-in-frames*))

(defun built-in-slot (slot) (member slot *built-in-slots*))

(defun built-in-bag-aggregation-slot (slot) (member slot *built-in-bag-aggregation-slots*))
(defun built-in-seq-aggregation-slot (slot) (member slot *built-in-seq-aggregation-slots*))
(defun built-in-set-aggregation-slot (slot) (member slot *built-in-set-aggregation-slots*))
(defun built-in-aggregation-slot (slot) (member slot *built-in-aggregation-slots*))

(defun non-inverse-recording-slot (slot)
  (or (member slot *non-inverse-recording-slot*)
      (get-vals slot '#$ignore-inverses :situation *global-situation* :dereferencep nil)))

(defun non-inverse-recording-concept (concept) (member concept *non-inverse-recording-concept*))

(defun universalp (slot)
  (gethash slot *built-in-non-fluent-slots*))

(defun built-in-concept-type (concept)
  (cond ((member concept *built-in-single-valued-slots*) "single-valued slot")
	((member concept *built-in-multivalued-slots*) "multivalued slot")
	((member concept *built-in-classes*) "class")
	((member concept *built-in-instances*) "instance")))

(defun combine-values-by-appending-slotp (slot)
  (or (member slot *built-in-combine-values-by-appending-slots*)
      (member slot *neq-slots*)
      (get-vals slot '#$combine-values-by-appending :situation *global-situation* :dereferencep nil)))

(defun remove-subsumers-slotp (slot)
  (or (member slot *built-in-remove-subsumers-slots*)
      (get-vals slot '#$remove-subsumers :situation *global-situation* :dereferencep nil)))

(defun dont-cache-values-slotp (slot)
  (get-vals slot '#$dont-cache-values :situation *global-situation* :dereferencep nil))

(defun remove-subsumees-slotp (slot)
  (or (member slot *built-in-remove-subsumees-slots*)
      (get-vals slot '#$remove-subsumees :situation *global-situation* :dereferencep nil)))

;;; ======================================================================

(defparameter *val-constraint-keywords* '#$(must-be-a mustnt-be-a <> possible-values excluded-values
						     constraint no-inheritance retain-expr))
(defparameter *set-constraint-keywords* '#$(at-least at-most exactly set-constraint sometimes set-filter))
(defparameter *constraint-keywords* (append *val-constraint-keywords* *set-constraint-keywords*))
(defparameter *constraint-slots* '(== /== < >))

;;; ======================================================================

;;; Situations
(defvar *curr-situation* *global-situation*)

;;; ======================================================================

(defvar *classification-enabled* t)
;(defvar *postpone-classification* nil)
(defvar *postponed-classifications* nil)
(defvar *prototype-classification-enabled* t)		; i.e."triggers" in AURA
;(defvar *classification-disabled-temporarily* nil)	; reset to nil at each KM call, in case KM bombs when it's set to t
(defvar *installing-inverses-enabled* t)

(defun enable-classification ()
  (km-setq '*classification-enabled* t)
  (km-setq '*prototype-classification-enabled* t)
  '#$(t))

(defun disable-classification ()
  (km-setq '*classification-enabled* nil)
  (km-setq '*prototype-classification-enabled* nil)
  '#$(t))

(defun classification-enabled () *classification-enabled*)
;  (and *classification-enabled* (not *classification-disabled-temporarily*)))

;(defun temporarily-disable-classification () (km-setq '*classification-disabled-temporarily* t))
;(defun remove-temporary-disablement-of-classification ()
;  (km-setq '*classification-disabled-temporarily* nil))

(defun enable-installing-inverses () (cond ((not *installing-inverses-enabled*)
					    (setq *installing-inverses-enabled* t))) '#$(t))
(defun disable-installing-inverses() (setq *installing-inverses-enabled* nil) '#$(t))

;;; ======================================================================

; (defvar *slot-checking-enabled* nil)	 ; in header.lisp

(defun enable-slot-checking ()
  (km-format t "(Run-time checking of slot domain/range constraints enabled)~%")
  (km-setq '*slot-checking-enabled* t)
  t)

(defun disable-slot-checking ()
  (cond ((not *slot-checking-enabled*)
;	 (km-format t "(Run-time checking of slot domain/range constraints already disabled)~%")
	 )
	(t (km-format t "(Run-time checking of slot domain/range constraints disabled)~%")
	   (km-setq '*slot-checking-enabled* nil)))
  t)

;;; ======================================================================

;;; Format ((<slot> <subslot-list>) (<slot> <subslot-list>) .... )
(defconstant *built-in-subslots* nil)	; if change this, the EDIT immediate-subslots, immediate-superslots too!

(defparameter *built-in-inverses*
  '#$((inverse inverse)				; important!!
      (inverse2 inverse2)
      (inverse3 inverse3)
      (instances instance-of)
      (instance-of instances)
      (locked-instance-of locked-instances)
      (locked-instances locked-instance-of)
      (subslots superslots)
      (superslots subslots)
      (subclasses superclasses)
      (superclasses subclasses)
      (supersituations subsituations)
      (subsituations supersituations)
      (prototypes prototype-of)
      (prototype-of prototypes)
      (members member-of)
      (member-of members)
      (prototype-participants prototype-participant-of)
      (prototype-participant-of prototype-participants)
      (next-situation prev-situation)
      (prev-situation next-situation)
      (cloned-from has-clones)
      (has-clones cloned-from)
      (clone-built-from has-built-clones)
      (has-built-clones clone-built-from)
;      (views as)
;      (as views)
      (/== /==)))				; new 10/3/00

(defparameter *built-in-inverse2s* '#$(
      (next-situation after-situation)		; <S S' A>  -> <A S' S>
      (after-situation next-situation)
      (prev-situation before-situation)		; <S' S A> -> <A S S'>
      (before-situation prev-situation)))

;;; ======================================================================
;;;			COREFERENTIALITY
;;; ======================================================================

#|
Some frames are, in fact, typed variables. They are denoted by having
a name which begins with "_", eg _person34 is a "variable frame" of type
person. Variable frames can be bound to other frames. The unifier
(km/lazy-unify.lisp) is the thing which does the unifying.
|#

;;; bind: RESULT is irrelevant, only the side-effect is important.
;;; [1] - check to prevent circular bindings
;;; NOTE: frame2 is considered the result of the binding.
;(defun km-bind (frame1 frame2)
;  (cond ((not (eql (dereference frame1) (dereference frame2)))	; [1]
;	 (km-setf frame1 'binding frame2)
;	 (merge-cached-explanations frame1 frame2)
;	 (merge-explanations frame1 frame2))))

;;; REVISED To (optionally) allow ununification
(defparameter *allow-ununify* nil)

;;; Actually, we only need to cache old2-slotsvals for where there's an old1-slotsvals.
;;; Modified KM procedure.
;;; NOTE: ununify is not designed to handle things like (km-bind _Thing1 (:seq 1 2 3))
;;; (e.g., what would the ununify call look like in the first place?)
;;; See km-notes/ununify-notes.txt for more info
;;; [1] NOTE: We delete the frame contents but KEEP it as a known frame, as it has a binding still
;(defun km-bind (frame1 frame2)
;  (cond ((not (eql (dereference frame1) (dereference frame2))) ; [1]
(defun km-bind (frame1d frame2d)
  (let ((frame1 (dereference frame1d))	; 2/9/12 - no we need to bind the DEREFERENCED objects. Really the caller should ensure this, but we'll do it here
	(frame2 (dereference frame2d)))
  (cond ((not (eql frame1 frame2))
	 (cond
	  ((and *allow-ununify* (kb-objectp frame2))
	   (let* ((situations (all-active-situations))
		  (s+old2s (remove nil
				 (mapcar #'(lambda (situation)
					     (let ((old2-slotsvals (get-slotsvals frame2 :situation situation)))
					       (cond (old2-slotsvals (list situation old2-slotsvals)))))
					 situations)))
		  (old-ununify-data (get frame2 'ununify-data)))
	     (km-setf frame2 'ununify-data (cons (list frame1 s+old2s) old-ununify-data)))))
;	 (km-setf frame1 'binding frame2)		; NEW: Move AFTER the explanations are merged
	 (merge-cached-explanations frame1 frame2)
	 (merge-explanations frame1 frame2)
	 (delete-frame-structure frame1 :remove-from-kb-object-list nil) 	; Note is reversible, with an (undo) [1]
	 (km-setf frame1 'binding frame2)
	 ))))

; Optimized version from Francis Leboutte
;(defun get-binding (frame) (get frame 'binding))
(defun get-binding (frame)
  (declare (type symbol frame))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (get frame 'binding))

(defun bound (frame1) (get frame1 'binding))

;;; RENAMING CLASSES - not called directly from KM
(defun rename-class (old-class new-class)
  (cond ((eq old-class new-class)
	 (make-comment "(rename-class ~a ~a) - The two classes are identical (ignoring)!~%" old-class new-class))
	((neq (dereference old-class) old-class)
	 (report-error 'user-error
		       "(rename-class ~a ~a) - ~a has already been renamed (to ~a), so can't rename it again!~%"
		       old-class new-class old-class (dereference old-class)))
	((unusable-frame-name new-class)
	 (report-error 'user-error "(rename-class ~a ~a) - ~a is already in use, so can't rename to it!~%"
		       old-class new-class new-class))
	(t (km-put-list new-class (subst new-class old-class (km-symbol-plist old-class)))
	   (km-setf old-class 'binding new-class)
	   (km-add-to-kb-object-list new-class))))

;;; ----------

;;; This version is marginally slower on small dbs, marginally faster on large ones, but does less cons'ing (better memory)
;;; [1] frame may be a structure (eg. (:triple a b c), (x <- y), '(the size of _Situation23)) as well as an atom, hence recurse
(defun dereference (frame)
  (cond ((and *dereferencing-on* (needs-dereferencing frame)) (dereference0 frame))
	(t frame)))

#|
(defun dereference0 (frame)
  (declare (optimize (speed 3) (safety 0)))
  (cond ((null frame) nil)
	((symbolp frame)
	 (let ((binding (get-binding frame)))
 	   (cond (binding (dereference0 binding))
		 (frame))))
 	((listp frame)			; [1]
	 (let* ((frame0 (car frame))
		(rframe (cdr frame))
		(dframe0 (dereference0 frame0))
		(drframe (dereference0 rframe)))
	   (if (and (eql frame0 dframe0) (eql rframe drframe))
	       frame
	     (cons dframe0 drframe))))
 	(t frame)))

(defun needs-dereferencing (frame)
  (declare (optimize (speed 3) (safety 0)))
  (cond ((symbolp frame) (get-binding frame))
	((listp frame) (list-needs-dereferencing frame))))

(defun list-needs-dereferencing (list)
  (declare (optimize (speed 3) (safety 0))
	   (list list))
  (cond ((null list) nil)
	((symbolp list) (get-binding list))	 ; for recursive call when list = (a . b)
	(t (let ((list0 (car list))
		 (list1 (cdr list)))
	     (or (cond ((symbolp list0) (get-binding list0))
		       ((listp list0) (list-needs-dereferencing list0)))
		 (list-needs-dereferencing list1))))))
|#

;;; FEB 2012 - Modifications thanks to Roger Corman for 64 bit Allegro

#-:64BIT
(defun dereference0 (frame)
  (declare (optimize (speed 3) (safety 0)))
  (cond ((null frame) nil)
	((symbolp frame)
	 (let ((binding (get-binding frame)))
 	   (cond (binding (dereference0 binding))
		 (frame))))
 	((listp frame)			; [1]
	 (let* ((frame0 (car frame))
		(rframe (cdr frame))
		(dframe0 (dereference0 frame0))
		(drframe (dereference0 rframe)))
	   (if (and (eql frame0 dframe0) (eql rframe drframe))
	       frame
	     (cons dframe0 drframe))))
 	(t frame)))

#+:64BIT

(defun dereference0 (frame)
  (cond ((null frame) nil)
        ((symbolp frame)
         (let ((binding (get-binding frame)))
           (if binding
               (dereference0 binding)
             frame)))
        ((listp frame)
         (let ((new-list '()))
           (do* ((x frame (cdr x)))
                ((atom x)
                 (let* ((result (nreverse new-list)))
                   (unless (null x)  ;; handle dotted pairs
                     (setf (cdr (last result)) (dereference0 x)))
                   result))
             (push (dereference0 (car x)) new-list))))
        (t frame)))

(defun needs-dereferencing (frame)
  (declare (optimize (speed 3) (safety 0)))
  (cond ((symbolp frame) (get-binding frame))
	((listp frame) (list-needs-dereferencing frame))))

(defun list-needs-dereferencing (list)
  (declare (optimize (speed 3) (safety 0))
	   (list list))
  (cond ((null list) nil)
	((symbolp list) (get-binding list))	 ; for recursive call when list = (a . b)
	(t (let ((list0 (car list))
		 (list1 (cdr list)))
	     (or (cond ((symbolp list0) (get-binding list0))
		       ((listp list0) (list-needs-dereferencing list0)))
		 (list-needs-dereferencing list1))))))

;;; ======================================================================

;;; dereference things, INCLUDING nullifying deleted frames
;;; Note: deleted frames are NOT KB concepts, but may still be mentioned elsewhere in the KB.
;;; They should have no internal structure, as delete-frame deleted it all.
;;; RETURNS: The concepts that have changed, and any concepts that have been deleted (obsolete)
;;; NOTE: IF you do (rename-class <old> <new>), then <new> will NOT be in the list of
;;;       modified-concepts -- the modification (i.e., addition) was already performed earlier, so is not done here.
;;;	  <old> will be returned in the list of deleted concepts.
;;; NOTE: If :unintern t, then the deleted frames are uninterned. Thus the 2nd value returned, the deleted frames,
;;;	  will return uninterned symbols (i.e., in no package). The calling function should not make use of these, thus!
(defun dereference-kb (&key unintern)
  (let ((deleted-frame-alist (mapcar #'(lambda (f) `(,f . nil)) *deleted-frames*))
	(modified-concepts nil)
	(deleted-concepts nil))
    (mapc #'(lambda (concept)
	      (let* ((symbol-plist (symbol-plist concept))
		     (new-symbol-plist (sublis deleted-frame-alist (dereference symbol-plist))))
		(cond ((not (equal symbol-plist new-symbol-plist))
		       (setf (symbol-plist concept) new-symbol-plist)
		       (push concept modified-concepts)))))
;	  (get-all-concepts)	- no, misses comments
	  (mapcar #'dereference (get-all-objects))) ; note that comments also need to be dereferenced
    (mapc #'(lambda (concept)
	      (cond ((bound concept) (delete-frame-structure concept :unintern unintern) (push concept deleted-concepts))))
	  (get-all-objects))		; non-dereferenced list, includes things bound to other things
    (setq *deleted-frames* nil)
    (reset-creations)			; can't undo now, as the dereferencing is destructive
    (reset-history)
    (values modified-concepts deleted-concepts)))

#|
OLD LESS EFFICIENT
(defun dereference0 (frame)
  (cond ((symbolp frame)
	 (let ( (binding (get-binding frame)) )
	   (cond (binding (dereference0 binding))
		 (t frame))))
	((listp frame)				; [1]
	 (mapcar #'dereference0 frame))
	(t frame)))

(defun needs-dereferencing (frame)
  (cond ((symbolp frame) (get-binding frame))
	((listp frame) (some #'needs-dereferencing frame))))
|#
;;; ----------

(defun show-bindings ()
  (mapcar #'show-binding (get-all-objects)) (terpri) t)

; No - this won't unmerge explanations! See ununify below for more sophisticated but untested approach
;(defun unbind ()
;  (mapcar #'(lambda (frame) (km-bind frame  nil)) (get-all-objects)) t)

;;; _X -> _Y, then we (delete-frame _Y), means any old references to _X in the KB should now return nil.
;;; NOTE: 'deleted is a flag that we DO assert a value, and dereference returns NIL as a result.
; (defun bind-to-nil (frame) (km-bind frame 'deleted) t)

(defun show-binding (frame)
  (cond ((get frame 'binding)
	 (terpri) (km-format t "~a" frame) (show-binding0 (get-binding frame)))))

(defun show-binding0 (frame)
  (cond (frame (km-format t " -> ~a" frame)
	       (cond ((symbolp frame) (show-binding0 (get-binding frame)))))))

;;; ---------- UNUNIFICATION ---------- (new)

;;; Test
(defun ununifiable (frame2) (get frame2 'ununify-data))

(defun ununify (frame2)
  (let*
      ((ununify-data (get frame2 'ununify-data))
       (curr-situation (curr-situation))
       (f1+s-old2s (first ununify-data))
       (frame1 (first f1+s-old2s))
       (s+old2s (second f1+s-old2s)))
    (cond
     ((not *allow-ununify*)
      (make-comment "(ununify ~a): Ununification is turned off -- do (setq *allow-ununify* t) to enable it.~%" frame2))
     ((not (eql frame2 (dereference frame2)))
      (make-comment "~a doesn't exist any more - it become ~a through unification" frame2 (dereference frame2)))
     ((null ununify-data)
      (make-comment "~a: No bindings left to ununify" frame2))
     (t (km-bind frame1 nil)		; unbind
	(let ((s+old2s-deref (dereference s+old2s))) ; important (and  do after unbind)
	  (mapc #'(lambda (situation)
		    (let* ((s+old2 (assoc situation s+old2s-deref))
			   (old1-slotsvals (get-slotsvals frame1 :situation situation))
			   (old2-slotsvals (second s+old2))) ; may be nil
		      (cond
		       (old1-slotsvals
			(in-situation situation) ; for each situation
			(mapc #'(lambda (old1-slotvals)
				  (let* ((slot (slot-in old1-slotvals))
					 (old2-slotvals (assoc slot old2-slotsvals))
					 (old1-vals (km-flatten (vals-in old1-slotvals)))
					 (old2-vals (km-flatten (vals-in old2-slotvals)))
					 (old1-only-vals (remove-if-not #'(lambda (old1-val)
									    (and (kb-objectp old1-val)
										 (not (member old1-val old2-vals))))
									old1-vals))
					 )
;				    (km-format t "old1-vals = ~a~%" old1-vals)
;				    (km-format t "old2-vals = ~a~%" old2-vals)
;				    (km-format t "old1-only-vals = ~a~%" old1-only-vals)
; Remove old1-val from new2-vals inc inverses.
; NOTE: fast-delete-val in case old1-val is embedded in a ((_X) && (<old1-val>)) structure of the like
				    (mapc #'(lambda (old1-val) (fast-delete-val frame2 slot old1-val)) old1-only-vals)
; re-establish pointers back to frame1 (were removed after binding frame1 -> frame2)
				    (install-inverses frame1 slot old1-vals)
				    ))
			      old1-slotsvals)))))
		(all-active-situations)))
	(km-setf frame2 'ununify-data (rest ununify-data))
	(change-to-situation curr-situation) ; Revert back to original situation
	t))))

;;; Flattens any & and && structures
(defun km-flatten (vals) (find-exprs vals :expr-type 'non-constraint :plurality 'plural))

;;; ======================================================================
;;;		FRAME STRUCTURES (as defined in KM)
;;; ======================================================================
;;; A frame structure is the basic data structure which KM stores/retrieves
;;; (using getobj/putobj, defined in km/myload.lisp). The data structures
;;; are stored using LISP property lists, in the LISP property list DB.
;;;
;;;  SYMBOL   PROPERTY		VALUE (the slotsvals)
;;;	car   own-properties	( (color (*red)) (wheels (4)) )

(defun slot-in (slotvals) (first slotvals))

; Optimized version below from Francis Leboutte
;(defun vals-in (slotvals)
;  (cond ((listp (second slotvals)) (second slotvals))
;	(t (report-error 'user-error
;"Somewhere in the KB, the slot `~a' was given a single value `~a'
;rather than a list of values! (Missing parentheses?)~%"
;		         (first slotvals) (second slotvals)))))
(defun vals-in (slotvals)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (let ((second (second slotvals)))
    (if (listp second)
      second
      (report-error 'user-error
                    "Somewhere in the KB, the slot `~a' was given a single value `~a'
rather than a list of values! (Missing parentheses?)~%"
                    (first slotvals) second))))

(defun make-slotvals (slot vals) (list slot vals))

(defun are-slotsvals (slotsvals)
  (cond
   ((not (listp slotsvals))
    (report-error 'user-error "Bad structure ~a for list of slot-values!~%Should be of form (s1 (v1 ... vn)) (s2 (...)) ...)~%" slotsvals))
   (t (every
       #'(lambda (slotvals)
	     (cond
		((not (pairp slotvals))
		 (report-error 'user-error "Bad structure ~a for slot+values!~%Slot+values should be of the form (slot (v1 ... vn))~%" slotvals))
		((not (symbolp (slot-in slotvals)))
		 (report-error 'user-error "Bad structure ~a for slot+values!~%Slot `~a' should be a symbol!~%"
			       slotvals (slot-in slotvals)))
		((not (listp (second slotvals)))
		 (report-error 'user-error "Bad structure ~a for slot+values!~%Values ~a for slot ~a should be a list!~%"
			       slotvals (second slotvals) (slot-in slotvals)))
		((member (slot-in slotvals) *reserved-keywords*)
		 (report-error 'user-error "Bad structure ~a for slot+values!~%The slot `~a' is a reserved KM keyword, and cannot be used as a slot name!~%"
			       slotvals (slot-in slotvals)))
		((no-reserved-keywords (vals-in slotvals))		; generates its own error otherwise
		 (cond ((or (some #'(lambda (val) (and (listp val) (member (first val) *constraint-keywords*))) (vals-in slotvals))
			    (member (slot-in slotvals) *constraint-slots*))
			(note-are-constraints)))
		 (cond ((some #'km-defaultp (vals-in slotvals)) (km-setq '*are-some-defaults* t)))
		 (cond ((member (slot-in slotvals) '#$(called)) (km-setq '*are-some-tags* t)))
		 (cond ((member (slot-in slotvals) '#$(uniquely-called)) (km-setq '*are-some-tags* t) (km-setq '*are-some-constraints* t)))
;		 (cond ((member (slot-in slotvals) '#$(useful-views views)) (km-setq '*are-some-views* t)))
		 (cond ((member (slot-in slotvals) '#$(subslots superslots)) (km-setq '*are-some-subslots* t)))     ; optimization flag
		 (cond ((eq (slot-in slotvals) '#$prototype-of) (km-setq '*are-some-prototypes* t)))
		 t)))
	    slotsvals))))

;;; ======================================================================
;;; 		KB SET UTILITIES
;;; Below is the only bit of code which defines the internal storage
;;; of the KB -- for now, it's (setf <frame> 'kb <alist>).
;;; ======================================================================

#|
USED BY THESE FUNCTIONS
 - a-prototype ?class #$with &rest	   simple update of #$prototype-participants slot
 - create-named-instance 		   add-val newframe #$prototype-participant-of (curr-prototype)
 - try-classifying		           add-val instance '#$instance-of `(<> ,possible-new-parent) ; add constraint, to prevent further retries
 - install-inverses0			   install inverse
 - clean-taxonomy		   put subclasses link back
 - enforce-val-constraint		   add-val val '/== excluded-value) for excluded values
 - unify-in-prototype			   add-val instance '#$cloned-from prototype
 - clone0				   add-val instance '#$cloned-from prototype
|#

;;; RETURNS: irrelevant and discarded
; (defun add-vals (instance slot vals &optional (install-inversesp t) (situation (curr-situation)))
(defun   add-vals (instance slot vals &optional (install-inversesp t) (situation (target-situation (curr-situation) instance slot)))
  (mapc #'(lambda (val)
	    (add-val instance slot val install-inversesp situation))
	vals))

;;; add-val: add a value to a instance's slot.
;;; EXCEPT NB new value is simply added, not unified
;;;   [Reason: Don't want *red:: color-of: ((_car1) && (_car2) && (_car3))]
;;; [1] Unfortunately this won't catch all redundancies. Consider:
;;;     Suppose I say x isa y1, then x is a y2, then y1 is a y2.
;;;     The redundancy in x's superclasses won't be spotted. Soln = call (clean-taxonomy)
;;;	to recompute the taxonomy without redundancy.
;;; RETURNS: irrelevant and discarded
;;; [2] remove-dup-instances very expensive if lots of oldvals, and also redundant as it's done again during retrieval
;(defun add-val (instance slot val &optional (install-inversesp t) (situation (curr-situation)))
(defun  add-val (instance slot val &optional (install-inversesp t) (situation (target-situation (curr-situation) instance slot)))
  (let* ( (oldvals1 (get-vals instance slot :situation situation))	 ; includes dereferencing
; [2]	  (oldvals1 (remove-dup-instances oldvals0))    ; rem-dups does dereference also    - very inefficient if lots of values, and redundant!
	  (oldvals (cond ((single-valued-slotp slot) (un-andify oldvals1))
			 (t oldvals1))) )
;   (km-format t "add-val: oldvals1 = ~a, oldvals = ~a~%" oldvals1 oldvals)
    (cond
     ((null oldvals)
      (un-done instance :slot slot :situation situation)	; [rather than just (un-done instance)]
      (put-vals instance slot (list val) :install-inversesp install-inversesp :situation situation))
     ((member val oldvals :test #'equal))		; val is already there, everything uptodate
     ((single-valued-slotp slot)
           (un-done instance :slot slot :situation situation)  ; [rather than just (un-done instance)]
	   (put-vals instance slot
		     (val-to-vals (vals-to-&-expr (append oldvals (list val))))
		     :install-inversesp nil 		 ; install-inversesp would be ineffective here, as we've a STRUCTURE
		     :situation situation)
	   (cond (install-inversesp
		  (install-inverses instance slot (list val) situation))))	  ; NOW do it manually for the new value...
     ((remove-subsumers-slotp slot)	  				  ; eg. instance-of, superclasses. See [1]
      (cond ((some #'(lambda (oldval) (is-subclass-of oldval val)) oldvals)) ; don't need it
	    (t #|NEW|#	   (un-done instance :slot slot :situation situation)
	       (put-vals instance slot
;;; Unnecessary overwork! ->  (remove-subsumers (cons val oldvals))
#|NEW|#			      (cons val (remove-if #'(lambda (oldval) (is-subclass-of val oldval)) oldvals))
			      :install-inversesp install-inversesp :situation situation)
	       )))
     ((remove-subsumees-slotp slot)					  ; eg. subclasses
      (cond ((some #'(lambda (oldval) (is-subclass-of val oldval)) oldvals)) ; don't need it!
	    (t #|NEW|#	   (un-done instance :slot slot :situation situation)
	       (put-vals instance slot
;;; Unnecessary overwork! ->  (remove-subsumees (cons val oldvals))
#|NEW|#			      (cons val (remove-if #'(lambda (oldval) (is-subclass-of oldval val)) oldvals))
			      :install-inversesp install-inversesp :situation situation))))
     ((&&-exprp oldvals)
      (let ( (valsets (&&-exprs-to-valsets oldvals)) )
	  (cond
	   ((some #'(lambda (valset) (member val valset :test #'equal)) valsets))	 ; already there
	   (t (un-done instance :slot slot :situation situation)
	      (let ( (new-valsets (valsets-to-&&-exprs
				   (append (butlast valsets) (list (append (last-el valsets) (list val)))))) )
		(put-vals instance slot new-valsets
			  :install-inversesp install-inversesp :situation situation))))))
     (t (put-vals instance slot (append oldvals (list val)) :install-inversesp install-inversesp :situation situation))))) ; preserve order (nicer)

;;; ======================================================================
;;; (put-vals instance slot vals [&key facet install-inversesp situation])
;;; ======================================================================

#| USES OF put-vals:
frame-io.lisp:
 1. add-val - adding a value into a list of values/expressions.
 2. put-slotsvals: does (mapc #'put-vals slotsvals)
 3. delete-slot: (put-vals frame slot nil)
 4. delete-val: (not used in main KM)
 5. add-slotsvals
[ 6. add-immediate-class (after classification is done) - adds the recomputed classes. Later: changed to be add-vals ]
 7. immediate-classes: after computing new superclasses, put the *result* back in
 8. immediate-classes0: after doing projection. This is followed by a note-done
 9. prev-situation: store previous situation
10. before-situation: similar
11. uninstall-inverses
12. eval-constraints (as part of eval-instances)
13. remove-redundant-superclasses (part of install-subclasses)

interpreter.lisp:
 1. after looping, if expression is a (the x of y) then do a get-vals (rather than get-slotvals-from-kb), evaluate the result, and put-vals it back.
 2. if slot - name, then compute the name (using (name frame)) and cache the name using put-vals.

get-slotvals.lisp:
 1. for the intermediate save
 2. for recursive rulesets
 3. after you're finally done. note-done follows.

lazy-unify.lisp:
 1. if you compute values on a slot, then put the results back on the slot. Note this may clobber rules previously on the slot. Hmm...
 2. unify-with-slotsvals2, called by unify-with-existential-expression: putting the results of unification back into the KB

Now: which ones of these might result in an own-rule in the global situation being clobbered?
|#

#|
IF vals is nil, this will delete a slot (and its value) from a instance.
If vals is non-nil, the new vals will overwrite the old vals.
	**NOTE** DOESN'T remove inverse links or scan through situations for any deleted old vals, so you shouldn't
	use put-vals to destructively change vals unless you are absolutely sure no inverses need removing. (Instead,
	use (X now-has Y) which does handle inverses)
NOTE: vals can validly be NIL, in the case where (i) lazy-unify may put a *path*
on an instance's slot, then (ii) it later is evaluated to NIL. So in that case, a put-vals with NIL will
remove that cached path.
This DOESN'T require that the right situation has been identified, here the determination of target-situation is done WITHIN this procedure
[1] NOTE: Normally:
     (km '#$(_Cat1 has (color ((*black [comment1])))))
will assert
     (_Car1 has (color (*black)))	and an explanation (_Car1 color *black) (*black [comment1])
This is fine, with one exception:
     (km '#$(_Cat1 has (prototype-scope ((the-class Cat [comment1])))))
When we assert this, we DO need to retain the comment tags, as when testing prototype-scope, we:
	(i) check a new instance is covered by the prototype-scope
	(ii) call (record-explanation-for instance new-class `(,instance isa ,prototype-scope)) in prototypes.lisp
In the latter case, we need to retain the comments in the prototype-scope expression.
|#
(defvar *trace-prototype-assertions* nil)

;(defun put-vals (instance slot vals0 &key (facet 'own-properties) (install-inversesp t) (situation (curr-situation)))
(defun  put-vals (instance slot vals0 &key (facet 'own-properties) (install-inversesp t) (situation (target-situation (curr-situation) instance slot)))
  (cond
   ((and (some #'protoinstancep (cons instance vals0))
	 (neq situation *global-situation*))
    (report-error 'user-warning
			 "Attempt to assert fact about protoinstance(s) ~a in a local situation (~a) - not allowed!
         All protoinstance facts should be asserted in the global situation.
         I was asserting (~a has (~a ~a)) in ~a.
         I will recover by asserting this fact in the global situation (*Global) instead....~%"
			 (delistify (remove-if-not #'protoinstancep (cons instance vals0))) situation
			 instance slot vals0 situation)
    (put-vals instance slot vals0 :facet facet :install-inversesp install-inversesp :situation *global-situation*))
   (t (cond ((and *trace-prototype-assertions*	; This error check is purely for debugging. Only switch on when changes to prototypes are *NOT* being made.
		(some #'protoinstancep (cons instance vals0))
		(not (am-in-prototype-mode))
		(anonymous-instancep instance)
		(not (member slot '#$(instances ; instance-of
				    prototypes ; prototype-of
;				    prototype-scope
				    has-clones cloned-from
				    has-built-clones clone-built-from
;				    prototype-participants prototype-participant-of
				    ))))
	     (report-error 'user-error
			 "Attempt to assert with protoinstance(s) ~a when not in prototype mode!~%         Doing (the ~a of ~a) = ~a~%"
			 (delistify (remove-if-not #'protoinstancep (cons instance vals0)))
			 slot instance vals0)))
      (let* ((vals (cond ((and (member facet '(own-properties own-definition))
			       (not (eql slot '#$prototype-scope))) ; [1]
			  (remove-sources-from-vals instance slot vals0))
			 (t vals0)))
	     (class-vals (cond ((eq slot '#$superclasses) (cons instance vals)) ; specifically for disjointness test, to spot
			       (t vals)))) ; (X superclasses Y) violates Partition {X Y}
	(cond (*slot-checking-enabled* (check-domain-and-range instance slot vals)))
	(cond
	 ((member instance *reserved-keywords*)
	  (report-error 'user-error "Attempt to use keyword `~a' as the name of a frame/slot (not allowed!)~% Doing (~a has (~a ~a))~%"
			instance instance slot vals))
	 ((not (kb-objectp instance))
	  (report-error 'program-error "Attempting to assert information on a non-kb-object ~a...~%Ignoring the slot-vals (~a ~a)~%"
			instance slot vals))

	 (t
	  (cond ((and (not (isa slot '#$Slot)) ; Do this *after* checking instance-of above!
		      *coerce-undeclared-slots*)
		 (add-val slot '#$instance-of '#$Slot t *global-situation*))) ; install-inversesp = t
	  (let* ( ; (target-situation (target-situation situation instance slot vals)) ; compute target situation AFTER potentially changing fluent status
		 (target-situation situation) ; 1/24/11 - PEC No, that's overly complex and not needed I think
		 (old-slotsvals (get-slotsvals instance :facet facet :situation target-situation))
		 (old-vals (vals-in (assoc slot old-slotsvals))) )

;;; Below is too slow with a large KB, so make it switchable (default off). We do this in case obj stack is flushed
;;; (requested by Andre Renard)
	    (cond (*active-obj-stack* (mapc #'push-to-obj-stack `(,instance ,@vals))))

	    (cond
	     ((equal vals old-vals) vals)
	     (t (let ( (putobj-facet (curr-situation-facet facet target-situation)) )
		  (cond ((not (known-frame instance)) (push-to-obj-stack instance))) ; new, 3.7.00
		  (cond ((null vals)
			 (putobj instance (remove-assoc-entry slot old-slotsvals) putobj-facet))
			(t (putobj instance (update-assoc-list old-slotsvals (make-slotvals slot vals)) putobj-facet)
			   (cond ((eq slot '#$prototype-scope)
				  (mapc #'(lambda (val)
					    (let ((parent-classes
						   (cond ((kb-objectp val) (list val)) ; Cat
							 ((class-descriptionp val :fail-mode 'error) ; (the-class Cat)  - KB error otherwise!
;						      (list (first (class-description-to-class+slotsvals val)))
							  (classes-in-description val)) ; better - get *all* the classes (the-class C1 with (instance-of (C2)))
							 )))
					  ;;; NOTE: Nov 2009: Added this so that (classify ...) also considers unifying
					  ;;; in prototypes, hence doing eager classification with prototypes.
					  ;;; Note that even single class prototype-scopes are registered here, as they
					  ;;; are still considered worth unifying in.
					  ;;; In addition, all-applicable-prototypes was modified to use this info.
					      (point-parents-to-defined-concept instance parent-classes
										'prototype-definition
										:simple-classp (kb-objectp val))))
					vals)))
			   (cond ((and (member facet '(own-definition own-properties))
				       install-inversesp)
				  (install-inverses instance slot (ordered-set-difference vals old-vals) target-situation)))

			   (cond ((and (eq slot '#$members)
				       (isa instance '#$Partition))
				  (let* ((subclasses (append vals (my-mapcan #'all-subclasses vals))))		; append vals, to spot error with partition (A B) given (A has (superclasses (B)))
				    (cond ((/= (length subclasses) (length (remove-duplicates subclasses)))
					   (let ((violated (remove-duplicates (bag-difference subclasses (remove-duplicates subclasses)))))
					     (report-error 'user-warning
							  "Partition violation! This new partition ~a with members ~a is violated by class(s):~%~a~%" instance vals (delistify violated))))))))

	 ;;; REVISED: Replace user-error with user-warning, because we want AURA to continue in the face of a partition violation (so instances don't spontaneously fail to be created)
			   (cond ((member slot '#$(instance-of superclasses))
				  (cond ((disjoint-classes (remove-if-not #'kb-objectp class-vals) :check-singletonp t)
					 (let* ((violated-partitions (remove-duplicates
								      (remove-singletons
								       (disjoint-classes (remove-if-not #'kb-objectp class-vals) :check-singletonp t))))) ; :check-singletonp t - do extra work to find indirect problems
					   (report-error 'user-warning `(|partition-violation| ,instance ,slot ,class-vals ,violated-partitions) ;   (_X1 instance-of X) but (X has (superclasses (Y NonY)))
							 (cond ((singletonp vals)
								"Partition violation! (~a has ~a ~a):~%The superclasses of this class ~a are mutually exclusive, partition(s) ~a were violated.~%~:{     ~a:~25t~a~%~:}")
							       (t "Partition violation! (~a has ~a ~a):~%These classes ~a or their superclasses are mutually exclusive, partition(s) ~a were violated.~%~:{     ~a:~25t~a~%~:}"))
							 instance slot vals (delistify vals) (delistify violated-partitions)
							 (mapcar #'(lambda (violated-partition) (list violated-partition (get-vals violated-partition '#$members))) violated-partitions)))))
				  (cond ((eq slot '#$superclasses) ; also need to check all these subclasses, e.g., Partition = (X Y) (A superclasses (X B)) then (B superclasses Y) -> need to check A
					 (mapc #'(lambda (subclass) (violated-partitions-at-class subclass :indirectp t)) (remove-duplicates (my-mapcan #'all-subclasses class-vals)))))))

;		       (cond ((and *are-some-views*
;				   (eq slot '#$instance-of))
;			      (install-views instance (remove-if #'constraint-exprp (set-difference vals old-vals)))))
			   ))))))))
	instance))))

;;; This function now ONLY ever used by lazy-unify.lisp
(defun put-slotsvals (frame slotsvals &key (facet 'own-properties) (install-inversesp t) (situation (curr-situation)))
    (mapc #'(lambda (slotvals)
	      (put-vals frame (slot-in slotvals) (vals-in slotvals) :facet facet :install-inversesp install-inversesp :situation situation))
	  (reorder-slotsvals slotsvals))
    frame)

;;; Reorder the slotsvals, to make sure instance-of links are FIRST. This is important so that the domain/range checking knows the
;;; correct instance-of links *before* the checking is done!
(defun reorder-slotsvals (slotsvals)
  (let ( (instance-of-slotvals (assoc '#$instance-of slotsvals)) )
    (cond (instance-of-slotvals (cons instance-of-slotvals (remove-if #'(lambda (slotvals) (eq (slot-in slotvals) '#$instance-of)) slotsvals)))
	  (t slotsvals))))

;;; --------------------

;;; ONLY used by KM itself to remove redundant superclasses, nowhere else within KM (though outside applications my use it)
(defun delete-val (instance slot val &optional (uninstall-inversesp t)
  						(situation (target-situation (curr-situation) instance slot)))
  (let* ( (oldvals0 (get-vals instance slot :situation situation))
	  (oldvals1 (remove-dup-instances oldvals0))    ; rem-dups does dereference also
	  (oldvals (cond ((single-valued-slotp slot) (un-andify oldvals1))
			 (t oldvals1))) )
    (cond ((not (member val oldvals :test #'equal))
	   (km-format t "Warning! Trying to delete non-existent value ~a on (the ~a of ~a)!~%" val slot instance))
	  ((single-valued-slotp slot)
	   (let ((new-val (vals-to-&-expr (remove val oldvals :test #'equal))))
	     (put-vals instance slot (cond (new-val (list new-val))) :install-inversesp nil :situation situation))
					; uninstall-inversesp would be ineffective here, as we've a STRUCTURE
	   (delete-explanation instance slot val :explanation-to-delete 'all :situation situation)
	   (cond (uninstall-inversesp
		  (uninstall-inverses instance slot (list val) situation) ; NOW do it manually for the new val
; Moved to uninstall-inverses
; 		  (delete-explanation val (invert-slot slot) instance :explanation-to-delete 'all :situation situation)
		  ))
	   (un-done instance :situation situation) ; 1.4.0-beta8: Don't forget this! Important!!
	   t)
	  (t (put-vals instance slot (remove val oldvals :test #'equal) :install-inversesp nil :situation situation)
	     (delete-explanation instance slot val :explanation-to-delete 'all :situation situation)
	     (cond (uninstall-inversesp
		    (uninstall-inverses instance slot (list val) situation) ; NOW do it manually for  new val
		    (delete-explanation val (invert-slot slot) instance :explanation-to-delete 'all :situation situation)))
	     (un-done instance :slot slot :situation situation)	; 3/28/08 - for good measure
	     t))))

;;; Simpler than delete-val above: just put a nil in for the to-be-deleted value. I *think* this is ok!
;;; NOTE: This is NOT used anywhere in KM or outside, and so is not really tested.
(defun fast-delete-val (instance slot val0 &optional (uninstall-inversesp t)
						(situation (target-situation (curr-situation) instance slot)))
  (let* ((val (dereference val0))
	 (old-vals (get-vals instance slot :situation situation))
	 (new-vals (subst nil val old-vals)))
    (cond ((not (equal new-vals old-vals))
	   (put-vals instance slot new-vals :install-inversesp nil :situation situation)
	   (cond (uninstall-inversesp (uninstall-inverse instance slot val situation)))))))

;;; Only used by fast-delete-val above
; (defun uninstall-inverse (frame slot val0 &optional (situation (curr-situation)))
(defun   uninstall-inverse (frame slot val0 &optional (situation (target-situation (curr-situation) frame slot)))
  (cond ((not (non-inverse-recording-slot slot))
	 (let ((invslot (invert-slot slot))
	       (val (dereference val0)))
	   (cond ((and (kb-objectp val)
		       (not (non-inverse-recording-concept val))) ; eg. don't want boolean (T has (open-of (Box1))
		  (let* ((old-vals (get-vals val invslot :situation situation))
			 (new-vals (subst nil frame old-vals)))
		    (cond ((not (equal new-vals old-vals))
			   (put-vals val invslot new-vals :install-inversesp nil :situation situation))))))))))


;;; ----------------------------------------------------------------------
;;;		IMPORTANT UTILITY
;;; Want to find slot values in situation X? Get/Put from situation X'
;;; ----------------------------------------------------------------------

#|
--------------------
Known (but irrelevant) bug below:
KM> (instance-of-is-fluent)
[_Situation1] KM> (showme adf)
(adf has (instance-of (Slot)))
(in-situation _Situation1 (adf has (instance-of (Foo))))

KM> (the all-classes of adf)
(Thing Foo Slot)

KM> (showme adf)
(adf has (instance-of (Foo Slot)))	; Foo added in global!

(in-situation _Situation1 (adf has (instance-of (Foo))))

Because [1] we just need *one* val to be a *built-in-classes-with-nonfluent-instances-relation*, KM will
put *all* values up in global. (It'd be too complicated to put some values here, some elsewhere - the
extra effort is not worth solving this issue, only for the classes Slot, Partition, Theory, and Situation.)
--------------------
|#
;;; GIVEN: you're either putting frame slot vals, or getting from frame slot,
;;; RETURN: the target situation to put/get vals to/from.
(defun target-situation (situation instance slot &optional vals)
  (cond ((eq situation *global-situation*) *global-situation*)	; efficiency: Avoid needless lookups for (fluentp slot)
	((and slot (universalp slot)) *global-situation*) ; NB fluent -> non-universal, by definition
	((and slot (protoinstancep instance)) *global-situation*) ; All prototype info is in global
	((and slot
	      (nor (fluentp slot)
		   (isa-theory situation))) *global-situation*) ; instance-of will normally pass this test
	((and (eq slot '#$instance-of)				; special handling for when (instance-of-is-fluent) is true
	      (some #'(lambda (val)
			(some #'(lambda (class) (is-subclass-of val class)) 	; e.g. (put-vals _Sit1 instance-of Situation)
			      *built-in-classes-with-nonfluent-instances-relation*)) ;				   ^^ val ^^
		    vals))
	 *global-situation*)
	((and (eq slot '#$instances)
	      (some #'(lambda (class) (is-subclass-of instance class))		; e.g. (put-vals Situation instances _Sit1)
		    *built-in-classes-with-nonfluent-instances-relation*))	;		 ^instance^
	 *global-situation*)
	(t situation)))

;;; ======================================================================
;;;		LOCAL ACCESS TO A SLOT'S VALUES
;;; ======================================================================

;;; This *doesn't* climb the supersituation hierarchy -- need to do this to stop looping
;;; find-vals -> supersituation -> find-vals -> supersituation....
;;; RETURNS A DEREFERENCED ANSWER (unless explicitly blocked from doing so)
;;; NOTE: We assume a PREPROCESSOR has determined the right situation to get from, using a call to (target-situation situation frame slot)
;;; [1] MODIFIED Feb04: add the target-situation finder here for the special case where situation is not specified
; [1]  get-vals (frame slot &key (facet 'own-properties) (situation (curr-situation))                               (dereferencep t))
(defun get-vals (frame slot &key (facet 'own-properties) (situation (target-situation (curr-situation) frame slot)) (dereferencep t))
  (cond ((and (symbolp slot)
;	      (is-km-term frame))		; bug
	      (kb-objectp frame))
	 (cond (dereferencep (dereference (vals-in (assoc slot (get-slotsvals frame :facet facet :situation situation :dereferencep nil)))))
	       (t (vals-in (assoc slot (get-slotsvals frame :facet facet :situation situation :dereferencep nil)))))) ; deref=nil
	((not (symbolp slot))
	 (report-error 'user-error "Doing (the ~a of ~a) - the slot name `~a' should be a valid KB object (a non-keyword symbo)l!~%" slot frame slot))
	(t (report-error 'user-error "Doing (the ~a of ~a) - the frame name `~a' should be a valid KB object (a non-keyword symbol)!~%" slot frame frame))))

;;; Get from multiple frames:
(defun gets-vals (frames slot &key (facet 'own-properties) (situation (target-situation (curr-situation) (first frames) slot)) (dereferencep t))
  (remove-duplicates
   (my-mapcan #'(lambda (frame)
		  (get-vals frame slot :facet facet :situation situation :dereferencep dereferencep))
	      frames)
   :test #'equal
   :from-end t))

;;; ----------

; (defun get-unique-val (frame slot &key (facet 'own-properties) (situation (curr-situation)) (fail-mode 'fail))
(defun get-unique-val (frame slot &key (facet 'own-properties) (situation (target-situation (curr-situation) frame slot)) (fail-mode 'fail))
  (let ( (vals (get-vals frame slot :facet facet :situation situation)) )
    (cond ((singletonp vals) (first vals))
	  (vals (report-error 'user-error
			      "(the ~a of ~a) should have at most one value,~%but it returned multiple values ~a!~%Just taking the first...(~a) ~%"
			      slot frame vals (first vals))
		(first vals))
	  ((eq fail-mode 'error)
	   (report-error 'user-error "No value found for the ~a of ~a!~%" slot frame)))))

;;; ----------

;;; RETURNS A DEREFERENCED ANSWER (unless explicitly blocked from doing so)
(defun get-slotsvals (frame &key (facet 'own-properties) (situation (curr-situation)) (dereferencep t))
  (cond (dereferencep (dereference (getobj frame (curr-situation-facet facet situation))))
	(t (getobj frame (curr-situation-facet facet situation)))))

;;; ----------------------------------------
;;; NEW - same thing, but just deal with member properties. A "ruleset" is a list of expressions on
;;; some class's slot, which should be applied to instances of that class.
;;; Here we collect both `assertional' and `definitional' rules; it'd be nice to ignore the definitional
;;; rules, or just take them if no assertional rules, but that would be incomplete wrt. the intended
;;; semantics.
;;; We have to search in two dimensions: (1) up the isa hierarchy and (2) up the situation hierarchy.


#|
NEW: IF   supersituation S1 yields the rule (a ...)
     AND  instance exists in S1
     THEN it is redundant to also evaluate the expression in situation,
	  as it will already have been evaluated in S1 and passed to instance through
          "situation inheritance".

So, we return two values:
  (<expr1> ...)		; exprs to evaluate in situation
  (<expr1> ...)		; redundant expressions (will already have been evaluated in supersituations)
|#
;;; ---------- search ALL situations and classes

;(defun inherited-rule-sets (instance slot &key (situation (curr-situation))
(defun  inherited-rule-sets (instance slot &key (situation (target-situation (curr-situation) instance slot))
					       retain-commentsp (climb-situation-hierarchyp t)
					       ignore-inherit-with-overrides-restriction)
  (let ((rulesets+classes (inherited-rulesets+classes instance slot :situation situation
						      :retain-commentsp retain-commentsp
						      :climb-situation-hierarchyp climb-situation-hierarchyp
						      :ignore-inherit-with-overrides-restriction
						      ignore-inherit-with-overrides-restriction
						      )))
    (remove-duplicates (append-lists (mapcar #'first rulesets+classes)) ; strip off classes
		       :test #'equal :from-end t)))

;;; RETURNS: a list of (<class> (<ruleset1> <ruleset2>...))
(defun inherited-rulesets+classes (instance0 slot &key ; (situation (curr-situation))
						         (situation (target-situation (curr-situation) instance0 slot))
							 retain-commentsp
							 (climb-situation-hierarchyp t) ignore-inherit-with-overrides-restriction)
  (let* ((instance (dereference instance0))
	 (all-situations (cond ((not climb-situation-hierarchyp) (list situation))
				((and (neq situation *global-situation*) (fluentp slot))
				 (cons situation (all-supersituations situation)))
				(t (list *global-situation*))))
	  (visible-theories (visible-theories)) )
    (cond ((and (inherit-with-overrides-slotp slot) (not ignore-inherit-with-overrides-restriction))
	   (desource+decomment
	    (bind-self (inherited-rule-sets+classes-with-overrides slot (immediate-classes instance) (append all-situations visible-theories)) instance)
	    :retain-commentsp retain-commentsp))
	  (t (desource+decomment
	      (bind-self (inherited-rule-sets+classes2 slot (all-classes instance) (append all-situations visible-theories)) instance)
	      :retain-commentsp retain-commentsp)))))

;;; ---------- STOP after you've found something

;;; Slots are declared to use this by setting their "inherit-with-overrides" property to t
;;; REVISED 8.16.00:
;;; With multiple inheritance, climb up all the branches stopping at the point(s) where you hit a rule.
;;; REVISED 12.11.00:
;;; Don't bother also ascending situation hierarchy, instead use all situations immediately
;;; RETURNS: A list of rulesets+class pairs
(defun inherited-rule-sets+classes-with-overrides (slot classes all-situations)
  (mapcan #'(lambda (class)
	      (inherited-rule-sets+classes-with-overrides2 slot class all-situations))
	  classes))

;;; Simpler version, strip off classes
(defun inherited-rule-sets-with-overrides (slot classes all-situations)
  (let ((rulesets+classes (inherited-rule-sets+classes-with-overrides slot classes all-situations)))
    (remove-duplicates (append-lists (mapcar #'first rulesets+classes)) ; strip off classes
		       :test #'equal :from-end t)))

;;; RETURNS: A list of rule sets. Is MAPCAN-SAFE
;;; [1] e.g., rule-sets+classes = (((((mustnt-be-a Formula))) Hydrocarbon-Molecule))
(defun inherited-rule-sets+classes-with-overrides2 (slot class all-situations)
  (let ((rule-sets+classes (inherited-rule-sets+classes2 slot (list class) all-situations)))   ; [1]
    (cond (
	   (some #'(lambda (rule-sets+class)
		     (some #'(lambda (rule-set)
			       (some #'(lambda (rule)
					 (not (constraint-exprp rule)))
				     rule-set))
			   (first rule-sets+class)))
		 rule-sets+classes)
	   rule-sets+classes)	; found something (which isn't just a constraint)! So stop along this (upward) branch.
	  ((neq class '#$Thing)
	   (inherited-rule-sets+classes-with-overrides slot (immediate-superclasses class) all-situations)))))

;;; ----------
(defun inherited-rule-sets2 (slot classes situations)
  (let ((rulesets+classes (inherited-rule-sets+classes2 slot classes situations)))
    (remove-duplicates (append-lists (mapcar #'first rulesets+classes)) ; strip off classes
		       :test #'equal :from-end t)))

;;; Find all the rule sets on all the classes in all the situations
;;; Is MAPCAN SAFE
;;; RETURNS: A list of rulesets+class pairs
(defun inherited-rule-sets+classes2 (slot classes situations)
  (remove nil				; tidy up answer...
   (mapcar #'(lambda (class)
	       (let ((rule-sets (remove-duplicates
				 (remove nil (mapcan #'(lambda (situation)
							 (get-rule-sets-in-situation class slot situation))
						     situations))
				 :test #'equal)))
		 (cond (rule-sets (list rule-sets class)))))
	   classes)))			; (includes situation)

#|
RETURNS: a LIST of VALUE-SETS
(Essentially a synonym for get-vals)
IS MAPCAN-SAFE [due to &&-exprs-to-valsets, and &-expr-to-vals]
[1] UNPACK '&&' sets, ie. If one rule set is (set1 && set2), return (set1 set2), not (((set1 && set2)))
These && sets might be created by the user through multiple (every ... has ...) statements for the same slot,
or created by KM during unification.
USER(45): (mapcar #'list
		  (append (mapcan #'&-expr-to-vals '(1 2 (3 & 4)))
			  (mapcan #'&-expr-to-vals '((3 & 4)))))
((1) (2) (3) (4) (3) (4))
|#
(defun get-rule-sets-in-situation (class slot situation)
  (cond ((single-valued-slotp slot)
	 (mapcar #'list
		 (remove-duplicates
		  (append (mapcan #'&-expr-to-vals (get-vals class slot :facet 'member-properties :situation situation))
			  (mapcan #'&-expr-to-vals (get-vals class slot :facet 'member-definition :situation situation)))
		  :test #'equal :from-end t)))
	(t (append (&&-exprs-to-valsets (get-vals class slot :facet 'member-properties :situation situation))
		   (&&-exprs-to-valsets (get-vals class slot :facet 'member-definition :situation situation))))))


;;; Climb up situation hierarchy collecting instance data
;;; [1] should be "and" rather than "or", but let's use "or" for efficiency
;;; Note, supersituation-own-rule-sets has the EXTRA FUNCTIONALITY of REMOVING fluent instances.
;;; [2] Given this, we better make sure that for non-fluents, we start in the right situation (global),
;;;	so we *don't* remove fluent instances then. Hmmm....
;(defun own-rule-sets (instance slot &key retain-commentsp (situation (curr-situation)))
(defun  own-rule-sets (instance slot &key retain-commentsp (situation (target-situation (curr-situation) instance slot)))
  (cond
   ((kb-objectp instance)
    (let ( (start-situation (target-situation situation instance slot)) ) ; [2]
      (desource+decomment
       (bind-self
	(remove nil
		(append
		 (&&-exprs-to-valsets (or (get-vals instance slot :facet 'own-properties :situation start-situation)
					  (get-vals instance slot :facet 'own-definition :situation start-situation)))
		 (supersituation-own-rule-sets instance slot :situation start-situation :retain-commentsp retain-commentsp)))
	instance)
       :retain-commentsp retain-commentsp)))))


#|
Collect all the local expr-sets of slot from all supersituations of situation [*NOT* including situation itself]
This is similar to own-rule-sets, except it *doesn't* look in the current situation.
It also filters our fluent instances, which *shouldn't* be propogated down the taxonomy.
Presumably, own-rule-sets should do this too.
If situation = *Global, then this procedure just searches (visible-theories)
[1] Ie has a previous situation, it's not the first in the chain
[2] Special-purpose code for clones:
	ALL cloned info is put in the GLOBAL situation
        BUT we need to allow for the FLUENT cloned information to be RETRACTED. The only easy way of
	 doing this is to ONLY pass fluent cloned information from *Global to a local situation in the
	 FIRST situation in a situation chain. From then on, it will be passed by projection.
|#
;(defun supersituation-own-rule-sets (instance slot &key retain-commentsp (situation (curr-situation)))
(defun supersituation-own-rule-sets (instance slot &key retain-commentsp (situation (target-situation (curr-situation) instance slot)))
  (cond
   ((and (isa-clone instance)								; [2]
	 (neq situation *global-situation*)
	 (inertial-fluentp slot)
	 (get-vals situation '#$prev-situation :situation *global-situation*))   ; [1]
    nil)
   ((kb-objectp instance)
    (let ( (all-supersituations (cond ((and (neq situation *global-situation*)
					      (fluentp slot))
					 (all-supersituations situation))))
	     (visible-theories (visible-theories)) )
	(desource+decomment
	 (remove-duplicates
	  (remove nil
		  (my-mapcan #'(lambda (sitn)
				 (&&-exprs-to-valsets
; Not used any more		  (recursive-remove-fluent-instances	; in case of ((_someCar1 & (must-be-a Car))
				   (or (get-vals instance slot :facet 'own-properties :situation sitn)     ; This disjunct should be in get-vals-
				       (get-vals instance slot :facet 'own-definition :situation sitn))))  ; in-situation, not here,+ should be conj!
			     (append all-supersituations visible-theories)))
	  :test #'equal :from-end t)
	 :retain-commentsp retain-commentsp)))))

;;; ----------

;;; Find all the constraints on an instance's slot.
;;; RETURNS: a list of constraint expressions
;;; NOTE: This won't collect constraints on subslots
;;; [1] retain-commentsp t for efficiency, we'll remove them later.
;;; [2] Actually, this decomment step is redundant because find-constraints-in-exprs ALWAYS does a decomment anyway!
(defun collect-constraints-on-instance (instance slot &key retain-commentsp ignore-prototypes
;							   (situation (curr-situation)))
							   (situation (target-situation (curr-situation) instance slot)))
  (let ((constraints+sources
	 (collect-constraints+sources-on-instance instance slot :situation situation :retain-commentsp retain-commentsp
						  :ignore-prototypes ignore-prototypes)))
    (remove-duplicates (mapcar #'first constraints+sources) :test #'equal :from-end t)))

;;; RETURNS: a list of (<constraint> <sources>) where <sources> is a list of sources where <constraint> was found
;;; Each <source> in <sources> is either a CLASS or an INSTANCE or (cloned-from <prototype-root> <clone-root>)
;;; For constraints from UNCLONED prototypes, <source> is simply CLASS of the prototype
;;; Used for AURA - see aura-api.txt
(defun collect-constraints+sources-on-instance (instance slot &key ; (situation (curr-situation))
							             (situation (target-situation (curr-situation) instance slot))
								     retain-commentsp ignore-prototypes)
  (cond ((and *are-some-constraints*								; optimization flag
	      (or (member slot *built-in-slots-with-constraints*)
		  (not (member slot *built-in-slots*))))
; HLO-2308: make sure constraints on prototypes are unified in:
; 	 (cond (*are-some-prototypes* (km `(#$the ,slot #$of ,instance))))
; HLO-2325: The above line is too aggressive, and causes infinite reasoning. Let's try something simpler at [2]
	 (let* ((inherited-rulesets+classes
		 (inherited-rulesets+classes instance slot :situation situation :retain-commentsp t))
		(inherited-constraints+classes	; list of (class constraints)
		 (mapcan #'(lambda (rulesets+class)
			     (let* ((rulesets (first rulesets+class))
				    (class (second rulesets+class))
				    (constraints (remove nil (mapcan #'find-constraints-in-exprs rulesets))))
			       (mapcar #'(lambda (constraint) (list constraint class)) constraints)))
			 inherited-rulesets+classes))
		(own-constraints (remove-duplicates
				  (mapcan #'find-constraints-in-exprs ; from instance in curr-sitn + its supersituations
					  (own-rule-sets instance slot :situation situation))
				  :test #'equal))
		(own-constraints+sources
		 (mapcan #'(lambda (own-constraint)	; [1] NB get-explanations also looks in *Global
			     (let ((isv-explanations (get-explanations instance slot own-constraint situation))) ;[1]
			       (or (remove nil
				    (mapcar #'(lambda (explanation)
						(cond ((and (eq (explanation-type explanation) '#$cloned-from)
							    (not (member (second explanation) ignore-prototypes)))
						       (list own-constraint (simplify-cloned-from explanation)))))
					    (my-mapcan #'explanation-in isv-explanations)))
				   (list (list own-constraint instance)))))	; new
			 own-constraints))
#|[2]|#		(prototype-constraints+sources (prototype-constraints+sources instance slot
									      :ignore-prototypes ignore-prototypes)))
	   (mapcar #'(lambda (key+vals)  ; remove duplicates from vals
		       (list (first key+vals) (remove-duplicates (second key+vals) :test #'equal :from-end t)))
		   (gather-by-key (desource+decomment (append inherited-constraints+classes own-constraints+sources
						      prototype-constraints+sources)
					      :retain-commentsp retain-commentsp)))))))

;;; [1] Simply discard constraints that refer to prototype instances (other than the root)
;;; This means some complex constraints won't be found, but hope that's good enough. HLO-2308 just needs simple
;;; ones like (exactly 46 Chromosome)
;;; Below there are 2 ways of finding applicable prototypes:
;;; (i) climb the isa hierarchy
;;; (ii) see what prototype nodes were already cloned onto instance.
;;; It might seem like these are redundant with own-constraints+sources above, as prototype-based constraints will
;;; already have been cloned in. BUT: we need to account for the fact that (i) cloning of the prototype may not have
;;; yet been triggered and (ii) the user might have locally deleted the constraint (happens in AURA) so need to
;;; reinstate it.
(defun prototype-constraints+sources (instance slot &key ignore-prototypes)
  (let* ((prototypes (my-mapcan #'(lambda (class) (get-vals class '#$prototypes)) (all-classes instance)))   ; (i)
	 (protoinstances (get-vals instance '#$cloned-from))) ; (ii)
;    (km-format t "prototypes = ~a, protoinstances = ~a~%" prototypes protoinstances)
    (my-mapcan #'(lambda (protoinstance)
		(let* ((constraints
			(find-constraints-in-exprs (get-vals protoinstance slot :situation *global-situation*)))
		       (ok-constraints	; [1]
			(remove-if #'(lambda (constraint)
				       (some #'(lambda (instance)
						 (and (kb-objectp instance)
						      (protoinstancep instance)))
					     (flatten constraint)))
				   (subst instance protoinstance constraints)))
		       (prototype-roots (ordered-set-difference (get-vals protoinstance '#$prototype-participant-of)
							ignore-prototypes)))
		  (cond ((and ok-constraints
			      prototype-roots
			      (or (member protoinstance protoinstances)
				  (satisfies-prototype-definition instance protoinstance)))
			 (let ((classes (my-mapcan #'immediate-classes prototype-roots)))
			   (mapcan #'(lambda (class)
				       (mapcan #'(lambda (constraint)
						   `((,constraint ,class)))
					       ok-constraints))
				   classes))))))
	       (remove-duplicates (append prototypes protoinstances) :from-end t))))
#|
(defun prototype-constraints+sources (instance slot &key ignore-prototypes)
  (let* ((classes (all-classes instance)))
    (mapcan #'(lambda (class)
		(let ((prototypes (get-vals class '#$prototypes)))
		  (mapcan #'(lambda (prototype)
			      (let* ((constraints
				      (find-constraints-in-exprs (get-vals prototype slot :situation *global-situation*)))
				     (ok-constraints ; [1]
				      (remove-if #'(lambda (constraint)
						     (some #'(lambda (instance)
							       (and (kb-objectp instance)
								    (protoinstancep instance)))
							   (flatten constraint)))
						 (subst instance prototype constraints))))
				(cond ((and ok-constraints (satisfies-prototype-definition instance prototype))
				       (mapcan #'(lambda (constraint)
						   `((,constraint ,class)))
					       ok-constraints)))))
			  prototypes)))
	    classes)))
|#
;;; Same, but start at classes
;;; [1] all-superclasses0 like all-superclasses, except *excludes* Thing and includes classes.
;;;	Perfect!
(defun inherited-rule-sets-on-classes (classes slot &key (situation (curr-situation))
							 retain-commentsp
							 ignore-inherit-with-overrides-restriction)
  (let* ( (all-situations (cond ((and (neq situation *global-situation*)
				      (fluentp slot))
				 (cons situation (all-supersituations situation)))
				(t (list *global-situation*))))
		   (visible-theories (visible-theories)) )
    (cond ((and (inherit-with-overrides-slotp slot) (not ignore-inherit-with-overrides-restriction))
	   (desource+decomment
	    (inherited-rule-sets-with-overrides slot classes (append all-situations visible-theories))
	    :retain-commentsp retain-commentsp))
	  (t (let ((all-classes (my-mapcan #'all-superclasses0 classes)))    ; [1]
	       (desource+decomment
		(remove nil 				; tidy up answer...
			(mapcan #'(lambda (sitn)
				    (mapcan #'(lambda (class) (get-rule-sets-in-situation class slot sitn)) all-classes))
				(append all-situations visible-theories))		; (includes situation)
			:test #'equal :from-end t)
		:retain-commentsp retain-commentsp))))))

;;; ----------

;;; Local to the slot AND situation
;(defun local-constraints (instance slot &key (situation (curr-situation)))
(defun  local-constraints (instance slot &key (situation (target-situation (curr-situation) instance slot)))
  (cond
   (*are-some-constraints*								; optimization flag
    (find-constraints-in-exprs (bind-self
				(or (get-vals instance slot :facet 'own-properties :situation situation)     ; This disjunct should be in get-vals-
				    (get-vals instance slot :facet 'own-definition :situation situation))    ; in-situation, not here,+ should be conj!
				instance)))))

;;; ======================================================================
;;; 		ADDITIONAL UTILITIES
;;; ======================================================================

(defun has-situation-specific-info (frame situation)
  (some #'(lambda (prop-list)
	    (getobj frame (curr-situation-facet prop-list situation)))
	*all-facets*))

;;; ======================================================================
;;;		SPECIAL FACET FOR BOOK-KEEPING OF DEFINITIONS
;;; ======================================================================

;;; For now, "defined-prototypes" points to both those with AND without definitions. simple-classp means no definitions.
(defun point-parents-to-defined-concept (frame parents facet &key simple-classp)
  (let ((defined-children-facet (case facet
				  (own-definition 'defined-instances)
				  (member-definition 'defined-subclasses)
				  (prototype-definition 'defined-prototypes))))
    (cond ((null parents)
	   (report-error 'user-error "~a:
Definition for ~a must include an `instance-of' slot,
declaring the most general superclass of ~a.
Continuing, but ignoring definition...~%" frame frame frame))
	  (t (mapc #'(lambda (parent)
		 (let ( (children (get parent defined-children-facet)) )
; Below. NO! This can cause redundant superclasses to be added based on load order.
; at time of load, parent is NOT a redundant superclass. But later load a X <| superclass link and parent
; BECOMES redundant :-(. Better not to assert it in the first place.
;			   (cond ((eq facet 'member-definition)   ; Prologue: add the implied taxonomic link
;				  (km-int `(,frame #$has (#$superclasses (,parent))) :fail-mode 'error)))
		   (cond
		    ((member frame children)) ; already got this definition
		    (t (case defined-children-facet
			 ((defined-instances defined-subclasses)
				    ;(setf (get parent defined-children-facet) (cons frame children))
;				    (make-transaction `(setf ,parent ,defined-children-facet ,(cons frame children)))
				  ;;; NEW: Must try most specific classifications first! HLO bug
			  (make-comment "Noting a definition for ~a..." frame)
			  (km-setf parent defined-children-facet (most-specific-first (cons frame children))))
			 (defined-prototypes
			  (km-setf parent defined-children-facet (most-specific-prototype-scopes-first
								                      (cons frame children)))
			     (cond ((not simple-classp)
				    (make-comment "Noting a definition for prototype ~a..." frame)
				    (km-setq '*are-some-prototype-definitions* t))))
			 (t (report-error 'program-error
				    "point-parents-to-defined-concept: Unknown defined-children-facet ~a!~%" facet)))))))
		   parents)))))

;; ----------

;;; (most-specific-first '#$(Create Protein-synthesis Action)) -> (|Protein-synthesis| |Create| |Action|)
;;; If the ordering is not unique (e.g., no subsumption relationship exists) then that part of the ordering will be
;;; arbitrary.
(defun most-specific-first (classes) (reverse (most-general-first classes)))

(defun most-general-first (classes &key looping-at)
  (cond
   ((endp classes) nil)
   (t (let* ((class (first classes))
	     (superclasses (all-superclasses class)))
	(cond ((eq class looping-at)
	       (km-format t "ERROR! Looping in most-general-first! Stopping...~%") classes)
	      ((not (intersection superclasses (rest classes))) ; class is a most general concept
	       (cons class (most-general-first (rest classes))))
	      (t (most-general-first (append (rest classes) (list class)) :looping-at (or looping-at class))))))))

;; ----------

;;; (most-specific-prototype-scopes-first '#$(_Synthesis7901 _Protein-synthesis161))
;;;	-> (|_Protein-synthesis161| |_Synthesis7901|)
(defun most-specific-prototype-scopes-first (protoroots)
  (let* ((class+protoroot-pairs	; e.g., ((Synthesis _Synthesis7901) (Protein-synthesis _Protein-synthesis161))
	 (mapcan #'(lambda (protoroot)
		     (let ((scope-classes
			    (remove-subsumers
			     (mapcar #'(lambda (scope)
					 (cond ((class-descriptionp scope)
						(first (class-description-to-class+slotsvals scope :fail-mode 'error)))
					       (t scope)))
				     (get-vals protoroot '#$prototype-scope)))))
		       (mapcar #'(lambda (scope-class)
				   (list scope-class protoroot))
			       scope-classes)))
		 protoroots))
	 (ordered-classes (most-specific-first (remove-duplicates (mapcar #'first class+protoroot-pairs)))))
    (collect-prototypes-for-classes ordered-classes (gather-by-key class+protoroot-pairs))))

;;; (COLLECT-PROTOTYPES-FOR-CLASSES
;;;   '#$(Protein-synthesis Synthesis) '#$((Synthesis (_Synthesis7901)) (Protein-synthesis (_Protein-synthesis161))))
;;; -> (_Protein-synthesis161 _Synthesis7901)
(defun collect-prototypes-for-classes (ordered-classes class+protoroots-list &key collected-so-far)
  (cond
   ((endp ordered-classes) collected-so-far)
   (t (let* ((class (first ordered-classes))
	     (protoroots-at-class (second (assoc class class+protoroots-list)))
	     (uncollected (ordered-set-difference protoroots-at-class collected-so-far)) ; may be nil, of course
	     (new-collected (append collected-so-far uncollected)))
	(collect-prototypes-for-classes (rest ordered-classes) class+protoroots-list :collected-so-far new-collected)))))

;;; ----------

;;; Undo the above
(defun unpoint-parents-to-defined-concept (frame parents facet)
  (let ((defined-children-facet (case facet
				  (own-definition 'defined-instances)
				  (member-definition 'defined-subclasses)
				  (prototype-definition 'defined-prototypes))))
    (mapc #'(lambda (parent)
		(let ((children (get parent defined-children-facet)))
		  (km-setf parent defined-children-facet (remove frame children))))
	  parents)
    t))

;;; ======================================================================
;;; Adding (not replacing) new values to the originals...
;;; ======================================================================

;;; [1] Factor out 'Self' at load-time for own properties.
;;; [2] Now compute-new-vals might return (old && new), we need to do install-inverses explicitly on new.
;;; RETURNS: irrelevant.
;;; [3] Extra condition: (greater-than has (instance-of (Relation)) (inverse (less-than)))
;;; *don't* install (less-than has (instance-of (Slot))), which will happen otherwise
;;; [4] Would use (not (non-inverse-recording-slot <i>)), but some assertions may not have been done by this point so would
;;;     not yet be valid.
(defun add-slotsvals (instance add-slotsvals &key (facet 'own-properties) ; (install-inversesp t)
						  (situation (curr-situation)) combine-values-by (bind-selfp t))
;  (let ( (old-classes (cond ((assoc '#$instance-of add-slotsvals) (immediate-classes instance)))) )	; for view mechanism
  (cond ((or (not (known-frame instance)) *active-obj-stack*) (push-to-obj-stack instance))) ; new 3/28/08
  (let* ( (new-add-slotsvals (cond ((and (member facet '(own-properties own-definition)) ; [1]
					 bind-selfp)
				    (bind-self add-slotsvals instance))
				   (t add-slotsvals))) )
    (mapc #'(lambda (add-slotvals)
	      (let* ((slot (slot-in add-slotvals))
		     (add-vals0 (vals-in add-slotvals))
		     (add-vals (cond ((single-valued-slotp slot) (un-andify add-vals0))
				     ;;; Suppose add-vals0 have same values but different source info?
				     ;;; '((Pet (@ Self Cat parts)) (Pet (@ Self Cat size)))
				     ;;; For now I guess we'll just leave both in
				      ((remove-subsumers-slotp slot) (remove-subsumers add-vals0))
				      ((remove-subsumees-slotp slot) (remove-subsumees add-vals0))
				      (t add-vals0)))
		     (situation0 (target-situation situation instance slot add-vals)) ; (situation0 really should be built into
		     (old-vals (get-vals instance slot :facet facet :situation situation0))) ;  get-vals directly)

		;;; For overwriting, we have to delete the old values. Adding (A r NEW) overwrites (A r OLD), but below we have to also remove (OLD invr A).
		(cond ((and (eq combine-values-by 'overwriting)
			    (eq facet 'own-properties))
		       (let ((invslot (invert-slot slot)))
			 (uninstall-inverses instance slot (ordered-set-difference old-vals add-vals) situation0)

	 		 ;;; And more complex, Adding (A r NEW) will *also* overwrite (NEW invr OLD2) (and thus (OLD2 r NEW)) if invr is single-valued.
			 (cond ((single-valued-slotp invslot) 		       ; If (X now-has (wife (Y))), and wife-of is single-valued, and Y was already wife-of Z, then
									       ; we also need to retract Y wife-of Z.
				(mapc #'(lambda (add-val)
					  (cond ((kb-objectp add-val)		; for HLO-4553
						 (let* ((old-vals2 (get-vals add-val invslot :facet facet :situation situation0))
							(old-vals-to-delete (remove instance old-vals2)))	; preserve instance, INCLUDING its explanation HLO-4574
						   (mapc #'(lambda (old-val-to-delete)
							     (delete-val add-val invslot old-val-to-delete :situation situation0))
							 old-vals-to-delete)))))
				      add-vals))))))

		(let ((new-vals (cond ((or (null old-vals) (eq combine-values-by 'overwriting))
				       (cond ((single-valued-slotp slot) (val-to-vals (vals-to-&-expr add-vals))) ; though add-vals should always be a singleton
					     (t add-vals)))
				      (t (compute-new-vals slot old-vals add-vals :combine-values-by combine-values-by)))))
;		(km-format t "add-vals0 = ~a~%" add-vals0)
;		(km-format t "add-vals = ~a~%" add-vals)
;		(km-format t "old-vals = ~a~%" old-vals)
					;		(km-format t "new-vals = ~a~%" new-vals)
		(cond (*active-obj-stack* (mapc #'push-to-obj-stack add-vals)))
		(cond ((or new-vals (eq combine-values-by 'overwriting))		; null new-vals means no change
		       (put-vals instance slot new-vals :facet facet :install-inversesp nil :situation situation0)
;		       (km-format t "add-slotsvals = ~a~%" add-slotsvals)
;		       (cond (install-inversesp
		       (cond ((member facet '(own-definition own-properties))
;			      (install-inverses instance slot new-vals situation0)))))))		; [2]
			      (install-inverses instance slot add-vals situation0))))))))		; [2]
	  (reorder-slotsvals new-add-slotsvals))
;;; NB do this here, after the inverse slot has been declared and asserted
    (cond ((and (eq facet 'own-properties) (assoc '#$domain add-slotsvals) (not (non-inverse-recording-slot instance)))
	   (add-vals (invert-slot instance) '#$range (vals-in (assoc '#$domain add-slotsvals)) :situation *global-situation*)))
    (cond ((and (eq facet 'own-properties) (assoc '#$range add-slotsvals) (not (non-inverse-recording-slot instance)))
	   (add-vals (invert-slot instance) '#$domain (vals-in (assoc '#$range add-slotsvals)) :situation *global-situation*)))
    (cond ((and (or (some #'(lambda (slots-slot)
			      (assoc slots-slot add-slotsvals))
			  *slots-slots*)
		    (isa instance '#$Slot))
		(eq facet 'own-properties))		; don't do this for Slot classes!
	   (cond ((and (not (assoc '#$instance-of add-slotsvals))
		       (not (isa instance '#$Slot))
		       *coerce-undeclared-slots*)
		  (add-vals instance '#$instance-of '#$(Slot) :situation *global-situation*)))
	   (cond ((and *installing-inverses-enabled*
		       (not (non-inverse-recording-slot instance)) ; avoid instance=situation-specific -> assert (situation-specific-of has ...)
		       (or *coerce-undeclared-slots*
			   (isa instance '#$Slot)			; forward WAS declared, so declare inverse also
			   (assoc '#$instance-of add-slotsvals)))
		  (add-vals (invert-slot instance) '#$instance-of
; 			    (or (vals-in (assoc '#$instance-of add-slotsvals)) '#$(Slot)) 		; I don't think this is justified!
; No - not okay. slot1 has instance-of Entity-to-Value ===> invslot1 has instance-of Value-to-Entity
			    '#$(Slot)
			    :situation *global-situation*)))))))

;    (cond ((assoc '#$instance-of add-slotsvals)				       				; view mechanism
;	   (install-views instance (set-difference (immediate-classes instance) old-classes))))))

;;; ======================================================================

#|
NOTE: These are older comments from an earlier version compute-new-slotsvals, not compute-new-vals.
;;; NB: Preserves original ordering if no updates are required, so we can detect no change
> (compute-new-slotsvals '((s1 (a b)) (s2 (c d))) '((s2 (d e)) (s3 (f g))))
((s1 (a b)) (s2 (c d e)) (s3 (f g)))
>  (compute-new-slotsvals '((s1 (a b)) (s2 (c d e)) (s3 (f g))) '((s2 (d e)) (s3 (f g))))
((s1 (a b)) (s2 (c d e)) (s3 (f g)))
[1] This could be made more efficient by only doing pair-wise subsumption tests between old-vals and extra-vals,
    rather than all possible pairings. See more efficient version in add-val, earlier.
[2] Defined in subsumes.lisp. NB *only* do this check for own properties!
	Why: Originally becuase the remove-subsuming-exprs check evaluates the expressions!
[3] Now we do a two-way check: if old-expr subsumes new-expr, or new-expr subsumes old-expr, then remove the subsumer.
    This is just a generalized case of remove-subsumers [1b], preserving which was in which set.

FILTER above at [2]:
More time consuming, but more thorough. Can skip this if you really want, to avoid this
rather unusual instance-specific problem.
IF there are any instances in old-vals AND a new-val expression subsumes that
instance THEN don't add the new-val expression to the description.
	KM> (Pete has (owns ((a Dog))))
	KM> (Pete owns)
	_Dog40
	KM> (Pete has (owns ((a Dog))))
	KM> (Pete owns)
	_Dog40				; was (_Dog40 _Dog41) in 1.3.7
	KM> (Pete has (owns ((a Dog) (a Dog))))
	(_Dog40 _Dog41)			; was just _Dog40 in beta version of 1.3.8

[2] Subtle bug: final-extra-vals should be computed using the REMAINDER of UNCOVERED old-vals, not old-vals neat. But we'll not worry
about it for now.
	 (*Pete has (owns ((a Car) (a Car))))
	 (*Pete has (owns ((a Car) (a Car) (a Car))))
 result: (*Pete has (owns ((a Car) (a Car))))		[non-subsumers=(a Car), final-extra-vals=(a car)]
|#

;;; REVISED APPROACH
;;; Return new-vals, or NIL means no changes are needed
;;; [1] only meaningful for remove-subsumers-slotp etc. cases, otherwise discard result.
(defun compute-new-vals (slot old-vals0 add-vals &key combine-values-by)
  (let* ( (old-vals (cond ((single-valued-slotp slot) (un-andify old-vals0))		; ((a & b)) -> (a b)
			  (t old-vals0)))
	  (extra-vals   (ordered-set-difference add-vals old-vals :test #'equal)) )
    (cond ((remove-subsumers-slotp slot) (cond (extra-vals (remove-subsumers (append old-vals extra-vals))) (t old-vals0))) ; [1]
	  ((remove-subsumees-slotp slot) (cond (extra-vals (remove-subsumees (append old-vals extra-vals))) (t old-vals0)))
	  ((combine-values-by-appending-slotp slot) (cond (extra-vals (remove-dup-instances (append old-vals extra-vals))) (t old-vals0)))
	  ((eq combine-values-by 'appending)
	   (cond ((single-valued-slotp slot) (val-to-vals (vals-to-&-expr (remove-dup-instances (append old-vals add-vals)))))
		 (t (remove-dup-instances (append old-vals add-vals)))))
	  ((single-valued-slotp slot)
	   (cond ((not (set-difference add-vals old-vals)) nil)			; all add-vals are in old-vals already
		 ((valset-subsumes-valset add-vals old-vals) nil)
		 (t (val-to-vals (vals-to-&-expr (append old-vals add-vals))))))
	  (t (let* ( (valsets (&&-exprs-to-valsets old-vals)) 	     ; (((a b) && (c d))) -> ((a b) (c d))
		     (nvalsets (length valsets)) )
	       (cond ((member add-vals valsets :test #'equal) nil)
;		     ((km-format t "length valsets = ~a..~%" (length valsets)))
;		     ((km-format t "~{  ~a~%~}" valsets))
;		     ((km-format t "trying some...~%"))
		     ((and (<= nvalsets 10)				; efficiency bound
			   (some #'(lambda (valset)
				     (valset-subsumes-valset add-vals valset))		; i.e. add-vals is redundant
				 valsets)) nil)
		     ((and (every #'constraint-exprp add-vals)		; Efficiency and prettier (x) && (c) -> (x c) not ((x) && (c))
			   (singletonp valsets))
;		      (km-format t "~%compute-new-vals: new-valset = ~a, valsets = ~a, result = ~a~%~%" add-vals valsets
;				 (remove-duplicates (append (first valsets) add-vals) :test #'equal))
		      (remove-duplicates (append (first valsets) add-vals) :test #'equal))
		     (t ; (km-format t "~%compute-new-vals: new-valset = ~a, valsets = ~a, result = ~a~%~%" add-vals valsets
			;	   (valsets-to-&&-exprs (append valsets (list add-vals))))
;		      (km-format t "trying reduced...~%")
		      (let ( (reduced-valsets (cond ((<= nvalsets 10)
						     (remove-if #'(lambda (valset)
								    (valset-subsumes-valset valset add-vals)) ; i.e. valset is redundant
								valsets))
						    (t valsets))) )
; old			(valsets-to-&&-exprs (append reduced-valsets (list add-vals)))
			(valsets-to-&&-exprs (remove-duplicates (append reduced-valsets (&&-exprs-to-valsets add-vals))
								:test #'equal
								:from-end t))))))))))

;;; ======================================================================
;;;		NEW FRAME CREATION
;;; create-instance -- just generate a new instance frame and hook it into the isa hierarchy.
;;; ======================================================================

;;; (create-instance 'person '((legs (3))))
;;; creates a new instance of person eg. _person30, with slot-values:
;;;		(generalizations (person)) (legs (3))
;;;
;;; `parent' can be either a symbol or a string
;;; This creates a new, anonymous subframe of parent, and attaches slotsvals
;;; to the new frame. :instance denotes that the frame is an instance, and
;;; hence its name is prefixed with an instance marker (eg. "_" in "_person31")

;;; Apr 99: If fluent-instancep is t, then a fluent instance is created, denoted by using
;;; the prefix-string "_Some". Fluents aren't passed between situations (Strictly they
;;; should be copied and renamed, but it's easier to simply rebuild them in the
;;; new situation from the (some ...) expression).

(defun create-instance (parent0 slotsvals0 &key
				          (prefix-string (cond ((am-in-prototype-mode) *proto-marker-string*) (t *var-marker-string*)))
					  (bind-selfp t)
					  target)
  (let ( (parent (dereference parent0))
	 (slotsvals (dereference slotsvals0)) )
    (cond
        ((kb-objectp parent)
;	     (eq parent '#$Number))	; the one valid class which *isn't* a KB object	; WHY NOT???
	 (setq *statistics-skolems* (1+ *statistics-skolems*))
	 (create-named-instance (create-instance-name parent prefix-string) parent slotsvals
				:bind-selfp bind-selfp :target target))
;;; NEW 2.29.00: Handle descriptions as class objects
	((class-descriptionp parent)
	 (let* ((dclass+dslotsvals (class-description-to-class+slotsvals parent))
		(dclass (first dclass+dslotsvals))
		(dslotsvals (second dclass+dslotsvals)))
	   (create-named-instance (create-instance-name dclass prefix-string) dclass (append dslotsvals slotsvals)
				  :bind-selfp bind-selfp :target target)))
	(t (report-error 'user-error "Class name must be a symbol or class description! (was ~a)~%" parent)))))

#|
Here I know the name of the new frame to create
[1] to handle (a Car with (instance-of (Expensive-Thing)))
[2] Use add-slotsvals, rather than put-slotsvals, to make sure the non-fluent assertions are made in the global situation.
    In addition, unify-with-existential-expr calls this, even though the old instance exists.
[3] No - global assertions are on a slot-by-slot basis.
[4] Make sure we add instance-of Event first, so slots are later recognized as Event slots!
[5] remove-subsumers is redundant, as it's done anyway in add-slotsvals (and better add-slotsvals checks that
    instance-of is a remove-subsumers slot)
|#
(defun create-named-instance (newframe parent slotsvals0 &key (bind-selfp t) target)
  (cond
   ((not (kb-objectp newframe))
    (report-error 'user-error "Ignoring slots on non-kb-object ~a...~%Slots: ~a~%" newframe slotsvals0))
   (t (let* ((extra-classes (vals-in (assoc '#$instance-of slotsvals0))) ; [1]
	     (all-classes (remove-duplicates `(,parent ,@extra-classes)))
	     (slotsvals1 (update-assoc-list slotsvals0 (list '#$instance-of all-classes)))
; [5]					    (list '#$instance-of (remove-subsumers (cons parent extra-classes))))) ; [5]
	     (slotsvals2 (cond (bind-selfp (bind-self slotsvals1 newframe))
			       (t slotsvals1)))
	     (slotsvals (mapcar #'(lambda (slotvals)
				    (let ((slot (slot-in slotvals))
					  (vals (vals-in slotvals)))
	                              (list slot (remove-sources-from-vals newframe slot vals))))
				slotsvals2))
	     )
;	(km-format t "slotsvals1 = ~a, slotsvals2 = ~a, slotsvals = ~a~%" slotsvals1 slotsvals2 slotsvals)
	(add-slotsvals newframe slotsvals :bind-selfp bind-selfp) ; allow Self to preserved in exceptional circumstances (prototype-scope)

	(cond ((am-in-prototype-mode)
	       (add-val newframe '#$prototype-participant-of (curr-prototype) t *global-situation*)))  ; install-inverses = t; Note in GLOBAL situation
#|NEW|#	(make-assertions newframe slotsvals)	; MOVED from situations only
	(un-done newframe)		; in case it's a redefinition	MOVED to put-slotsvals Later: No!
	(let ( (slots-that-changed (remove '#$instance-of (mapcar #'slot-in slotsvals))) )
	  (cond (target (push (list target newframe) *postponed-classifications*))
		(t (classify newframe :slots-that-changed slots-that-changed)))) ; with *indirect-classification* on, see
										 ; note [1] below
	(mapc #'(lambda (slot)
		  (km-trace 'comment "New instance ~a: evaluating slot ~a opportunistically..." newframe slot)
		  (km-int `#$(the ,SLOT of ,NEWFRAME)))
	      (slots-to-opportunistically-evaluate newframe))
	newframe))))

;;; [1] above: NOTE If *indirect-classification* is NIL, and there's a plain instance (a <C>), then slots-that-changed will be NIL, and
;;; hence classification won't happen anyway.

;;; ----------

#|
KM> (a Engine with (parts ((*Cylinder2 (@ Car parts Engine parts)))))
    want the (@ Car ...) filtered out and just *Cylinder2 stored (i) so that inverses are also installed and
    (ii) so redundant unification is avoided:
	KM> (a Foo with (parts ((*C1 (@ Foo parts))))) -> (_Foo6)
	KM> (a Foo2 with (parts ((*C1 (@ Foo2 parts))))) -> (_Foo28 #|"a Foo2"|#)
	KM> (_Foo6 & _Foo28) -> (_Foo6 #|"a Foo&Foo2"|#)
	KM> (showme _Foo6)
	(_Foo6 has (parts ((((*C1 (@ Foo parts))) && ((*C1 (@ Foo2 parts)))))))	<============== undesirable, avoided by [2]

OLD: (desource+decomment-top-level (*black (comm [Comment1] _Dog1))) USED TO -> (*black):
(defun remove-sources-from-vals (instance slot vals)
  (mapcar #'(lambda (valexp0)
	      (let* ((valexp (desource+decomment-top-level valexp0))
		     (val (cond ((and (singletonp valexp)
				      (fully-evaluatedp (first valexp))
				      (not (member (first valexp) ; special keywords which should remain listified
						   (cons '#$no-inheritance *structured-list-val-keywords*))))
				 (first valexp)))))
;		(km-format t "valexp0 = ~a, valexp = ~a, val = ~a~%" valexp0 valexp val)
		(cond ((and val (not (equal val valexp0)))
		       (record-explanation-for `#$(the ,SLOT of ,INSTANCE) val valexp0)
		       val)
		      (t valexp0))))
	  vals))
|#

; NEW: (desource+decomment-top-level (*black (comm [Comment1] _Dog1))) NOW -> *black:
(defun remove-sources-from-vals (instance slot vals)
  (mapcar #'(lambda (valexp)
	      (let* ((val (desource+decomment-top-level valexp)))
		(cond ((and val
			    (fully-evaluatedp val)
			    (not (equal val valexp)))
		       (record-explanation-for `#$(the ,SLOT of ,INSTANCE) val valexp)
		       val)
		      (t valexp))))
	  vals))

;;; ======================================================================

;;; NEW - keep a local copy of the gensym counter, rather than use the Lisp internal counter,
;;; to allow us to reset it (eg. after an "undo" operation)
(defvar *km-gensym-counter* 0)

;;; [gentemp = gensym + intern in current package]
;;; [1] Consider the user saves a KB, then reloads it in a new session. As the gentemp
;;; counter starts form zero again, there's a small chance it will re-create the name
;;; of an already used frame, so we need to check for this.
(defun create-instance-name (parent &optional (prefix-string (cond ((am-in-prototype-mode) *proto-marker-string*)
								   (t *var-marker-string*))) add-to-kb-object-list)
  (cond ((and (checkkbp) (not (known-frame parent)))
	 (report-error 'user-warning "Class ~a not declared in KB.~%" parent)))
  (km-setq '*km-gensym-counter* (1+ *km-gensym-counter*))
  (let ( (instance-name (intern (concat prefix-string (symbol-name parent) (princ-to-string *km-gensym-counter*)) *km-package*)) )
    (cond ((unusable-frame-name instance-name) (create-instance-name parent prefix-string))		; [1]
	  (t (cond (add-to-kb-object-list (km-add-to-kb-object-list instance-name)))	; need to do this if we want to reclaim it by (undo-creations)
	     instance-name))))

;;; ------------------------------
;;;	NEW: If build a situation, make its assertions
;;; ------------------------------

;;; Generalized to cover any new instance. SubSelf is only used for Situations, as a holder for Self.
;;; For situations, assertions are meant to be made *in* the situation they're in.
;;; [1] (second ...) to strip off the (quote ...)
(defun make-assertions (instance &optional slotsvals)
  (cond ((or (and *classes-using-assertions-slot*
		  (intersection (all-classes instance) *classes-using-assertions-slot*))
	     (assoc '#$assertions slotsvals))			; has local assertions
	 (let ( (assertions (subst '#$Self '#$SubSelf (km-int `#$(the assertions of ,INSTANCE)))) )	; SubSelf becomes Self
	   (mapc #'(lambda (assertion)
		     (cond ((not (quotep assertion))
			    (report-error 'user-error "Unquoted assertion ~a on ~a! Ignoring it...~%" assertion instance))
			   (t (let ( (situated-assertion (cond ((isa instance '#$Situation) `#$(in-situation ,INSTANCE ,(UNQUOTE ASSERTION))) ; [1]
							       (t (unquote assertion)))) )
				(make-comment "Evaluating ~a" situated-assertion)
				(km-int situated-assertion :fail-mode 'error)))))
		 assertions)))))

;;; ======================================================================
;;;		THE DONE LIST
;;; The purpose of this list is to prevent recomputation of cached values.
;;; Here KM records which slot-values have been computed. If KM subsequently
;;; need those slot-values, it just does a lookup rather than a recomputation.
;;; note-done and reset-done are called by interpreter.lisp.
;;; Aug 98: We have to note "done in a situation", note just "done". Just
;;; because KM knows X's age in Sitn1, doesn't mean it knows it in Sitn2!
;;; ======================================================================

;(defvar *caching* t)			; if NIL then blocks noted-done
;(defun caching-on () (setq *caching* t))
;(defun caching-off () (setq *caching* nil))
;(defun caching-p () *caching*)

(defvar *noted-done* nil)

;;;    SYMBOL  PROPERTY  VALUE (list of already computed slots)
;;;    _Car1   done     (age wheels)
;;; Aug 98: Modify this so we note done in a situation, rather than globally done.
;;;    SYMBOL  PROPERTY  VALUE (list of already computed slots and situations)
;;;    _Car1   done     ((age *Global) (wheels Sitn1) (age Sitn1) (age Sitn2) (wheels *Global))
;;; [1] When *internal-logging* = t, i.e., we know backtracking *will* occur, we DO allow rollback via undo.
;;;     This avoids the more expensive alternative of calling reset-done after the undo.
;;;     Currently internal logging is only used once in subsumes.lisp.
;;; [2] May cause duplicates (one for each situation) but that's probably more efficient
(defun note-done (frame slot &optional (situation (target-situation (curr-situation) frame slot)))
; (km-format t "note-done: situation = ~a, curr-situation = ~a~%" situation (curr-situation))
  (cond (; (and (caching-p)
	 (and (kb-objectp frame)
	      *use-inheritance*	; NOTE: If we're *not* doing inference, then we can't consider the computed value as "done"
	      *use-prototypes*)
	 (let ( (done-so-far (get frame 'done)) )
	   (cond ((member (list slot situation)  done-so-far :test #'equal))
		 (*internal-logging*							; [1]
		  (push frame *noted-done*)						; [2]
		  (km-setf frame 'done (cons (list slot situation) done-so-far)))
		 (t (push frame *noted-done*)
		    (setf (get frame 'done) (cons (list slot situation) done-so-far))))))))

(defun already-done (frame slot &optional (situation (target-situation (curr-situation) frame slot)))
   (and (kb-objectp frame)
;       (member (list slot situation) (get frame 'done) :test #'equal)  - old - less efficient
#|new|# (member-if (lambda (item)		; More efficient version, thanks to Sunil Mishra!
		    (and (consp item)
			 (null (cddr item))
			 (eq (car item) slot)
			 (eq (cadr item) situation)))
		  (get frame 'done))
       ))

;;; ----------
#|
There's a subtle special case here. Fluent instances are NOT projected, so if we have (*MyCar owner _SomePerson3) in S0,
then ask for (*MyCar owner) in S1, we get NIL, and then (*MyCar owner) is flagged as DONE in S1. Fine so far.
But suppose later _SomePerson3 becomes a non-fluent instance, by doing (_SomePerson3 & *Pete) - now it SHOULD be
projected to S1, which would require removing the DONE flag on (*MyCar owner) in S1. But of course this unification
will not remove the DONE flag on all the things which are in some relationship to _SomePerson3.
We can probably make it do that though with a (very) special purpose line of code in lazy-unify.lisp!
|#
;;; [1] in principle, classification can indirectly affect ANY prior computation, including ones not
;;; directly on instance. Here we make a guess and remove caching on the instance and it's immediate
;;; slot-values.
(defun un-done (frame &key slot situation)
  (cond ((eq slot '#$instance-of)	; will affect all other slots if instance-of changes [1]
;	 (showme frame)
;	 (km-format t "remprop on ~a~%" frame)
	 (remprop frame 'done)
	 (mapc #'(lambda (instance)
		   (cond ((kb-objectp instance)
;			  (km-format t "also remprop on ~a~%" instance)
			  (remprop instance 'done))))
	       (my-mapcan #'(lambda (situation)
			      (my-mapcan #'vals-in (get-slotsvals frame :situation situation)))
			  (all-situations-and-theories))))
	((or (eq situation *global-situation*)
	     (and (null situation) (am-in-global-situation))
	     (null slot)
	     (and slot (not (fluentp slot))))
	 (cond (slot (let ( (done-so-far (get frame 'done)) )
		       (setf (get frame 'done) (remove-if #'(lambda (pair) (eq (first pair) slot)) done-so-far))))
	       (t (remprop frame 'done))))
	(t (let* ( (done-so-far (get frame 'done))
		   (next-situations (all-next-situations (or situation (curr-situation)))) )
	     (setf (get frame 'done) (remove-if #'(lambda (pair)
						    (and (member (second pair) next-situations)
							 (or (null slot) (eq (first pair) slot))))
						done-so-far))))))

#|
;;; KM 2.0.35 and earlier
(defun un-done (frame &key slot situation)
  (cond ((or ; (am-in-global-situation)
	     (eq situation *global-situation*)
	     (and (null situation) (am-in-global-situation))
	     (null slot)
	     (and slot (not (fluentp slot))))
	 (cond (slot (let ( (done-so-far (get frame 'done)) )
		       (setf (get frame 'done) (remove-if #'(lambda (pair) (eq (first pair) slot)) done-so-far))))
	       (t (remprop frame 'done))))
	(t (let* ( (done-so-far (get frame 'done))
		   (next-situations (all-next-situations (or situation (curr-situation)))) )
;	     (km-format t "next-situations = ~a~%" next-situations)
	     (setf (get frame 'done) (remove-if #'(lambda (pair)
						    (and (member (second pair) next-situations)
							 (or (null slot) (eq (first pair) slot))))
						done-so-far))))))
|#

;;; ----------

;;; (defun reset-done () (mapc #'un-done *done*) (setq *done* nil) t)
;(defun reset-done () (mapc #'un-done (get-all-concepts)) t)
; More efficient
(defun reset-done () (mapc #'un-done *noted-done*) (setq *noted-done* nil) t)

(defun show-done ()
  (mapc #'(lambda (frame)
	    (cond ((get frame 'done)
		   (km-format t "~a:~%" frame)
		   (mapc #'(lambda (slot+situations)
			     (km-format t "     ~a~20T [in ~a]~%" (first slot+situations) (second slot+situations)))
			 (gather-by-key (get frame 'done))))))
	(get-all-concepts))
  t)

;;; ======================================================================
;;;	TESTING WHETHER A CLASS/INSTANCE IS USEFUL OR NOT...
;;; Used to decide whether to do work in classification or not.
;;; In practice, this isn't used now.
;;; ======================================================================

(defun class-has-something-to-say-about (instance slot &optional (situation (target-situation (curr-situation) instance slot)))
  (frame-has-something-to-say-about instance slot 'member-properties situation))

;;; We could be even more thorough here by also checking whether its classes have something to say about slot
(defun instance-has-something-to-say-about (instance slot &optional (situation (target-situation (curr-situation) instance slot)))
  (frame-has-something-to-say-about instance slot 'own-properties situation))

(defun frame-has-something-to-say-about (frame slot facet &optional (situation (target-situation (curr-situation) frame slot)))
  (let ( (all-situations (cond ((and (neq situation *global-situation*)
				     (fluentp slot))
				(cons situation (all-supersituations situation)))
			       (t (list *global-situation*))))
	 (visible-theories (visible-theories)) )
    (some #'(lambda (situation)
	      (some #'(lambda (subslot)
			(get-vals frame subslot :facet facet :situation situation))
		    (cons slot (all-subslots slot))))
	  (append all-situations visible-theories))))

;;; ======================================================================
;;;			(RE)CLASSIFICATION OF INSTANCES
;;; ======================================================================

#|
If it's a new/redefined frame, should classify it.
If it has extra values through unification, should reclassify it.
If it has an extra value through installation of inverses, do reclassify it
	(see kb/test1.kb)
If it is just having existing expressions computed into values, don't reclassify it.
|#

;;; Wrapper to limit tracing....
;;; [1] slot-of-interest as option: classify is never called now giving this argument. But if it was, only consider
;;;     possible-new-parent classes which have something explicit to offer for slot's value. 10/23/00 drop
;;;     this for now.
;;; [2] slot-that-changed: Only do reclassification work if slot-that-changed might directly affect the class.
;;;	Note: If *indirect-classification* = t, then slot-that-changed is NOT used
;;; NEW: 9/14/00 - ONLY do classification in the global situation
;;; 4/13/01 - *am-classifying* - don't classify while classifying
;;; [3] 'unspecified, to distinguish from :slots-that-changed NIL
;;; [1] Don't classify prototypes unless in prototype mode. Simply blocking classification is
;;; preferable to throwing an error and making the user wrap the assertion in a (disable-classification)
;;; ...(enable-classification) wrapper.
(defun classify (instance &key (slots-that-changed 'unspecified) slot-of-interest) ; [3]
  (cond ((and (classification-enabled)
	      (or (not (protoinstancep instance))	; [1]
		  (am-in-prototype-mode))
	      (or (not (listp slots-that-changed))
		  (set-difference slots-that-changed *neq-slots*)) ; there must be at least one non-NEQ slot that changed, to trigger reclassification
	      (or *classify-slotless-instances*
		  slots-that-changed)		; may be NIL, as opposed to unspecified
	      (or *are-some-definitions*
		  (and *are-some-prototype-definitions* *prototype-classification-enabled*))
	      (or (am-in-global-situation)
		  *classify-in-local-situations*)
	      (and (or *recursive-classification* (not *am-classifying*))
		   (neq *am-classifying* instance)))
	 (let ((*am-classifying* instance))
	   (cond ((and (tracep) (not (traceclassifyp)))
		  (let ((*trace* nil))
		    (classify0 instance :slots-that-changed slots-that-changed :slot-of-interest slot-of-interest)))
		 (t (classify0 instance :slots-that-changed slots-that-changed :slot-of-interest slot-of-interest)))))))

;;; Question: Does the order of which classifications are attempted matter?
;;; The current implementation tries the more specific classes up to the more general ones.
;;; A comment in point-parents-to-defined-concept reads:
;;; 		"NEW: Must try most specific classifications first! HLO bug"
;;; So obviously the specific-to-general ordering is important!!
;;; (The ordering is effected by most-specific-first in point-parents-to-defined-concept).
(defun classify0 (instance &key slots-that-changed slot-of-interest)
  (cond
   ((not (kb-objectp instance))
    (report-error 'user-error "Attempt to classify a non-kb-object ~a!~%" instance))
   ((is-an-instance instance)				; NEW: Don't try classifying Classes!
    (let ( (all-parents  (all-classes instance)) )  ; (immediate-classes ...) would
						      ; be faster but incomplete
	(cond ((some #'(lambda (parent)
			 (or (classify-as-member instance parent :slots-that-changed slots-that-changed
						 :slot-of-interest slot-of-interest)
			     (classify-as-coreferential instance parent :slots-that-changed slots-that-changed
							:slot-of-interest slot-of-interest)
			     (classify-as-prototype instance parent :slots-that-changed slots-that-changed
							:slot-of-interest slot-of-interest)))
			 all-parents)	; if success, then must re-iterate, as the success
	       (classify0 instance
			  :slots-that-changed 'unspecified	 	; may make previously failed classifications now succeed
			  :slot-of-interest slot-of-interest)))))))

;(defun do-postponed-classifications ()
;  (mapc #'(lambda (postponed-classification)
;	    (let ((instance (first postponed-classification))
;		  (slots-that-changed (second postponed-classification))
;		  (slot-of-interest (third postponed-classification)))
;	      (classify instance :slots-that-changed slots-that-changed :slot-of-interest slot-of-interest)))
;	*postponed-classifications*)
;  (setq *postponed-classifications* nil))

(defun do-postponed-classifications (instance slot)
  (cond (*postponed-classifications*
	 (let ((target `(#$the ,slot #$of ,instance)))
;	       (old-length (length *postponed-classifications*)))
	   (setq *postponed-classifications*
	     (remove nil (mapcar #'(lambda (postponed-classification)
				     (let ((target2 (first postponed-classification))
					   (instance2 (second postponed-classification)))
				       (cond ((equal target target2) (classify instance2) nil)
					     (t postponed-classification))))
				 *postponed-classifications*)))))))
;    (let ((new-length (length *postponed-classifications*)))
;      (km-format t "DEBUG: Did ~a postponed classifications (~a remain)~%" (- old-length new-length) new-length))))

;;; ----------------------------------------------------------------------
;;; (I) CLASSIFY INSTANCE AS BEING A MEMBER OF A CLASS
;;; ----------------------------------------------------------------------

;;; [1] Efficiency - if instance is explicitly (<> Parent), or (<> SubParent) then don't go and test further.
;;; [2] Quick lookahead check
;;; [3] More rigorous lookahead - Hmm... in my earlier tests I thought this helped, but later it seems not
(defun classify-as-member (instance parent &key slots-that-changed slot-of-interest)
 (cond (*are-some-definitions*
  (some #'(lambda (possible-new-parent)
	    (cond ((and	(might-be-member instance possible-new-parent)
			(not (disjoint-class-sets0 (immediate-classes instance) (list possible-new-parent))) ; [2]
			(not (isa instance possible-new-parent)) ; already done!
			(test-val-constraints possible-new-parent ; [1]
					      (extract-constraints (get-vals instance '#$instance-of :situation *global-situation*))
					      'remove-subsumers-slot
					      :mode 'consistent)
			(not (disjoint-class-sets (immediate-classes instance) (list possible-new-parent))) ; [3]
			(or (null slot-of-interest)
			    (class-has-something-to-say-about possible-new-parent slot-of-interest)))
		   (try-classifying instance possible-new-parent :slots-that-changed slots-that-changed))))
	(get parent 'defined-subclasses)))))

;;; [1] e.g., slotsvals = ((instance-of (Chemical-Entity)) (has-chemical-name ("Tellurium")))
(defun might-be-member (instance parent)
;  (km-format t "(might-be-member ~a ~a)? " instance parent)
  (let* ((defn-slotsvals (append (get-slotsvals parent :facet 'member-definition :situation *global-situation*)
				 (cond ((am-in-local-situation) (get-slotsvals parent :facet 'member-definition))))))
    (might-have-slotsvals instance defn-slotsvals)))

(defun might-have-slotsvals (instance defn-slotsvals)
  (let* ((missing-required-info		; if instance doesn't have some required info AND is already-done (i.e., no more
	  (some #'(lambda (defn-slotvals)	; computational possible) THEN don't even try classifying
		    (let* ((dslot (slot-in defn-slotvals))
			   (dvals (vals-in defn-slotvals))
			   (ivals (get-vals instance dslot)))
;		      (km-format t "dslot = ~a, dvals = ~a, ivals = ~a, already-done = ~a~%" dslot dvals ivals
;				 (already-done instance dslot))
		      (and (already-done instance dslot)
			   (not (remove-subsumers-slotp dslot))	; can have different, named vals and still subsume
			   (not (remove-subsumees-slotp dslot))
			   (or (and (some #'non-constraint-exprp dvals) (null ivals)) ; defn has a val, instance no val
			       (and (every #'named-instancep ivals)		      ; ival all named
				    (some #'(lambda (dval)			      ; there's a dval that's named and
					      (and (atom dval)			      ; not in ivals
						   (named-instancep dval)             ; (named check to prevent unif)
						   (not (member dval ivals :test #'equal))))
					  dvals))))))
		defn-slotsvals)))
    (and (not missing-required-info)
	 ;;; [1] we optimize for this specific defn pattern ((instance-of (Chemical)) (has-basic-structural-unit ((a Zn))))
	 (let* ((rest+dslot+class (minimatch defn-slotsvals '#$((instance-of &rest) (?slot ((a ?class &rest))) &rest)));[1]
		(dslot (second rest+dslot+class))
		(class (third rest+dslot+class))
		(ivals (cond (dslot (get-vals instance dslot)))))
	   (cond ((and rest+dslot+class			; IF just need a class
		       (already-done instance dslot)
		       (singletonp ivals) ; and already got an instance
		       (kb-objectp (first ivals))) ; not a constraint e.g., dslot = instance-of, ivals = ((<> *ShinerBock))
		  (isa (first ivals) class)) ; check class membership
		 (t))))))

;;; ----------

;;; The hierarchy looks:       parent (eg. put)
;;;                           /                \
;;;                  instance (eg. _put12)      possible-new-parent (eg. tell)
;;;
;;; [1] Remove unifiable-with-expr -- this shortcut wasn't working as it doesn't check constraints on the classes (here Thing)
;;; [2] must check class consistency also!
(defun try-classifying (instance possible-new-parent &key slots-that-changed)
  (multiple-value-bind
   (satisfiedp explanation)
   (satisfies-definition instance possible-new-parent :slots-that-changed slots-that-changed)
   (cond (satisfiedp
; 	  (cond ((unifiable-with-expr instance `#$(a Thing with . ,(FIND-SLOTSVALS POSSIBLE-NEW-PARENT 'MEMBER-PROPERTIES)))	; New test!
;	  (cond ((km-int `#$(,INSTANCE &? (a Thing with . ,(FIND-SLOTSVALS POSSIBLE-NEW-PARENT 'MEMBER-PROPERTIES))))  ; new test [1]
	  (cond ((km-int `#$(,INSTANCE &? (a ,POSSIBLE-NEW-PARENT with
					  ,@(GET-SLOTSVALS POSSIBLE-NEW-PARENT :FACET 'MEMBER-PROPERTIES :SITUATION *GLOBAL-SITUATION*))))  ; new test [1,2]
		 (cond ((check-classification-with-user instance possible-new-parent)
			(setq *statistics-classifications-succeeded* (1+ *statistics-classifications-succeeded*))
			(add-immediate-class instance possible-new-parent explanation)
			t)
		       (t (add-val instance '#$instance-of `(<> ,possible-new-parent) nil		; add constraint, to prevent further retries
				   (target-situation (curr-situation) instance '#$instance-of))
			  nil)))
		(t (make-comment "~a satisfies definition of ~a,"  instance possible-new-parent)
		   (make-comment "...but classes/properties clash!! So reclassification not made.")))))))

;;; This is a dummy procedure, which can then be redefined in applications where the interaction is required.
(defun check-classification-with-user (instance possible-new-parent)
  (declare (ignore instance possible-new-parent))
  t)

;;; explanation for X isa Car is of form (every Car has-definition (instance-of (Vehicle)) (parts ((a Wheel) (a Wheel))))
;;; This is very different from the encoded explanations of a path + expression, i.e., here we record the expression directly.
(defun add-immediate-class (instance0 new-immediate-parent explanation)
  (let* ((instance (dereference instance0))
	 (old-classes (immediate-classes instance))
	 (new-classes (remove-subsumers (cons new-immediate-parent old-classes))))
   (make-comment "~a satisfies definition of ~a," instance new-immediate-parent)
   (make-comment "so changing ~a's classes from ~a to ~a" instance old-classes new-classes)
;  (put-vals instance '#$instance-of new-classes)
;  NOTE: Must assert the value before recording the explanation, or else the explanation won't stick
   (add-val instance '#$instance-of new-immediate-parent t ; install-inverses = t
	    (target-situation (curr-situation) instance '#$instance-of (list new-immediate-parent)))	; target situation
   ;;; OLD
;  (record-explanation-for `#$(the instance-of of ,INSTANCE) new-immediate-parent explanation :situation *global-situation*)
   ;;; NEW: Copy, rather than delete, the old explanations over
   (let* ((old-isv-explanations (get-all-explanations instance '#$instance-of))
	  (old-instance-of-isv-explanations (remove-if-not #'(lambda (isv-expn) (eq (second isv-expn) '#$instance-of)) old-isv-explanations))
	  (old-instance-of-explanations (mapcar #'explanation-in old-instance-of-isv-explanations))
	  (new-instance-of-explanations (cons explanation old-instance-of-explanations))
	  (new-instance-of-isv-explanations
	   (mapcar #'(lambda (explanation)
		       `(,instance #$instance-of ,new-immediate-parent ,explanation))
		   new-instance-of-explanations)))
;     (km-format t "putting explanations:~%~{	~a~%~}" new-instance-of-isv-explanations)
     (put-explanations instance '#$instance-of new-instance-of-isv-explanations))

;  (cond ((isa instance '#$Situation) (make-situation-specific-assertions instance)))
   (make-assertions instance)	; test later
   (un-done instance)))		; all vals to be recomputed now - now in add-slotsvals; later: No!

;;; (satisfies-definition '_get32 'db-lookup)
;;; Can we make _get32, a specialization of get, into a specialization of
;;; db-lookup?
;;; Returns *two* values (i) a satisfied flag (ii) the definition that was satisfied (for explanatory purposes)
;;; [1] Note we don't need to say (a Parent-Class with...), as instance is already known to be a member of Parent-Class
;;;     (that's how we found the definition to test in the first place)
;;;     Also note the Class in the definition is stored as (instance-of (Class)) rather than (the-class Class with ...)
(defun satisfies-definition (instance class &key slots-that-changed)
  (let ( (definitional-slotsvals (bind-self (get-slotsvals class :facet 'member-definition :situation *global-situation*) instance)) )
    (cond
     ((or *indirect-classification*
 	  (eq slots-that-changed 'unspecified)		; distinct from NIL, means no slots changed
	  (intersection slots-that-changed (mapcar #'slot-in definitional-slotsvals)))	; i.e. slots-that-changed must have something
      (km-trace 'comment "CLASSIFY: ~a has just been created/modified. Is ~a now a ~a?" 		   ; affecting the definition
	instance instance class)
      (setq *statistics-classifications-attempted* (1+ *statistics-classifications-attempted*))
      (let* ( (description `'#$(a Thing with ,@DEFINITIONAL-SLOTSVALS))    ; [1]
	      (satisfiedp (km-int `#$(,INSTANCE is ,DESCRIPTION))) )
	(cond (*developer-mode* (km-format t "#")))
	(cond (satisfiedp
	       (km-trace 'comment "CLASSIFY: ~a *is* a ~a!" instance class))
	      (t (km-trace 'comment "CLASSIFY: ~a is not a ~a." instance class)))
	(values satisfiedp
		`#$(every ,CLASS has-definition ,@DEFINITIONAL-SLOTSVALS)))))))

;;; ----------------------------------------------------------------------
;;; (II) CLASSIFY INSTANCE AS BEING COREFERENTIAL WITH ANOTHER INSTANCE
;;; ----------------------------------------------------------------------

#|
This is for equating coreferential instances, eg.

	bright-color IS red

	(Red has
	   (definition (((Self isa Color) and ((Self is) = Bright)))))

	(a Color with (is (Bright)))
	-> _Color32 unifies with Red
	-> Red

BUT: Suppose an instance satisfies *two* different instances' definitions?
In fact, KM will prevent you doing this. The first classification will cause
_Color34 to be unified to Red. The second will classify Red as Another-red,
but the unification of these two isn't permitted.
|#

(defun classify-as-coreferential (instance0 parent &key slots-that-changed slot-of-interest)
 (cond (*are-some-definitions*
  (let ( (instance (dereference instance0)) )
    (some #'(lambda (possible-coreferential-instance)
	      (cond ((and (not (eql instance possible-coreferential-instance))   ; already done!
			  (or (null slot-of-interest)
			      (instance-has-something-to-say-about possible-coreferential-instance slot-of-interest)))
		     (try-equating instance possible-coreferential-instance :slots-that-changed slots-that-changed))))
	  (get parent 'defined-instances))))))

(defun try-equating (instance possible-coreferential-instance &key slots-that-changed)
  (cond ((satisfies-definition2 instance possible-coreferential-instance :slots-that-changed slots-that-changed)
	 (unify-with-instance instance possible-coreferential-instance))))

; [1]. Just doing (X & Y) doesn't fail,
(defun unify-with-instance (instance possible-coreferential-instance)
  (make-comment "~a satisfies definition of ~a," instance possible-coreferential-instance)
  (make-comment "so unifying ~a with ~a" instance possible-coreferential-instance)
  (setq *statistics-classifications-succeeded* (1+ *statistics-classifications-succeeded*))
  (cond ((km-int `(,instance & ,possible-coreferential-instance))		; so failure gets reported below instead
	 (un-done instance))		; all vals to be recomputed now - now in put-slotsvals via lazy-unify. Later: no!
	(t (report-error 'user-error "~a satisfies definition of ~a but won't unify with it!~%"
			 instance possible-coreferential-instance))))

(defun satisfies-definition2 (instance poss-coref-instance &key slots-that-changed)
  (let ( (definitional-slotsvals (bind-self (get-slotsvals poss-coref-instance :facet 'own-definition :situation *global-situation*) instance)) )
    (cond
     ((or *indirect-classification*
	  (eq slots-that-changed 'unspecified)
	  (intersection slots-that-changed (mapcar #'slot-in definitional-slotsvals)))
      (km-trace 'comment "CLASSIFY: ~a has just been created/modified. Is ~a now = ~a?"
		instance instance poss-coref-instance)
      (setq *statistics-classifications-attempted* (1+ *statistics-classifications-attempted*))
      (let* ( (description `'#$(a Thing with ,@DEFINITIONAL-SLOTSVALS))
	      (satisfiedp (km-int `#$(,INSTANCE is ,DESCRIPTION))) )
	(cond (*developer-mode* (km-format t "#")))
	(cond (satisfiedp (km-trace 'comment "CLASSIFY: ~a = ~a!" instance poss-coref-instance))
	      (t (km-trace 'comment "CLASSIFY: ~a \= ~a." instance poss-coref-instance)))
	satisfiedp)))))

;;; ----------------------------------------

#|
Note: the 'defined-prototypes for the below will be logged on Cell:
(get '#$Cell 'defined-prototypes) -> (|_Euk-cell14|)
(_Euk-cell14 has
  (instance-of (Euk-cell))
  (prototype-of (Euk-cell))
  (prototype-scope (Euk-cell
                    (the-class Cell with (has-part ((a Nucleus))))))

; Though we also got in the original conception of prototypes:
(_Red-Wine1 has
   (instance-of (Wine))
   (prototype-of (Wine))
   (prototype-scope ((the-class Wine with (color (*Red))))))

So what class do we assign then when the classification succeeds?
|#
(defun classify-as-prototype (instance parent &key slots-that-changed slot-of-interest)
  (declare (ignore slots-that-changed slot-of-interest))
  (cond
   ((and *are-some-prototypes* *prototype-classification-enabled*)
    (some #'(lambda (protoroot)
	      (classify-as-prototype0 instance protoroot))
	  (get parent 'defined-prototypes)))))

(defun classify-as-prototype0 (instance protoroot)
  (let ((class-definitions (subst '#$Self protoroot
				  (remove-if-not #'the-class-exprp (get-vals protoroot '#$prototype-scope))))
	(protoclasses (remove-subsumers 	; Ug - remove-subsumers because AURA allows redundant classes e.g., (instance-of (Cell Tangible-Entity))
		       (get-vals protoroot '#$instance-of)))) ; I guess...rather than '#$prototype-of, which may be overly general as used for indexing
;   (km-format t "class-definitions for ~a = ~a~%" protoroot class-definitions)
    (cond
     ((and class-definitions
	   (notany #'(lambda (protoclass) (instance-of instance protoclass)) protoclasses)) ; already done!
      (some #'(lambda (class-definition)
		(let* ((class+slotsvals (class-description-to-class+slotsvals class-definition))
		       (class (first class+slotsvals))
		       (slotsvals (decomment (second class+slotsvals))))
;		  (km-format t "class+slotsvals = ~a~%" class+slotsvals)
;		  (km-format t "slotsvals = ~a~%" slotsvals)


; [2] these lookaheads copied from classify-as-member, don't know if we really need them
; [3] Don't bother when the prototype class isn't reified, e.g., in the Wine example above.
		  (cond ((and (not (member class protoclasses)) ; [3]
			      (might-have-slotsvals instance slotsvals) ; [2]
			      (not (disjoint-class-sets (immediate-classes instance) protoclasses))) ; [2]
			 (try-classifying-as-prototype instance protoclasses class-definition)))))
	    class-definitions)))))

;;; The has-definition version of this function included an &? test first to make sure of unifiability, but we
;;; don't do that for prototypes. I *think* the &? test is merely to check for KB consistency, which we'll assume here.
(defun try-classifying-as-prototype (instance protoclasses class-definition)
  (push-to-goal-stack `(,instance #$isa ,(first protoclasses)))  ; to avoid cloning the same prototype for this classfn
  (multiple-value-bind
      (satisfiedp explanation)
      (satisfies-class-definition instance class-definition protoclasses)
    (prog1
	(cond (satisfiedp
	       (setq *statistics-classifications-succeeded* (1+ *statistics-classifications-succeeded*))
	       (mapc #'(lambda (protoclass)
			 (add-immediate-class instance protoclass explanation))
		     protoclasses)
	       t))
      (pop-from-goal-stack))))

;;; This procedure solely does (km-int `#$(,INSTANCE isa ,CLASS-DEFINITION)) wrapped in a lot of tracing info
;;; Note: Both prototype and traditional classification will be recorded in the explanation database in the form (every C has-definition ...)
;;; Also note: prototype classification is also done separately by unify-in-prototype in prototype.lisp. If
;;; prototype classification is also done there, it is also recorded in the explanation database in the same form.
;;; Thus you can't tell from the explanation database whether the definition was stored on a prototype or traditional class frame.
(defun satisfies-class-definition (instance class-definition conclusion-classes)
  (km-trace 'comment "CLASSIFY: ~a has just been created/modified. Is ~a now a ~a?"
	    instance instance (delistify conclusion-classes))
  (setq *statistics-classifications-attempted* (1+ *statistics-classifications-attempted*))
  (let* ((satisfiedp (km-int `#$(,INSTANCE isa ,CLASS-DEFINITION))))
    (cond (*developer-mode* (km-format t "#")))
    (cond (satisfiedp
	   (km-trace 'comment "CLASSIFY: ~a *is* a ~a!" instance (delistify conclusion-classes))
	   (let* ((class+slotsvals (class-description-to-class+slotsvals class-definition))
		  (class (first class+slotsvals))
		  (slotsvals (second class+slotsvals)))
	     (values satisfiedp
		     (subst instance '#$Self
			    `#$(every ,(FIRST CONCLUSION-CLASSES) has-definition (instance-of (,CLASS)) ,@SLOTSVALS)))))
	  (t (km-trace 'comment "CLASSIFY: ~a is not a ~a." instance (delistify conclusion-classes))
	     nil))))

;;; ======================================================================
;;;			TAXONOMIC OPERATIONS
;;; ======================================================================


;;; check frame isa genframe. Returns frame.
;;; (isa x x)	returns nil
(defun isa (instance class &optional (situation (curr-situation)))
  (instance-of instance class situation))	; synonym

;;; [1] Still some cases where test-suite passes non-class arguments, need a bit more work to filter them out
(defun instance-of (instance target-class &optional (situation (curr-situation)))
  (let ((its-classes (immediate-classes instance :situation situation)))
    (cond ;((not (kb-objectp target-class))	; [1]
     ; (report-error 'user-error "Doing (instance-of ~a ~a): Encountered a non-KB object ~a (illegal!)"
     ;		 instance target-class target-class))
     ((member target-class its-classes) instance)
     ((and (not (null its-classes))
           (some #'(lambda (its-class) (is-subclass-of its-class target-class))
                 its-classes))
      instance))))

;;; [1] There are still cases where we want to not break, e.g., constraints or comment tags passed
;;;     I need to do more work to properly filter out these cases elsewhere in the code
(defun is-subclass-of (class target-class &key path-so-far)
    (cond ;((not (kb-objectp target-class)) - [1]
	  ; (report-error 'user-error "Doing (is-subclass-of ~a ~a): Encountered a non-KB object ~a (illegal!)"
	  ;		 class target-class target-class))
          ((eq class target-class) class)
	  ((eq class '#$Thing) nil)
	  ((member class path-so-far)
	   (report-error 'user-error "You have a cycle in the taxonomy (not allowed)!~%~a~%"
			 (commaed-list (reverse (cons class path-so-far)) '->)))
	  ((and (kb-objectp class)
		(kb-objectp target-class))
	   (let ( (superclasses (immediate-superclasses class)) )
	     (cond ((member target-class superclasses) class)
		   ((and (not (null superclasses))
			 (some #'(lambda (superclass) (is-subclass-of superclass target-class :path-so-far (cons class path-so-far)))
			       superclasses))
		    class))))))

;;; Identical code structure to is-subclass-of above
(defun is-subslot-of (slot target-slot &key path-so-far)
    (cond ((eq slot target-slot) slot)
	  ((member slot path-so-far)
	   (report-error 'user-error "You have a cycle in the slot hierarchy (not allowed)!~%~a~%"
			 (commaed-list (reverse (cons slot path-so-far)) '->)))
	  ((and (kb-objectp slot)
		(kb-objectp target-slot))
	   (let ( (superslots (immediate-superslots slot)) )
	     (cond ((member target-slot superslots) slot)
		   ((and (not (null superslots))
			 (some #'(lambda (superslot) (is-subslot-of superslot target-slot :path-so-far (cons slot path-so-far)))
			       superslots))
		    slot))))))

;;; Shadow of KM. Find immediate generalizations of a frame.
;;; NOTE: This does *NOT* remove redundant superclasses (there shouldn't be any there)
;;; The top generalization is #$Thing
;;; [1] instance-of is treated as a *Non-Fluent for Slots and Situations, and so we must also check the global
;;;     situation here. For cases where it's a fluent, it's value will be cached in the local situation.
;;; [2] :enforce-constraints - if we always enforce constraints, the system will easily fall into infinite
;;;	recursion. So we restrict how much this is allowed. Here we just allow it when the user explicitly
;;;     requests it.
;;; [3] enforce-constraints may change the parent classes, so we then must recheck what the parent
;;;     classes are (this recursive call WITHOUT constraint checking this time, to prevent looping)
(defun immediate-classes (instance &key (situation (curr-situation)) enforce-constraints) ; [2]
  (declare (optimize (speed 3) (safety 0)) (ignore enforce-constraints))
  (macrolet ((fassoc (item alist)	; NOTE: This goes wrong when (T Boolean) is in the list, as T in a case statement matches *any* item, not just item = T.
	       `(case ,item		; So we need to disallow T as an entry. Note that this optimization seems to be highly important, it saves 20%-30% reasoning time in the test suite
	     	  ,@(mapcar (lambda (pair) (list (car pair) (list 'quote (list (cadr pair)))))
             			    (symbol-value alist))))
	     (fmember (item list)
	       `(case ,item
		  (,(symbol-value list) t))))
    (cond ((integerp instance) '(#$Integer))
	  ((numberp instance) '(#$Number))
	  ((fassoc instance *built-in-instance-of-links*)) ; e.g. t -> Boolean
					;	((eq instance '#$*Global) '(#$Situation))
	  ((fmember instance *built-in-set-aggregation-slots*) '#$(Set-Aggregation-Slot))
	  ((fmember instance *built-in-seq-aggregation-slots*) '#$(Seq-Aggregation-Slot))
	  ((fmember instance *built-in-bag-aggregation-slots*) '#$(Bag-Aggregation-Slot))
	  ((fmember instance *built-in-slots*) '#$(Slot))
	  ((class-descriptionp instance) '#$(Class))
	  ((quoted-expressionp instance) '#$(Quoted-Expression))
	  ((stringp instance) '(#$String))

					; 8/19/05 - the following added for these special classes, to allow (a Sequence) & (:seq 1 2) to unify
	  ((km-seqp instance) '#$(Sequence))
	  ((km-bagp instance) '#$(Bag))
	  ((km-pairp instance) '#$(Pair))
	  ((km-triplep instance) '#$(Triple))
	  ((km-functionp instance) '#$(Function))

	  ((km-structured-list-valp instance) ; Hmm.... (the classes of (:seq A B)) should really return #$Sequence
	   (immediate-classes (arg1of instance))) ; But (the classes of (:args _Pipe1 _Tank2)) should be #$Pipe (?)
					; Called by constraints.lisp to test expressions like (exactly 1 Thing)
	  ((not (kb-objectp instance))
	   (report-error 'user-error "ERROR! Attempt to find the instance-of of an non-KB object ~a -- ~a should be a non-keyword symbol!"
			 instance instance)
	   '#$(Thing))

	  ((or (not (inertial-fluentp '#$instance-of)) ; allow redefinition of this thing
	       (eq situation *global-situation*))


;;; 9/28/00 Rewrite this to explicitly test instance-of constraints [this test is bypassed by interpreter.lisp]
	   (let* ( (vals+constraints (append (cond (*are-some-definitions*
						    (get-vals instance '#$instance-of :facet 'own-definition :situation *global-situation*)))
					     (get-vals instance '#$instance-of :facet 'own-properties :situation *global-situation*)))
		  (constraints (extract-constraints vals+constraints))
		   (vals0 (remove-constraints vals+constraints))
		   (vals (cond ((every #'kb-objectp vals0) vals0)
			       (t (km-trace 'comment "Computing the parent classes of ~a..." instance)
				  (let ( (vals1 (remove-subsumers (km-int (vals-to-val vals0)))) )
				    (put-vals instance '#$instance-of (append vals1 constraints))
				    (note-done instance '#$instance-of)
				    vals1)))) )
	     (cond
					;	         (nil 	; NEW!!!!!! DISABLE THIS FUNCTION, IT CAUSES TOO MANY PROBLEMS!!
					;		  (and enforce-constraints constraints)
					;		  (enforce-constraints vals constraints instance '#$instance-of)  ; [3]
					;		  (immediate-classes instance :situation situation))
	       (vals)
	       ('#$(Thing)))
	     ))

					;APR30	((already-done instance '#$instance-of situation)
	  ((already-done instance '#$instance-of)
	   (or (remove-constraints (get-vals instance '#$instance-of :situation situation))
	       (remove-constraints (get-vals instance '#$instance-of :situation *global-situation*)) ; [1]
	       '#$(Thing)))

	  (t (prog1
		 (immediate-classes0 instance :situation situation)
					;APR30	     (note-done instance '#$instance-of situation)))))
	       (note-done instance '#$instance-of))))))

;;; REVISED: We must do more work here when there are situations.
(defun immediate-classes0 (instance &key (situation (curr-situation)))
  (let* ( (local-classes-and-constraints (get-vals instance '#$instance-of :situation situation))
	  (local-constraints (extract-constraints local-classes-and-constraints))
	  (supersituation-classes (my-mapcan #'(lambda (supersituation)
						 (immediate-classes instance :situation supersituation))
					     (immediate-supersituations situation)))
	  (projected-classes (projected-classes instance situation local-constraints))
	  (definitional-classes (cond (*are-some-definitions* (get-vals instance '#$instance-of :facet 'own-definition :situation situation)))) )
    (cond ((some #'(lambda (class)				;	 [1] Local Classes are *NOT* a complete list
		     (and (neq class '#$Thing)
			  (not (member class local-classes-and-constraints))))
		 (append supersituation-classes projected-classes definitional-classes))
	   (let* ( (local-classes (remove-constraints local-classes-and-constraints))
		   (all-classes (remove-subsumers (append local-classes supersituation-classes projected-classes definitional-classes))) )
	     (put-vals instance '#$instance-of (append local-constraints all-classes) :situation situation)		; note-done is done above
	     all-classes))
	  ((remove-constraints local-classes-and-constraints))			; [2] Local Classes *ARE* a complete list
	  ((and (checkkbp) (not (known-frame instance)))
	   (report-error 'user-warning "Object ~a not declared in KB.~%" instance)
	   '(#$Thing))
; Hmm...can we get rid of automatically computed meta-classes?
;	  ((find-vals instance '#$superclasses)
;	   (put-vals instance '#$instance-of '(#$Class) :situation situation)		; note-done is done above
;	   '(#$Class))
	  (t (cond ((checkkbp)
		    (report-error 'user-warning "Parent (superclasses/instance-of) for ~a not declared.~%" instance)))
	     '(#$Thing)))))

(defun projected-classes (instance situation local-classes-and-constraints)
  (let ( (prev-situation (prev-situation situation instance)) )
    (cond (prev-situation (filter-using-constraints (immediate-classes instance :situation prev-situation) local-classes-and-constraints '#$prev-situation)))))

;;; ======================================================================

;;; [1] Note, this was earlier, but I need to allow users to override the built-in taxonomy, unfortunately.
;;; This is particularly so in AURA, where we have already relied on Entity as a superclass of Aggregate, and Entity contains
;;; some important NLG information.
;;; Note also that immediate-subclasses similarly allows user definitions to override the *built-in-superclass-links*
(defun immediate-superclasses (class)
  (cond ((eq class '#$Thing) nil)
	((class-descriptionp class)
	 (list (first (class-descriptionp class))))			; (the-class Remove with ...) -> (Remove)
	((let ( (superclasses (get-vals class '#$superclasses)) )
	   (cond ((member class superclasses)
		  (report-error 'user-error "Cycle in the KB! ~a is its own superclass!" class)
		  (remove class superclasses))
		 (t superclasses))))
;		  (note-statistics-for class '#$superclasses superclasses)
;		  superclasses))))
	((rest (assoc class *built-in-superclass-links*)))		; e.g. (immediate-superclasses '#$Integer) -> (Number)  [1]
	((and (checkkbp) (not (known-frame class)))
	 (report-error 'user-warning "Class ~a not declared in KB.~%" class)
	 '(#$Thing))
;	((is-an-instance class) nil)
	((checkkbp)
	 (report-error 'user-warning "superclasses not declared for `~a'.~%I'll assume superclass `Thing'.~%" class)
	 '(#$Thing))
	(t '(#$Thing))))

;;; ----------

#|
Returns the FIRST cycle found, if there are any in the taxonomy, NIL otherwise.
A cycle is a list of classes where each class is a superclass of the previous,
and the first and last elements of the list are the same.
CL-USER(18): (km '#$(Vehicle has (superclasses (Car))))
CL-USER(19): (km '#$(Device has (superclasses (Vehicle))))
CL-USER(20): (km '#$(Car has (superclasses (Device))))
CL-USER(21): (check-for-cycles)
(|Car| |Device| |Vehicle| |Car|)
|#
(defun check-for-cycles ()
  (let ((all-classes (remove-if-not #'(lambda (concept)
					(or (get-vals concept '#$subclasses)
					    (get-vals concept '#$superclasses)))
				    (get-all-concepts))))
    (some #'check-for-cycles0 all-classes)))

(defun check-for-cycles0 (class &key done)
  (cond ((member class done) (append (member class (reverse done)) (list class)))
	(t (some #'(lambda (superclass)
		     (check-for-cycles0 superclass :done (cons class done)))
		 (or (get-vals class '#$superclasses)			; user-defined classes take priority (allow redefinition of built-ins)
		     (rest (assoc class *built-in-superclass-links*))
		     )))))

;;; ----------

(defun immediate-subclasses (class)
;  (find-vals class '#$subclasses))
  (cond ((eq class '#$Thing) (subclasses-of-thing))
	((let ( (subclasses (get-vals class '#$subclasses :situation *global-situation*)) )
	   (cond ((member class subclasses)
		  (report-error 'user-error "Cycle in the KB! ~a is its own subclass!" class)
		  (remove class subclasses))
		 (t subclasses))))
	((inv-assoc class *built-in-superclass-links*) 				; e.g. (immediate-subclasses '#$Number) -> (Integer)
	 (mapcar #'first (remove-if-not #'(lambda (pair) (eq (second pair) class)) *built-in-superclass-links*)))))

;;; ----------
;;; Returns subclasses of Thing, excluding built-in classes which aren't ever used in the KB.
;;; Here we infer subclasses for those unplaced classes.
;;; [1,2,3] Three pieces of evidence that the object is a class: [1] it has subclasses [2] it has instances [3] it's a built-in class.
;;; [4] These two built-in classes *don't* have Thing as their superclass.
;;; [5] Special case: If Integer (say) is explicitly in the KB, but Number isn't, then we should introduce Number in the retrieved
;;; 	taxonomy for printing and question-answering.
#|
(defun subclasses-of-thing ()
  (let* ( (all-objects (remove-if-not #'kb-objectp (dereference (get-all-concepts))))
	  (unplaced-classes+instances				; + includes classes explicitly directly under Thing
	   (remove-if #'(lambda (concept)
			  (let ( (superclasses (get-vals concept '#$superclasses :situation *global-situation*)) )
			    (or (and superclasses
				     (not (equal superclasses '#$(Thing))))		   ; ie. is placed (and not under Thing)
				(assoc concept *built-in-superclass-links*)))) ; [4], e.g. Integer, Aggregation-Slot
		      all-objects))
;	  (all-situations-and-theories (all-situations-and-theories))
	 (unplaced-classes (remove-if-not #'(lambda (concept)
					      (or (get-vals concept '#$subclasses)
						  (get-vals concept '#$superclasses)
						  (member concept *built-in-classes*))) ; [3]
					  unplaced-classes+instances))
	 (extra-classes (my-mapcan #'(lambda (class-superclass) ; [5]
					(cond ((and (member (first class-superclass) all-objects)
						    (not (member (second class-superclass) unplaced-classes))
						    (not (assoc (second class-superclass) *built-in-superclass-links*)))
					       (rest class-superclass))))
				    *built-in-superclass-links*))
	  )
    (remove '#$Thing (append extra-classes unplaced-classes))))
|#

(defun subclasses-of-thing ()
  (remove-duplicates
   (append (get-vals '#$Thing '#$subclasses)
	   (mapcar #'first (remove-if-not #'(lambda (class+superclass)
					      (and (eq (second class+superclass) '#$Thing)
						   (not (get-vals (first class+superclass) '#$superclasses)))) ; built-in not redefined by user
					  *built-in-superclass-links*))
	   (unplaced-classes))))

(defun unplaced-classes ()
  (remove-if-not #'unplaced-class (dereference (get-all-concepts))))

(defun unplaced-class (concept)
  (and (classp concept)
       (not (get-vals concept '#$superclasses))
       (not (assoc concept *built-in-superclass-links*))
       (neq concept '#$Thing)))

;;; ----------

;(defun immediate-subslots (slot)
;  (cond ((undeclared-slot slot) nil)		; supposed to be for efficiency, but slows it down!
;	(t (find-vals slot '#$subslots))))

(defun immediate-subslots (slot)
  (cond ; there are none yet ! ((second (assoc slot *built-in-subslots*)))
	(*are-some-subslots* 			; optimization flag (worth it?)
	 (get-vals slot '#$subslots :situation *global-situation*))))

;;; NB *doesn't* include slot.
(defun all-subslots (slot)
  (let ( (immediate-subslots (immediate-subslots slot)) )
    (append immediate-subslots (mapcan #'all-subslots immediate-subslots))))

(defun immediate-superslots (slot)
  (cond ; there are none yet ! ((second (assoc slot *built-in-subslots*)))
	(*are-some-subslots* 			; optimization flag (worth it?)
	 (get-vals slot '#$superslots :situation *global-situation*))))

;;; This *doesn't* include slot in the list
(defun all-superslots (slot)
  (let ( (immediate-superslots (immediate-superslots slot)) )
    (append immediate-superslots (mapcan #'all-superslots immediate-superslots))))

;;; ======================================================================

;;; [1] Misses inheritance! Probably not important, but better cover that case -> [2]
;;; [2] km-unique-int, as may be a path there (unlikely!, did in previous test suites though)
;;; [3] Don't consider it an error to be missing a :args structure, so we can say (Y1999 has (next-situation (Y2000))) for short.
;;; RETURNS: NIL if no prev situation, the atomic prev situation otherwise
(defun prev-situation (situation &optional instance)
  (declare (ignore instance))
  (let* ((prev-situation-args-structures0 (get-vals situation '#$prev-situation)) ; eg ((:args _Sit23 _Action23)) [2]
	 (prev-situation-args-structures (km-int (vals-to-val prev-situation-args-structures0)))
	 (prev-situation-args-structure (first prev-situation-args-structures)))
    (cond ((>= (length prev-situation-args-structures) 2)
	   (km-trace 'comment "Warning! (the prev-situation of ~a) Multiple previous situations ~a found! Taking just the first (~a)..."
		     situation prev-situation-args-structures prev-situation-args-structure)))
    (cond ((not (equal prev-situation-args-structures0 prev-situation-args-structures))
	   (put-vals situation '#$prev-situation prev-situation-args-structures)
;APR30		   (note-done situation '#$prev-situation *global-situation*)))
	   (note-done situation '#$prev-situation)))
    (cond ((km-argsp prev-situation-args-structure)
	   (arg1of prev-situation-args-structure))
	  (t prev-situation-args-structure))))

;;; Rather than going back to the previous situation, go back to the previous situation which has a
;;; value for instance's slot.
(defun prev-situation-with-vals (situation instance slot)
  (let ((prev-situation (prev-situation situation instance)))
    (cond (prev-situation
	   (cond ((get-vals instance slot :situation prev-situation) prev-situation)
		 (t (prev-situation-with-vals prev-situation instance slot)))))))

;(defun next-situations (situation)
; (let ( (next-situation-args-structures
;     (get-vals situation '#$next-situation :situation *global-situation*)) ) ; eg ((:args _Sit23 _Action23)) [1]
;   (mapcar #'(lambda (next-situation-args-structure)
;	       (cond ((km-argsp next-situation-args-structure)
;		      (arg1of next-situation-args-structure))
;		     ((kb-objectp next-situation-args-structure)
;		      next-situation-args-structure)
;		     (t (report-error 'user-error "Can't work out next situation of ~a!" situation))))
;	   next-situation-args-structures)))

;;; REVISION: from Francis Leboutte: Old version was producing very long lists with duplicates.
;;; Result is MAPCAN-SAFE
(defun next-situations (situation)
  (let ((next-situation-args-structures
         ;; eg ((:args _Sit23 _Action23)) [1]
         (get-vals situation '#$next-situation :situation *global-situation*)))
    ;; RVA 29Mar2007
    ;; make sure the returned list doesn't contain duplicate situations
    ;; especially important when using do-concurrently-and-next
    (let ((acc nil))
      (loop for next-situation-args-structure in next-situation-args-structures
            as next-situation =
            (cond ((km-argsp next-situation-args-structure)
                   (arg1of next-situation-args-structure))
                  ((kb-objectp next-situation-args-structure)
                   next-situation-args-structure)
                  (t
                   (report-error 'user-error "Can't work out next situation of ~a!" situation)))
            do (pushnew next-situation acc :test #'eq))
      acc)))

;;; INCLUDES situation
;;; Optimized version from Francis Leboutte
;(defun all-next-situations (situation)
;  (cond ((null situation) nil)
;	(t (cons situation (mapcan #'all-next-situations (next-situations situation))))))
(defun all-next-situations (situation)
  (declare (type symbol situation))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (cons situation
        (loop for situation in (next-situations situation)
              nconc (all-next-situations situation))))

;;; ========================================

;;; before-situation of an event
(defun before-situation (event)
 (let ( (before-situation-args-structures
	          (get-vals event '#$before-situation :situation *global-situation*)) ) ; eg ((:args _Sit23 _Action23)) [1]
;  (let ( (before-situation-args-structure
;	     (km-unique-int (find-unique-val event '#$before-situation :situation *global-situation*) ; eg ((:args _Sit23 _Action23)) [2]
;			)) )										; [3]
   (cond ((null before-situation-args-structures) nil)
	 ((singletonp before-situation-args-structures)
	  (let ( (before-situation-args-structure (km-unique-int (first before-situation-args-structures))) )
	    (cond ((not (equal before-situation-args-structure
			       (first before-situation-args-structures)))
		   (put-vals event '#$before-situation (list before-situation-args-structure)
			     :situation *global-situation*)
;APR30		   (note-done event '#$before-situation *global-situation*)))
		   (note-done event '#$before-situation)))
	    (cond ((km-argsp before-situation-args-structure)
;		   (km-format t "before-situation-args-structures = ~a~%" before-situation-args-structures)
		   (arg1of before-situation-args-structure))
		  (t before-situation-args-structure))))
	 (t (report-error 'user-error "Action ~a has multiple before situations, but that isn't allowed!~%  (~a has (before-situation ~a))~%"
			  event before-situation-args-structures)))))

;;; ======================================================================
;;;	BIND-SELF: Replace 'Self keyword with an instance name
;;; 9/22/00 - but DON'T replace quoted Selfs
;;; ======================================================================

#|
Efficiency: bind-self1 appears, to my surprise, 1.5 times slower (2.2 sec/million) than
bind-self2 (1.4 sec/million)!
(defun bind-self1 (expr self) (subst self 'Self expr))
(defun bind-self2 (frame self)
  (cond ((eq frame 'Self) self)
	((listp frame)				; [1]
	 (mapcar #'(lambda (x) (bind-self2 x self)) frame))
	(t frame)))

(defun test1 (n) (loop repeat n do (bind-self1 '(the cat sat on Self) 'test)))
(defun test2 (n) (loop repeat n do (bind-self2 '(the cat sat on Self) 'test)))
|#

#|
[1] a quoted expression has structure (quote <expr>) -- it should be guaranteed to be a pair, by the way the Lisp reader proceses "'" and "#,"
[2] Special case:
(a Person with (owns ('(a Car with (made-by (#,Self)))))) should return
		... '(a Car with (made-by (_Person4)))
	not	... '(a Car with (made-by (#,_Person4)))

(showme (a Person with (likes ('(the age of #,Self)))))		-> (_Person15 has (likes ('(the age of _Person15))))
(showme (a Person with (likes ('#,Self))))			-> (_Person16 has (likes ('_Person16))
(showme (a Person with (likes ('(the sum of #,(1 + 1)))))) 	-> (_Person17 has (likes ('(the sum of #,(1 + 1)))))
(showme (a Person with (likes ('(the sum of #,(the age of (evaluate '(the likes of #,Self))))))))
		-> (_Person18 has (likes ('(the sum of #,(the age of (evaluate '(the likes of _Person18)))))))

[3] It turns out, you can sometimes have quotes within quotes, e.g.
	(*definition-qn has
	  (answer-procedure ('#'(LAMBDA (CONCEPT) (SHOW-SLOT-VALUE CONCEPT 'text-def)))))
    So this isn't an error.
[4] SPECIAL CASE: (:triple ...) Self *doesn't* have to be explicitly unquoted, even though we treat it as if it's quoted.
    No special action is needed in the code here.
|#
#|
(defun bind-self (expr self &key in-quotes)
  (cond ((listp expr)				; [1]
	 (case (first expr)
	       (quote (list 'quote (bind-self (second expr) self :in-quotes t)))		; [3]
	       (unquote (cond (in-quotes (cond ((eq (second expr) '#$Self) self)				; [2]
					       (t (list 'unquote (bind-self (second expr) self :in-quotes nil))))) ; [1]
			      (t (report-error 'user-error "An unquoted expression #,~a was encountered inside a non-quoted expression (not allowed!)~%"
					     (second expr)))))
	       (t (mapcar #'(lambda (x) (bind-self x self :in-quotes in-quotes)) expr))))
	((and (eq expr '#$Self) (not in-quotes)) self)
	(t expr)))
|#
;;; EXECUTIVE DECISION 2/23/01 - Revert to the case where Self no longer has to be explicitly unquoted
(defun bind-self (expr self) (subst self '#$Self expr))

;;; ======================================================================

;;; Returns the most specific class(es) in a list
;;; (remove-subsumers '(car vehicle car tree)) -> (car tree)
;;; NOTE preserves order, so if there are no subsumers, then (remove-subsumers x) = x.
(defun remove-subsumers (classes)
  (let ((nodup-classes (remove-duplicates classes :from-end t)))	; much more efficient, reduces combinatorics
   (remove-if #'(lambda (class)
		  (some #'(lambda (other-class)
			    (and (neq other-class class)
				 (not (constraint-exprp class)) ; constraints allowed as class values
				 (not (constraint-exprp other-class))	; constraints allowed as class values
				 (is-subclass-of other-class class)))
			nodup-classes))
	      nodup-classes)))

;;; Returns the most general class(es) in a list
;;; (remove-subsumees '(car vehicle car tree)) -> (vehicle tree)
;;; NOTE preserves order, so if there are no subsumees, then (remove-subsumees x) = x.
(defun remove-subsumees (classes)
  (remove-duplicates
   (remove-if #'(lambda (class)
		  (some #'(lambda (other-class)
			    (and (neq other-class class)
				 (not (constraint-exprp class)) ; constraints allowed as class values
				 (not (constraint-exprp other-class)) ; constraints allowed as class values
				 (is-subclass-of class other-class)))	 classes))
	      classes)
   :from-end t))

;;; (classes-subsumes-classes classes1 classes2)
;;; TRUE if EVERY classes1 subsume SOME classes2. The intuition here is that
;;;    (remove-subsumers (append classes1 classes2)) -> classes2 (or more precisely -> (remove-subsumers classes2))
;;; This function still works if there are redundant classes in the list.
;;;
;;; (classes-subsume-classes '(vehicle expensive-thing) '(car very-expensive-thing))
;;; AND
;;; (classes-subsume-classes '(vehicle expensive-thing) '(car very-expensive-thing wheeled-thing))
;;; case [1] should never be necessary, but just in case...

;(defun classes-subsume-classes (classes1 classes2)
;  (let ( (trimmed-classes2 (remove-subsumers classes2)) )	; [1] eg. (car thing) -> (car)
;    (subsetp trimmed-classes2 (remove-subsumers (append classes1 trimmed-classes2)))))

;;; Or more efficiently...every class1 has some class2 which is a subclass of it.
(defun classes-subsume-classes (classes1 classes2)
  (every #'(lambda (class1)
	     (some #'(lambda (class2) (is-subclass-of class2 class1))
		   classes2))
	 classes1))

;;; ======================================================================
;;;		AND FOR NORMAL SPECIALIZATION LINKS
;;; ======================================================================

(defun all-classes (instance)
  (cons '#$Thing (remove-duplicates (mapcan #'all-superclasses0 (immediate-classes instance)))))

;;; ----------

;;; This *doesn't* include class in the list
(defun all-superclasses (class)
  (cond ((neq class '#$Thing)
	 (cons '#$Thing (remove-duplicates (my-mapcan #'all-superclasses0 (immediate-superclasses class)))))))

;;; Returns a *list* of superclasses, *including* class, but *not* including #$Thing, and possibly with duplicates.
(defun all-superclasses0 (class &key path-so-far)
  (cond ((eq class '#$Thing) nil)		; for efficiency. #$Thing is added by all-superclasses above
	((member class path-so-far)
	 (report-error 'user-error "You have a cycle in the taxonomy (not allowed)!~%~a~%"
		       (commaed-list (reverse (cons class path-so-far)) '->)))
	(t (cons class (my-mapcan #'(lambda (c)
				      (all-superclasses0 c :path-so-far (cons class path-so-far)))
				  (immediate-superclasses class))))))

;;; ----------

;;; This *doesn't* include class in the list
(defun all-subclasses (class)
  (remove-duplicates (mapcan #'all-subclasses0 (immediate-subclasses class))))

;;; Returns a *list* of subclasses, *including* class, but *not* including #$Thing, and possibly with duplicates.
(defun all-subclasses0 (class &key path-so-far)
  (cond ((member class path-so-far)
	 (report-error 'user-error "You have a cycle in the taxonomy (not allowed)!~%~a~%"
		       (commaed-list (cons class path-so-far) '->)))
	(t (cons class (my-mapcan #'(lambda (c)
				      (all-subclasses0 c :path-so-far (cons class path-so-far)))
				  (immediate-subclasses class))))))

#|
Prob. more efficient, but doesn't spot cycles.
(defun all-subclasses (class)
  (all-subclasses0 (list class)))

(defun all-subclasses0 (classes &optional subclasses-so-far)
  (cond
   ((endp classes) subclasses-so-far)
   (t (let ( (class (first classes)) )
	(cond ((member class subclasses-so-far)
	       (all-subclasses0 (rest classes) subclasses-so-far))
	      (t (let ( (new-subclasses-so-far (all-subclasses0 (immediate-subclasses class) (cons class subclasses-so-far))) )
		   (all-subclasses0 (rest classes) new-subclasses-so-far))))))))
|#
;;; This *doesn't* include situation in the list
(defun all-supersituations (situation)
  (cond ((neq situation *global-situation*)
	 (cons *global-situation* (remove-duplicates
				   (mapcan #'all-supersituations0 (immediate-supersituations situation)))))))

;;; Returns a *list* of situations, including situation but NOT including *global-situation*.
(defun all-supersituations0 (situation)
  (cond ((eq situation *global-situation*) nil)	  ; For efficiency. *global-situation* is added by all-supersituations
	(t (cons situation (mapcan #'all-supersituations0 (immediate-supersituations situation))))))

;;; ======================================================================
;;;			ALL-INSTANCES: find all instances of a class
;;; ======================================================================
#|
Includes dereferencing (in remove-dup-instances).
This is only used for:
	- (all-situations)
	- Handling a user's all-instances query
	- (mapc #'un-done (all-instances class))  after an (every ...) assertion. But this isn't quite
		right, we want to undo instances in class within a situation only too.
        - (all-instances '#$Slot), for (showme-all instance) and (evaluate-all instance)
	- we should really use it for Partition also; sigh...
Thus, we can get away being inefficient!!

[1] This is probably redundant, as instances should never be declared a fluent. However, it used to be
    allowed as an option a long time ago, so let's leave it there.
    NOTE: We *won't* consider *Global to be an instance of Situation, as really Situation is meant to mean
    situation-specific situation
[2] immediate-instances vs. full-immediate-instances
    CLib has a few statements that involve (the instances of ...) and
    (the all-instances of ...), e.g., on Time-Instant and Time-Interval.
    These are problematic with prototypes as currently a protoinstance is also
    an instance, and so these statements collect and start reasoning on
    protoinstances (not allowed!). It's a little schizophrenic, though,
    as the instance-of assertions are still there in the KB, just hidden
    from    (the instances of ...)
	    (the all-instances of ...)
    and the Lisp equivalents
            (all-instances <class>)
	    (immediate-instances <class>)
    i.e., one can view the above as meaning (the real-instances of ...) etc.
|#
(defun immediate-protoinstances (class) (remove-if-not #'protoinstancep (full-immediate-instances class)))
(defun all-protoinstances (class) (remove-if-not #'protoinstancep (full-all-instances class)))

(defun immediate-instances (class) (remove-if #'protoinstancep (full-immediate-instances class)))
(defun all-instances (class) (remove-if #'protoinstancep (full-all-instances class)))

(defun full-all-instances (class)
  (remove-duplicates
   (my-mapcan #'full-immediate-instances (cons class (all-subclasses class)))))	; dereferencing done in immediate-instances

;;; [1] This is probably redundant, as instances should never be declared a fluent. However, it used to be allowed as an option
;;; a long time ago, so let's leave it there.
;;; NOTE: We *won't* consider *Global to be an instance of Situation, as really Situation is meant to mean situation-specific situation
(defun full-immediate-instances (class)
  (remove-if-not #'kb-objectp			; object might be unified to a string
   (dereference		 			; Don't know if is neccesary, but put in to be safe!
    (cond ((and (neq class '#$Situation)					; Situation needs to collect ADDITIONAL user-created situations too (in next cond clause)
		(inv-assoc class (built-in-instance-of-links)))	  	; e.g. Boolean -> {t,f}
	   (mapcan #'(lambda (instance+class) (cond ((eq (second instance+class) class) (list (first instance+class))))) (built-in-instance-of-links)))
	  ((or (not (fluentp '#$instances))
	       (some #'(lambda (class2) (is-subclass-of class class2)) *built-in-classes-with-nonfluent-instances-relation*))   ; i.e. (Situation Slot Partition)
	   (get-vals class '#$instances :situation *global-situation*))
	  (t 				; instances is a fluent slot (NOT the default)
	   (km-slotvals2 class '#$instances))))))   ;;;  [1] does projection and constraint enforcement

;;; ----------

(defun immediate-prototypes (class) (get-vals class '#$prototypes :situation *global-situation*))
(defun all-prototypes (class)
  (remove-dup-instances
   (append (get-vals class '#$prototypes :situation *global-situation*)
	   (mapcan #'all-prototypes (immediate-subclasses class)))))

;;; ----------------------------------------

;;; Return a list of all situations used in the current session.
;;; It includes doing dereferencing (in all-instances)
;;; [1] Strictly, should be remove-dup-instances; however all-instances has already done this (including dereferencing), so we just need to make sure
;;;	we don't have *global-situation* in twice.
(defun all-situations ()
  (cond ((am-in-global-situation)
	 (remove-duplicates (cons *global-situation* (all-instances '#$Situation)) :from-end t))		; [1]
	(t (let ( (curr-situation (curr-situation)) )
	     (change-to-situation *global-situation*)
	     (prog1
		 (remove-duplicates (cons *global-situation* (all-instances '#$Situation)) :from-end t)	; [1]
	       (change-to-situation curr-situation))))))

;;; [1] NB Can't do a get-vals, as find-vals calls immediate-situations and we'd have a loop!
;;; We assume all situation facts and relationships are asserted in the global situation.
;;; A test in create-named-instance helps ensure this is maintained. We also check local for safety ([2]).
;(defun immediate-supersituations (situation)
;  (cond ((eq situation *global-situation*) nil)
;	((get-vals situation '#$supersituations :situation *global-situation*))
;	(t (list *global-situation*))))

;;; Modified by Fabien Dubail to include handling an expression in Supersituations
(defun immediate-supersituations (situation)
    (cond ((eq situation *global-situation*) nil)
          ((let ((supersits (get-vals situation '#$supersituations :situation *global-situation*)))
      						      ; get-vals > (|*Global| (|the| |world| |of| *S1))
	    (remove nil                        ; (km-int `#$(,SIT)) can be Nil
                    (mapcar #'(lambda (sit)
		            (cond ((kb-objectp sit) sit)
                                   (t (first (km-int `#$(,SIT))))))
                    supersits))))
        (t (list *global-situation*))
        ))

;;; ======================================================================
;;;			SLOTS: Cardinalities
;;; ======================================================================

(defconstant *default-default-fluent-status* '#$*Fluent) ; neah, don't change this!
(defparameter *default-fluent-status* *default-default-fluent-status*)	; user can change this

(defun default-fluent-status (&optional status)
  (cond ((null status)
	 (km-format t "By default, slots have fluent-status = ~a.~%" *default-fluent-status*)
	 '#$(t))
        ((member status *valid-fluent-statuses*)
;	 (setq *default-fluent-status* status)
;	 (make-transaction `(setq *default-fluent-status* ,status))
	 (km-setq '*default-fluent-status* status)
	 (km-format t "By default, slots now have fluent-status = ~a.~%" *default-fluent-status*)
	 '#$(t))
	(t (report-error 'user-error "Invalid default-fluent-status `~a'! (Must be one of ~a)~%" status *valid-fluent-statuses*))))

;;; ----------

;;; [1] if slot is known as a fluent, then t. Else NIL.
;;; [2] if slot is NOT known to be a non-fluent, then t.
(defun fluentp (slot)
  (case *default-fluent-status*
	(#$*Non-Fluent 		      (member (fluent-status slot)
					      '#$(*Fluent *Inertial-Fluent)))	; [1]
	(#$(*Fluent *Inertial-Fluent) (neq (fluent-status slot)			; [2]
					   '#$*Non-Fluent))))

(defun inertial-fluentp (slot)
  (case *default-fluent-status*
	(#$(*Non-Fluent *Fluent) (eq (fluent-status slot)
				     '#$*Inertial-Fluent))
	(#$*Inertial-Fluent      (not (member (fluent-status slot)
					      '#$(*Non-Fluent *Fluent))))))

;;; ----------

;;; [1] I could save a little CPU time with this
;;; but this would remove the error check for inconsistent status.
;;; Even better would be to cache the whole fluentp result. But I don't think I need these
;;; optimizations for now.
;; [2] Provide *either* an instance *or* a set of classes (of a non-created instance) to
;;;	see if it's an event.
;;; [3] These are add-list, del-list, pcs-list, ncs-list. In this case, allow user override if he/she wants - Eagh, let's hope he/she doesn't!!!
(defun fluent-status (slot)
  (cond
   ((member slot *built-in-inertial-fluent-slots*) '#$*Inertial-Fluent)
   ((member slot *built-in-non-inertial-fluent-slots*) '#$*Fluent)
   ((universalp slot) '#$*Non-Fluent)
   ((let ( (fluent-status1 (get-unique-val slot '#$fluent-status :situation *global-situation*))
	     (fluent-status2 #|(cond ((not fluent-status1) [1] |#
			     (get-unique-val (invert-slot slot) '#$fluent-status
					     :situation *global-situation*)) )
	(cond ((and fluent-status1 (not (member fluent-status1 *valid-fluent-statuses*)))
	       (report-error 'user-error "Invalid fluent-status `~a' on slot `~a'! (Should be one of: ~a)~%"
			     fluent-status1 slot *valid-fluent-statuses*))
	      ((and fluent-status2 (not (member fluent-status2 *valid-fluent-statuses*)))
	       (report-error 'user-error "Invalid fluent-status `~a' on slot `~a'! (Should be one of: ~a)~%"
			     fluent-status2 (invert-slot slot) *valid-fluent-statuses*))
	      ((and fluent-status1 fluent-status2 (neq fluent-status1 fluent-status2))
	       (report-error 'user-error "Inconsistent declaration of fluent-status! ~a has fluent-status ~a, but ~a has fluent-status ~a.~%"
			     slot fluent-status1 (invert-slot slot) fluent-status2))
	      (t (or fluent-status1 fluent-status2)))))))

;   ((member slot *built-in-non-inertial-fluent-slots*) '#$*Fluent)))		; [3]

;;; ----------

(defun single-valued-slotp (slot)
  (member (cardinality-of slot) '#$(1-to-1 N-to-1)))

(defun multivalued-slotp (slot) (not (single-valued-slotp slot)))

(defun inherit-with-overrides-slotp (slot)
  (or (get-vals slot '#$inherit-with-overrides :situation *global-situation* :dereferencep nil)
      (get-vals slot '#$simple-inherit-with-overrides :situation *global-situation* :dereferencep nil)))

(defun simple-inherit-with-overrides-slotp (slot)
  (get-vals slot '#$simple-inherit-with-overrides :situation *global-situation* :dereferencep nil))

(defun slots-to-opportunistically-evaluate (instance)
  (remove-duplicates
   (my-mapcan #'(lambda (class)
		  (get-vals class '#$slots-to-opportunistically-evaluate :facet 'member-properties :situation *global-situation* :dereferencep nil))
	      (all-classes instance))))

;;; Rather inefficient, I shouldn't need to do 2 kb-accesses for every slot query to see if it's single-valued or not!
(defun cardinality-of (slot)
  (cond
   ((member slot *built-in-single-valued-slots*) '#$N-to-1)
   ((member slot *built-in-multivalued-slots*) '#$N-to-N)
   ((or (cardinality-of2 slot)
	(invert-cardinality (cardinality-of2 (invert-slot slot)))
	*default-cardinality*))))

(defun cardinality-of2 (slot)
  (case slot
    (t (let ( (cardinalities (get-vals slot '#$cardinality :situation *global-situation* :dereferencep nil)) )
	 (cond ((null cardinalities) nil) 		; was *default-cardinality* - but I need to check the slot's inverse first!
	       (t (cond ((>= (length cardinalities) 2)
			 (report-error 'user-error "More than one cardinality ~a declared for slot ~a!Just taking the first ...~%"
				       cardinalities slot)))
		  (cond ((not (member (first cardinalities) *valid-cardinalities*))
			 (report-error 'user-error
				       "Invalid cardinality ~a declared for slot ~a.~%(Should be one of ~a). Assuming default ~a instead~%"
				       (first cardinalities) slot *valid-cardinalities* *default-cardinality*)
			 *default-cardinality*)
			(t (first cardinalities)))))))))

(defun invert-cardinality (cardinality)
  (cond ((eq cardinality nil) nil)
	((eq cardinality '#$1-to-N) '#$N-to-1)
	((eq cardinality '#$N-to-1) '#$1-to-N)
	((eq cardinality '#$N-to-N) '#$N-to-N)
	((eq cardinality '#$1-to-1) '#$1-to-1)
	(t (report-error 'user-error "Invalid cardinality ~a used in KB~%(Should be one of ~a)~%" cardinality *valid-cardinalities*)
	   cardinality)))

;;; ======================================================================
;;;			SLOTS: Inverses
;;; ======================================================================

#|
Automatic installation of inverse links:
eg. (install-inverses '*Fred 'loves '(*Sue))
will install the triple  (*Sue loves-of (*Fred)) in the KB.

[1] NOTE: special case for slot declarations:
	(install-inverses 'from 'inverse '(to))
want to assert
	(to (inverse (from)) (instance-of (Slot)))
not just
	(to (inverse (from))) 		; KM think's its a Class by default
and also (situation-specific (t)) if the forward slot is situation-specific.
This is justified because we know inverse's domain and range are Slot.

[2] Complication with Situations and projection:
  If   Fred loves {Sue,Mary}
  Then we km-assert Mike loves Mary,
  Then when we install-inverses, we assert Mary loves-of Mike, which over-rides
	(and prevents projection of) the old value of Mary loves-of Fred. So
  	we have to prevent installation of inverses for projected facts, or
	project the inverses also somehow.
  This has now been fixed; partial information is now merged with, rather than
    	over-rides, projected information.

With multiargument values, this is rather intricate...
    (install-inverses Fred loves (:args Sue lots))
  -> (install-inverse (:args Sue lots) loved-by Fred)
   ->  (install-inverse Sue loved-by (:args Fred lots))				Assert
   AND POSSIBLY (install-inverse lots amount-of-love-given-to (:args Sue Fred))	Assert
   AND IF SO, ALSO (install-inverses lots amount-of-love-given-to (:args Sue Fred))
    ->  (install-inverse Sue receives-love-of-amount (:args lots Fred))		Assert
     AND POSSIBLY (install-inverse Fred gives-amount-of-love (:args lots Sue))
     AND IF SO, ALSO (install-inverses Fred gives-amount-of-love (:args lots Sue))
    -> ...

|#
;;; [1] put-vals for single-valued slots may be called with value (val & constraint), so must unpack this expression to make sure inverse is
;;; installed.
;;; RETURNS: irrelevant
(defun install-inverses (frame slot vals &optional (situation (target-situation (curr-situation) frame slot)))
  (cond  ((not *installing-inverses-enabled*))		; skip otherwise
	 ((not (listp vals))
	 (report-error 'program-error "Non-list ~a passed to (install-inverses ~a ~a ~a)!~%" vals frame slot vals))
        ((not (non-inverse-recording-slot slot))
	 (let ( (invslot (invert-slot slot)) )
	   (mapc #'(lambda (val)
		     (cond ((or (kb-objectp val) (km-argsp val)) (install-inverses0 val invslot frame slot situation))
			   ((&-exprp val) (install-inverses frame slot (&-expr-to-vals val)) :situation situation))) ; [1] otherwise ignore it
		 vals)))))

#|
Install a link (invframe0 invslot invval).
This basically does an add-val, except it also does:
;  1. If invframe0 is a Slot, and we're declaring an inverse, then KM also copies the situation-specific property
;   		from the invframe0's inverse to this frame.
   2. If invframe0 is a multi-argument structure (:args v1 v2), then as well as asserting (invframe0 invslot v1)
		we also assert (invframe0 inv2slot v2), and possibly (invframe0 inv3slot v3).
Note that to make sure inverses of inverse2's are installed, we set install-inversesp to t if invval is a (:args v1 v2)
  structure [1]. This will eventually terminate, as the "don't already know it" test fails:
		(not (member invval (find-vals invframe invslot 'own-properties situation) :test #'equal))) ; don't already know it
[2] Note: inverse, inverse2, inverse3 and situation-specific are all non-fluents, so we work in the global
situation for manipulating this data.
[3] This is redundant, now done by add-slotsvals more intelligently
|#
(defun install-inverses0 (invframe0 invslot invval slot &optional (situation (target-situation (curr-situation) invframe0 invslot)))
  (let ( (invframe (dereference invframe0)) )
    (cond ((and (kb-objectp invframe)
		(not (non-inverse-recording-concept invframe))    		; eg. don't want boolean (T has (open-of (Box1))
		(not (member invval (get-vals invframe invslot :situation situation) :test #'equal)))  ; don't already know it
	   (let ( (install-inversesp (km-argsp invval)) )			    ; [1] nil, unless a :args structure, in which case iterate
	     (add-val invframe invslot invval install-inversesp situation))	    ;     so all inverses are installed.
; NEW: see [3]
;	   (cond ((member slot '#$(inverse inverse2 inverse3))			    ; See earlier [2]
;		  (add-val invframe '#$instance-of '#$Slot t *global-situation*)))
	   (classify invframe :slots-that-changed (list invslot))
	   )
	  ((km-argsp invframe)							; multiargument value, eg. Fred loves (:args Sue lots)
	   (install-inverses0 (second invframe) invslot 			; do first argument...    Sue loved-by (:args Fred lots)
			    `#$(:args ,INVVAL ,@(REST (REST INVFRAME))) slot situation)
	   (cond ((and (third invframe)						; do second argument...    lots love-given-to (:args Sue Fred)
		       (or (assoc slot *built-in-inverse2s*)
			   (get-unique-val slot '#$inverse2 :situation *global-situation*)))
		  (let ( (inv2slot (or (second (assoc slot *built-in-inverse2s*))
				       (get-unique-val slot '#$inverse2 :situation *global-situation*)))
			 (modified-args `#$(:args ,(SECOND INVFRAME) ,INVVAL ,@(REST (REST (REST INVFRAME))))) )	;  (:args Sue Fred)
		    (install-inverses0 (third invframe) inv2slot modified-args slot situation))))
	   (cond ((and (third invframe)
		       (get-unique-val slot '#$inverse12 :situation *global-situation*))
		  (let ( (inv12slot (get-unique-val slot '#$inverse12 :situation *global-situation*))
			 (modified-args `#$(:args ,(ARG2OF INVFRAME) ,(ARG1OF INVFRAME) ,@(REST (REST (REST INVFRAME))))) )
		    (add-val invval inv12slot modified-args t situation))))		; install-inversesp = t
	   (cond ((and (fourth invframe)							; do third argument
		       (get-unique-val slot '#$inverse3 :situation *global-situation*))
		  (let ( (inv3slot (get-unique-val slot '#$inverse3 :situation *global-situation*))
			 (modified-args `#$(:args ,(SECOND INVFRAME) ,(THIRD INVFRAME) ,INVVAL ,@(REST (REST (REST (REST INVFRAME)))))) )
		    (install-inverses0 (fourth invframe) inv3slot modified-args slot situation))))))))

;;; ----------

;;; Undo the install operation, INCLUDING deleting explanations.
(defun uninstall-inverses (frame slot vals &optional (situation (target-situation (curr-situation) frame slot)))
  (cond ((not (non-inverse-recording-slot slot))
	 (let ( (invslot (invert-slot slot)) )
	   (mapc #'(lambda (val0)
		     (let ( (val (dereference val0)) )
		       (cond ((and (kb-objectp val)
				   (not (non-inverse-recording-concept val))    ; eg. don't want boolean
				   						; (T has (open-of (Box1))
				   (member frame (get-vals val invslot :situation situation)))
			      (let ( (new-vals (remove frame (get-vals val invslot :situation situation))) )
				(delete-explanation val invslot frame :explanation-to-delete 'all :situation situation)
				(put-vals val invslot new-vals :install-inversesp nil :situation situation))))))
		 vals)))))


;;; ----------
;;; Evaluate local expressions, with the intension that inverses will
;;; be installed. Used by forc function in interpreter.lisp
;;; MUST return instance as a result.
;;; We just deal with slotsvals in the current situation.

(defun eval-instance (instance)
  (eval-instances (list instance))
  instance)

;;; Note, we have to keep recurring until a stable state is reached. Just checking for newly created
;;; instances isn't good enough -- some expansions may cause delayed unifications, without creating new instances.
(defun eval-instances (&optional (instances (obj-stack)) &key (n 0))
  (cond
   ((null instances))
   ((>= n 100)
    (report-error 'user-error "eval-instances in frame-io.lisp!~%Recursion is causing an infinite graph to be generated! Giving up...~%"))
   (t (let ( (obj-stack (obj-stack)) )
	(mapc #'simple-eval-instance instances)
	(cond (;(not (am-in-prototype-mode))
	       (use-prototypes)
	       (mapc #'unify-in-prototypes instances)
	       (mapc #'classify instances))
	      (t 			; ie. (am-in-prototype-mode)
	       (mapc #'eval-constraints instances))) ; expand (<> (the Car)) -> (<> _ProtoCar23)
	(eval-instances (ordered-set-difference (obj-stack) obj-stack) ; process newly created instances
			:n (1+ n))))))

;   (t (let ( (expansion-done? (remove nil (mapcar #'simple-eval-instance instances))) )
;	(cond (expansion-done? (eval-instances (obj-stack) (1+ n))))))))

(defun eval-constraints (instance)
  (mapc #'(lambda (slotvals)
	    (let ( (new-vals (mapcar #'(lambda (val)
					 (cond ((and (pairp val)
						     (eq (first val) '<>))
						(list '<> (km-unique-int (second val) :fail-mode 'error)))
					       (t val)))
				     (vals-in slotvals))) )
	      (cond ((not (equal slotvals new-vals))
		     (put-vals instance (slot-in slotvals) new-vals :install-inversesp nil)))))
	(get-slotsvals instance)))

;;; [1] More conservative - only evaluate paths, rather than force inheritance when only atomic instances are present.
;;; return t if some expansion was done, to make sure we get everything!
(defun simple-eval-instance (instance)
  (remove nil
	  (mapcar #'(lambda (slotvals)
		      (cond ((some #'(lambda (val)
				       (and (not (fully-evaluatedp val))
					    (not (constraint-exprp val))))
; for debugging				    (or (km-format t "expanding (~a has (~a (~a)))...~%" instance (slot-in slotvals) val) t)
				   (vals-in slotvals))	; [1]

			     (km-int `#$(the ,(SLOT-IN SLOTVALS) of ,INSTANCE))
			     t)))
		  (get-slotsvals instance))))

;;; ----------------------------------------

;;; *inverse-suffix* = "-of" (case-sensitivity on) "-OF" (case-sensitivity off)
(defun invert-slot (slot)
  (cond	((second (assoc slot *built-in-inverses*)))	; use built-in declarations
	((not (check-isa-slot-object slot)) nil)
        ((get-unique-val slot '#$inverse :situation *global-situation*))	; look up declared inverse
	(t (let ( (str-slot (symbol-name slot)) )		; default computation of inverse
	     (cond ((and (> (length str-slot) 3)
			 (ends-with str-slot *inverse-suffix*)) 		; "parts-of"
		    (intern (trim-from-end str-slot *length-of-inverse-suffix*) *km-package*))
		   (t (intern (concat str-slot *inverse-suffix*) *km-package*)))))))


;;; Thanks to Ken Murray for this one:
(defun invert-predicate (predicate &optional (argnum 2))
  "return the inverse variant of PREDICATE such that
   the first and ARGNUMth args have been swapped."
  (case argnum
    (1 predicate)
    (2 (invert-slot predicate))
    (3 (km-unique `(#$the #$inverse2 #$of ,predicate)))
    (4 (km-unique `(#$the #$inverse3 #$of ,predicate)))))


;;; ======================================================================
;;;		SLOTS: Check conformance with slot declarations
;;; ======================================================================

;;; RETURNS: nil - simply checks for domain and range violations
#|
Warning! Asserting (Pete has (location (Farm1 Farm2)))...
         Pete isn't a Place (violates the domain constraint for `location')
         Farm2 isn't a Place (violates the range constraint for `location')
|#
(defun check-domain-and-range (instance slot vals)
  (let* ( (domains (domains-of slot))
	  (ranges (ranges-of slot))
	  (domain-violation
	   (cond ((and domains
		       (notany #'(lambda (domain) (instance-of instance domain)) domains))
		  (cond ((some #'(lambda (domain) (compatible-classes :instance1 instance :classes2 (list domain))) domains))
			(t (report-error 'user-error "Attempt to access (the ~a of ~a), but ~a is incompatible with the domains of `~a' ~a!"
					 slot instance instance slot domains))))))
	  (range-violations
	   (cond (ranges
		  (remove-if-not #'(lambda (val)
				     (cond ((and (kb-objectp val)
						 (notany #'(lambda (range) (instance-of val range)) ranges))
					    (cond ((some #'(lambda (range) (compatible-classes :instance1 val :classes2 (list range))) ranges) val)
						  (t (report-error 'user-error "Attempt to put ((the ~a of ~a) = ~a), but ~a is incompatible with the ranges of `~a' ~a!"
								   slot instance val val slot ranges))))))
				 vals)))) )
    (cond ((or domain-violation range-violations)
	   (km-format t "Warning! Asserting (~a has (~a (~a))):~%" instance slot vals)
	   (cond (domain-violation
		  (km-format t "         ~a isn't one of  ~a (violates the domain constraint for `~a')~%" instance domains slot)))
	   (mapc #'(lambda (range-violation)
		     (km-format t "         ~a isn't one of ~a (violates the range constraint for `~a')~%" range-violation ranges slot))
		 range-violations)))))

;;; ----------

(defun check-isa-slot-object (slot)
  (cond ((listp slot)
	 (report-error 'user-error "Non-atomic slot ~a encountered! (Missing parentheses in expression?)~%" slot))
	((numberp slot)
	 (report-error 'user-error "Numbers can't be used as slots! (A slot named `~a' was encountered)~%" slot))
	((not (slot-objectp slot))
	 (report-error 'user-error "Invalid slot name `~a' encountered! (Slots should be a non-nil symbol)~%" slot))
	(t)))		; otherwise, it's a slot!

(defun check-slot (frame slot values)
  (declare (ignore frame values))
  (cond
   ((not (checkkbp)))
   ((built-in-concept slot))
   ((undeclared-slot slot))
   (t (let ( (domains (domains-of slot))
	     (ranges (ranges-of slot)) )
	(cond ((not domains) (report-error 'user-warning "Domain for slot ~a not declared.~%" slot)))
	(mapc #'(lambda (domain)
		  (cond ((not (known-frame domain))
			 (report-error 'user-warning "Domain ~a for slot ~a not declared in KB.~%" domain slot))))
	      domains)
	(cond ((not ranges) (report-error 'user-warning "Range for slot ~a not declared.~%" slot)))
	(mapc #'(lambda (range)
		  (cond ((not (known-frame range))
			 (report-error 'user-warning "Range ~a for slot ~a not declared in KB.~%" range slot))))
	      ranges)))))

(defun domains-of (slot)
  (or (get-vals slot '#$domain :situation *global-situation*)
      (get-vals (invert-slot slot) '#$range :situation *global-situation*)))

(defun ranges-of (slot)
  (or (get-vals slot '#$range :situation *global-situation*)
      (get-vals (invert-slot slot) '#$domain :situation *global-situation*)))

(defun undeclared-slot (slot)
  (cond ((not (symbolp slot))
	 (report-error 'user-error "Non-slot ~a found where a slot was expected!~%" slot) t)
	((and (not (known-frame slot))
	      (not (known-frame (invert-slot slot)))
	      (not (built-in-concept slot)))
	 (cond ((checkkbp) (report-error 'user-warning "Slot ~a (or inverse ~a) not declared.~%"
					 slot (invert-slot slot))))
	 t)))

;;; ======================================================================
;;;		AND FOR NORMAL SPECIALIZATION LINKS
;;; ======================================================================

#|
We assume the superclasses are correctly installed.
put-vals will avoid most redundancy in the superclasses link, but unfortunately
not all (see comments on put-vals above).
The subclasses links can still get redundancies in, for example:
	KM> (Car has (superclasses (Vehicle)))
	KM> (Nissan has (superclasses (Vehicle)))
	KM> (Nissan has (superclasses (Car)))
	KM> (showme 'Nissan)
	(Nissan has (superclasses (Car)))		; OK
	KM> (showme 'Vehicle)
	(Vehicle has (subclasses (Nissan Car)))		; Not OK

Call (clean-taxonomy) to recompute the taxonomy without redundancies.

[1] strips all subclass links
[2] walks through every superclass link, installing respective subclass links
[3] final check for unconnected nodes
|#
;;; ----------------------------------------

(defun install-all-subclasses ()
  (format t "(install-all-subclasses) has been renamed (clean-taxonomy). Please update your code!~%"))

;;; RETURNS: TWO values: List of classes whose supers were changed, list of classes whose subs were changed
;;; [3] You know, let's leave the unplaced-classes as unplaced. (immediate-subclasses '#$Thing) and (the subclasses of Thing)
;;;     will still return them (as it calls (subclasses-of-thing), but we want to leave them unplaced so we can flag them later.
(defun clean-taxonomy (&key silentp)
  (cond ((not silentp) (format t "Removing redundant superclasses...~%")))
  (let ((modified-classes1 (my-mapcan #'remove-redundant-superclasses (get-all-concepts)))) ; [2]
    (cond ((not silentp) (format t "Removing redundant subclasses...~%")))
    (let ((modified-classes2 (my-mapcan #'remove-redundant-subclasses (get-all-concepts)))) ; [2]
      (cond ((not silentp) (format t "Computing subclasses of Thing...~%")))
      (let* (; (modified-classes3 (update-subclasses-of-thing))
	     (modified-classes3 nil)	; [3]
	     (modified-classes (append modified-classes1 modified-classes2 modified-classes3)) ; ((supers1 subs1) (supers2 subs2) (supers3 subs3) ...)
	     (sets-of-changed-supers+sets-of-changed-subs (transpose modified-classes))	       ; ((supers1 supers2 supers3 ...) (subs1 subs2 subs3 ...))
	     (sets-of-changed-supers (first sets-of-changed-supers+sets-of-changed-subs))
	     (sets-of-changed-subs (second sets-of-changed-supers+sets-of-changed-subs))
	     (changed-supers (remove-duplicates (append-lists sets-of-changed-supers)))
	     (changed-subs (remove-duplicates (append-lists sets-of-changed-subs))))
	(check-partitions)
	(values changed-supers changed-subs)))))

#|
(defun update-subclasses-of-thing ()
  (let* ((subclasses-of-thing (get-vals '#$Thing '#$subclasses))
	 (actual-subclasses-of-thing (subclasses-of-thing)) ; [3]
	 (extra-subclasses-of-thing (set-difference actual-subclasses-of-thing subclasses-of-thing)))
    (cond (extra-subclasses-of-thing
	   (mapc #'(lambda (val) (add-val '#$Thing '#$subclasses val)) extra-subclasses-of-thing)
	   `((,extra-subclasses-of-thing (#$Thing)))))))		;;; Cs with changed superclasses, Cs with changed subclasses
|#

(defun update-subclasses-of-thing ()
  (let ((extra-subclasses-of-thing (unplaced-classes)))
    (cond (extra-subclasses-of-thing
	   (mapc #'(lambda (val) (add-val '#$Thing '#$subclasses val)) extra-subclasses-of-thing)
	   `((,extra-subclasses-of-thing (#$Thing)))))))		;;; Cs with changed superclasses, Cs with changed subclasses

;;; ----------------------------------------
;;; This is too slow to include in the loader for all superclass changes
#|
X <| C
X <| GenC    hence  X <| C, GenC
Now add C <| GenC, X <| GenC is redundant and should be removed, so foreach GenC's subclasses, check for
	redundancy in its superclasses link

ALSO:
C <| D
GenC <| D    hence   D subclasses C, GenC
Now add C <| GenC, C <| D is redundant and should be removed, so foreach C's superclasses, check for
	redundancy in its subclasses link
|#
;;; class's superclasses have just been updated to be superclasses
;(defun remove-redundancies-in-superclasses (class superclasses)
;  (declare (ignore class))
;  (mapc #'(lambda (superclass)
;	    (mapc #'remove-redundant-superclasses (immediate-subclasses superclass)) ; [1]
;	    (remove-redundant-subclasses superclass))				     ; [2]
;	superclasses))

;;; ----------------------------------------

;;; RETURNS: A (singleton) list of a pair ((SUPERS SUBS)) where
;;;	SUPERS = a list of classes whose supers were changed, SUBS = list of classes whose subs were changed
(defun remove-redundant-superclasses (class)
  (let* ((superclasses (get-vals class '#$superclasses))
	 (minimal-superclasses (remove-subsumers superclasses)))
    (cond ((not (set-equal superclasses minimal-superclasses))
	   (let ((redundant-superclasses (set-difference superclasses minimal-superclasses)))
	     (mapc #'(lambda (redundant-superclass)
		       (delete-val class '#$superclasses redundant-superclass)
		       (make-comment "Removing redundant superclass ~a in (~a has (superclasses (~a)))"
				     redundant-superclass class superclasses))
		   redundant-superclasses)
	     `(((,class) ,redundant-superclasses)))))))	     ;;; Cs with changed superclasses, Cs with changed subclasses

;;; RETURNS: A (singleton) list of a pair ((SUPERS SUBS)) where
;;;	SUPERS = a list of classes whose supers were changed, SUBS = list of classes whose subs were changed
(defun remove-redundant-subclasses (class)
  (let* ((subclasses (get-vals class '#$subclasses))
	 (minimal-subclasses (remove-subsumees subclasses)))
    (cond ((not (set-equal subclasses minimal-subclasses))
	   (let ((redundant-subclasses (set-difference subclasses minimal-subclasses)))
	     (mapc #'(lambda (redundant-subclass)
		       (delete-val class '#$subclasses redundant-subclass)
		       (make-comment "Removing redundant subclass ~a in (~a has (subclasses (~a)))"
				     redundant-subclass class subclasses))
		   redundant-subclasses)
	     `((,redundant-subclasses (,class))))))))	 ;;; Cs with changed superclasses, Cs with changed subclasses

;;; --------------------------------------------------

;;; Check partitions below and above the argument class
;;; This function returns t if a partition was violated.
(defun check-partitions (&optional (start-class '#$Thing))
  (mapc #'violated-partitions-at-class (all-subclasses start-class)))

#|
(defun check-partitions (&optional (start-class '#$Thing))
  (check-partitions0 (list start-class)))

(defun check-partitions0 (classes &key done)
  (let ((class (first classes)))
    (cond
     ((endp classes) nil)
     ((member class done)
      (check-partitions0 (rest classes) :done done))
     (t (violated-partitions-at-class class) ; return answer
        (check-partitions0 (append (immediate-subclasses class) (rest classes)) :done (cons class done))))))
|#

;;; disjoint-classes collects all the superclasses of (and including) class and checks they are not disjoint.
;;; This function returns t if a partition was violated.
(defun violated-partitions-at-class (class &key indirectp)
  (let ((violated-partitions (remove-duplicates (remove-singletons (disjoint-classes (list class) :check-singletonp t)))))
    (cond
     (violated-partitions
      (report-error 'user-warning `(|partition-violation| ,class '#$superclasses '* ,violated-partitions)
		    (cond (indirectp "Indirect partition violation (re)detected!~%   Some of ~a's superclasses are become mutually exclusive, partition(s) ~a were violated:~%~:{     ~a:~25t~a~%~:}")
			  (t "Partition violation!~%   Some of ~a's superclasses are mutually exclusive, partition(s) ~a were violated:~%~:{     ~a:~25t~a~%~:}"))
		    class (delistify violated-partitions)
		    (mapcar #'(lambda (violated-partition) (list violated-partition (get-vals violated-partition '#$members))) violated-partitions))
      t))))

;;; ======================================================================
;;;			THE SITUATION MECHANISM
;;; ======================================================================

;;; [1] Note we don't dereference *curr-situation*, in case it's bound to *Global.
;;; If it is bound to global, we want to (i) change *curr-situation* to point to
;;; *Global directly and (ii) by a subtle interaction, (reset-kb) get's messed up
;;; otherwise: If we leave *curr-situation* as (say) _S2, thinking it's *Global
;;; (as it's bound to *Global), but then do an (unbind), we're then left apparently
;;; in a (now unbound) _S2!

;;; Must return a list of values (here, just a singleton) for consistency
(defun global-situation ()
  (cond ((neq *curr-situation* *global-situation*)		; [1]
	 (in-situation *global-situation*))
	(t (list *global-situation*))))

;;; A KM function passed to Lisp:
;;; NB 2.12.99 dereference added!!!
(defun curr-situation () (dereference *curr-situation*))

(defun in-situation (situation-expr &optional km-expr theoryp)
  (cond ((and (tracep) (not (traceothersituationsp)))
	 (let* ((*trace* nil))
	   (in-situation0 situation-expr km-expr theoryp)))
;	 (prog2
;	     (suspend-trace)
;	     (in-situation0 situation-expr km-expr theoryp)
;	   (unsuspend-trace)))
	(t (in-situation0 situation-expr km-expr theoryp))))

;;; [1] The special case which *is* allowed, of an (in-situation *Global ...) issued when within a prototype, will be caught earlier by [2].
(defun in-situation0 (situation-expr &optional km-expr theoryp)
  (let* ( (situation-structure (km-unique-int situation-expr))
	  (situation (cond ((and (not theoryp)
				 (km-argsp situation-structure)) (arg1of situation-structure))	; e.g. situation-expr = (the next-situation of ...)
			   (t situation-structure))) 						; e.g. situation-expr = (a Situation)
	  (situation-class (cond (theoryp '#$Theory)
				 (t '#$Situation))) )
    (cond ((and (not theoryp) (neq situation-expr *global-situation*)) (set-situations-mode)))
    (cond ((eq situation (curr-situation))			; [2]
	   (cond ((neq (curr-situation) *curr-situation*)
		  (change-to-situation (curr-situation))))	; in case *curr-situation* is bound, but not eq, to (curr-situation)
	   (cond (km-expr (km-int km-expr))
		 (t (list (curr-situation)))))
	  ((am-in-prototype-mode)				; [1]
	   (report-error 'user-error "Trying to do ~a: Can't enter a ~a when you're in prototype mode!~%"
			 (cond ((and theoryp km-expr) `#$(in-theory ,SITUATION-EXPR ,KM-EXPR))
			       (km-expr `#$(in-situation ,SITUATION-EXPR ,KM-EXPR))
			       (theoryp `#$(in-theory ,SITUATION-EXPR))
			       (t `#$(in-situation ,SITUATION-EXPR)))
			 situation-class))
	  ((or (not situation)
	       (not (kb-objectp situation)))
	   (report-error 'user-error "~a doesn't evaluate to a ~a (results in ~a instead)!~%"
			 situation-expr situation-class situation-structure))
	  ((not (isa situation situation-class))
	   (report-error 'user-error "~a doesn't evaluate to a ~a (~a isn't declared an instance of ~a)!~%"
			 situation-expr situation-class situation situation-class))
	  ((not km-expr)
	   (cond ((and (kb-objectp situation-expr)
		       (neq situation-expr situation))
		  (make-comment "~a ~a is bound to ~a" situation-class situation-expr situation)))
	   (make-comment "Changing to ~a ~a" situation-class situation)
	   (list (change-to-situation situation)))		; must return a list of values, for consistency
	  (t (let ( (curr-situation (curr-situation)) )
	       (km-trace 'comment "")			; does a nl
	       (km-trace 'comment "Temporarily changing to ~a ~a..." situation-class situation)
	       (change-to-situation situation)
	       (prog1
		   (km-int km-expr)
		 (change-to-situation curr-situation)
		 (km-trace 'comment "Exiting ~a ~a, and returning to ~a." situation-class situation curr-situation)
		 (km-trace 'comment "")))))))


(defun am-in-global-situation () (eq (curr-situation) *global-situation*))
(defun am-in-local-situation () (and (neq (curr-situation) *global-situation*)
				     (not (isa-theory (curr-situation)))))
(defun change-to-situation (situation)
;  (make-transaction `(setq *curr-situation* ,situation)))
  (km-setq '*curr-situation* situation))

(defun am-in-local-situation-or-theory () (neq (curr-situation) *global-situation*))

;;; next-situation will create a new situation which is at the next-situation relation
;;; to the situation given.
;;; action is an INSTANCE (it better be!)
;;; RETURNS: The next situation
(defun next-situation (action &key next-situation)
    (cond ((am-in-global-situation)
	   (report-error 'user-error "You must be in a Situation to create a next-situation!~%"))
	  (t (let ((curr-situation (curr-situation))
		   (new-situation (or next-situation (make-new-situation))))
;; changed by Fabien Dubail from "has" to "also-has" to avoid unification of anonymous actions
	       (km-unique-int `#$(,NEW-SITUATION also-has
		(instance-of (Situation))
	 	(prev-situation ((:args ,CURR-SITUATION ,ACTION)))) :fail-mode 'error))))) ; inverse auto-installed

(defun new-situation ()
  (in-situation (make-new-situation)))

(defun make-new-situation ()
  (km-unique-int `#$(a Situation with (supersituations (,*GLOBAL-SITUATION*))) :fail-mode 'error))

;;; always t for now -- disable this verification step
(defun isa-situation-facet (situation) (declare (ignore situation)) t)

;;; facet refers to a global property list, for storing data.
;;; In the global situation, we refer to that facet directly. In a local
;;; situation, we create a situation-specific property list storing that data.
;;; The facet "own-properties" in _Sitn1 becomes "own-properties_Sitn1".
;;; To avoid computing this symbol many times, I cache it using get/setf:
;;;	SYMBOL		PROPERTY   VALUE
;;;	own-properties  _Sitn1     own-properties_Sitn1
;;; This simply caches the concatenation of these two symbols into a third
;;; symbol, hopefully being more efficient than reconcatenating and interning
;;; the symbols' strings!
;;; 3.25.99 - time on test suite goes up from 20 to 37 secs without this caching!
;;; Looks like it's doing something useful...
;;; [1] is simply an optimization, so doesn't need to be undone with roll-back

;;; Optimized version from Francis Leboutte
(defun curr-situation-facet (facet &optional (curr-situation (curr-situation)))
  (declare (type symbol facet))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (cond ((eq curr-situation *global-situation*) facet)
	((get facet curr-situation))
	(t
         (setf (get facet curr-situation) 				; [1]
               (intern (concatenate 'string
                                    (symbol-name facet)
                                    (symbol-name curr-situation))
                       *km-package*)))))

;(defun curr-situation-facet (facet &optional (curr-situation (curr-situation)))
;  (cond ((eq curr-situation *global-situation*) facet)
;	((get facet curr-situation))
;	(t ; (km-format t "making a new facet...~%")
;	   (setf (get facet curr-situation) 				; [1]
;		 (intern (concat (symbol-name facet) (symbol-name curr-situation)) *km-package*)))))

;;; ======================================================================
;;;		SITUATION TRANSITIONS:
;;; ======================================================================

(defvar *user-has-been-warned* nil)

(defvar *interactive-preconditions* nil)

;;; Effects can be either quoted propositions or :triple statements (take your pick!)
;;;
;;; a PROPOSITION is a structure of the form (:triple F S V), where V may be (:set a b)
;;;
;;; Note we must precompute all the effects *before* actually making them, to avoid one
;;; effect being considered as part of the initial situation for calculating another.
;;; [2] Here we insist the user to make Events explicitly identifiable by KM.
;;;     KM uses this information when computing projection, namely NEVER project slot-values for Events.
;;;     The reason for this is somewhat complicated.
;;; [1] NOTE: consistency check &? in lazy-unify **DOESN'T** do projection, so better provoke it here!
;;; [3] It shouldn't really matter where I compute add-list and del-list, although the later position is better (in case the pcs-list fails).
;;;	HOWEVER: the "Forward propogate relevant facts" causes some undesirable unifications of values, which cause actions to be misunified
;;;	together -- this is the familiar bug with &&'ing inverses together. If I move the test [3] earlier, then I can get the add- and del-list
;;;	before this destruction is caused. Hack!
;;;	Later: No, we must evaluate del-list AFTER the pcs-list have been asserted! Suppose the del-list says (forall <x> (:triple ...))
;;;		  and the pcs-list asserts the existence of an <x>, we better make sure the pcs-list are evaluated first!
;;; [4]
;;;	We need to allow for conditional add-list and del-list, which means that
;;;	(i) add-list etc. are changed to non-inertial fluents
;;;     (ii) retrieval of the add-list etc. must be done in the situation BEFORE the action is performed, but AFTER any pcs have
;;;			been assumed
;;; [5] Must disable classification, or else assert -> classify -> premature computation of other slot-values, before other adds/dels have been done!
(defun do-action (action-expr &key next-situation change-to-next-situation (test-or-assert-pcs 'assert))
 (let ((*classification-enabled* nil))	; [5]
   (cond ((not *user-has-been-warned*)
	  (km-format t "
----------------------------------------------------------------------
	KM 1.4.0.51 and later: IMPORTANT CHANGE!!
	=========================================
The default fluent-status of slots is now *Fluent, *NOT* *Inertial-Fluent.
Make sure the fluent-status of your slots are set correctly -- See the
KM Situations Manual, Section 6.2, p23-24 for the rules to follow.
----------------------------------------------------------------------
")
	 (setq *user-has-been-warned* t)))
  (cond
   ((am-in-global-situation)
    (make-comment "Ignoring (do-action ~a) in global situation:" action-expr)
    (make-comment "Can only execute actions in local situations"))
   (t (let ( (old-situation (curr-situation))
	     (action (cond (action-expr (km-unique-int action-expr)))) )
	(cond
;	 ((and action (not (isa action '#$Event)))		; NEW! [2]
;	  (report-error 'user-error "KM 1.4.0.51 and later: ***Actions must now be instances of the built-in class Event***~%       I can't do ~a as it is not an instance of Event (or one of Event's subclasses)!~%       Please update your taxonomy!~%" action))
;	 ((get-vals action '#$after-situation :situation *global-situation*)
;	  (report-error 'user-error "You can't do the same action ~a twice! You should create a new action instance instead!~%" action))
	 (t (cond ((not action)
		   (make-comment "Doing null action...")
		   (in-situation (next-situation nil :next-situation next-situation))
		   (prog1
		       (curr-situation)
		     (cond ((not change-to-next-situation) (in-situation old-situation)))))
		  (t (km-trace 'comment "Computing the preconditions and effects of action ~a..." action)
		     (let* ( (semi-evaluated-pcs-list (find-propositions action '#$pcs-list))
			     (semi-evaluated-ncs-list (find-propositions action '#$ncs-list))
					; Result = ((:triple expr expr expr) ... (:triple expr expr expr)).
			     		; For each (:triple <f> <s> <v>), <f>, <s> are evaluated, and <v>
					; is evaluated UNLESS <v> = an existential or constraint expr.
					; This evaluation is done in handling (:triple ...) in interpreter.lisp itself
			     )

		       (cond ((or semi-evaluated-pcs-list semi-evaluated-ncs-list)
			      (km-trace 'comment "Forward propogate relevant facts from previous situation...")	; [1]
			      (mapc #'(lambda (frame+slot)
					(let ( (frame (first frame+slot))
					       (slot (second frame+slot)) )
					  (cond ((comparison-operator slot)
						 (km-int frame))
						(t (km-int `#$(the ,SLOT of ,FRAME))))))
				    (remove-duplicates (mapcar #'(lambda (triple)
								   (list (arg1of triple) (arg2of triple)))
							       (append semi-evaluated-pcs-list semi-evaluated-ncs-list))))))

		       (cond ((or semi-evaluated-ncs-list semi-evaluated-pcs-list)
			      (km-trace 'comment "Preconditions of ~a which must be true in the old situation (~a)..." action old-situation)))
		       (cond ((consistent-to-do-action action semi-evaluated-pcs-list semi-evaluated-ncs-list)
			      (let ( (unsatisfied-pcs (unsatisfied-propositions semi-evaluated-pcs-list)) )
				(cond ((or (null unsatisfied-pcs)
					   (eq test-or-assert-pcs 'assert)
					   (progn (km-format t "(~a ~a):~%Can't do this action because these precondition(s) aren't satisfied:~%~{  ~a~%~}"
							     (cond (change-to-next-situation '#$try-do-and-next)
								   (t '#$try-do)) action
								   (desource+decomment unsatisfied-pcs))
						  (cond (*interactive-preconditions*
							 (eq (ynread "Would you like me to assume these precondition(s) are true (y or n)? ") 'y)))))
				       (mapc #'(lambda (ncs-item) (km-assert ncs-item action :in-list '#$ncs-list)) semi-evaluated-ncs-list)
				       (mapc #'(lambda (pcs-item)
						 (make-comment "Assuming ~a, to do action ~a..." pcs-item action)
						 (km-assert pcs-item action :in-list '#$pcs-list))
					     unsatisfied-pcs)

; [4] PC - This isn't drastic enough: see test-suite/cache.km
;				       (un-done action :slot '#$add-list :situation (curr-situation))	; (in case asserting pcs/ncs has changed them)
;				       (un-done action :slot '#$del-list :situation (curr-situation))
#| Do this instead |#		       (cond ((or semi-evaluated-ncs-list unsatisfied-pcs) (un-done action :situation (curr-situation))))

				       (let* ( (next-situation0 (next-situation action :next-situation next-situation))
#|Now it's okay to have them here, see [4]|#
#|tmp|#					       (add-list (find-propositions action '#$add-list))
#|tmp|#					       (del-list (find-propositions action '#$del-list))
#|tmp|# #|[3]|#				       (evaluated-add-list (mapcar #'evaluate-triple add-list))
#|tmp|#					       (evaluated-del-list (mapcar #'evaluate-triple del-list))
					       (add-blk-list (block-list evaluated-add-list)) )
					 (cond ((or del-list add-blk-list add-list)
						(km-trace 'comment "Now asserting effects of ~a in the new situation (~a)..."
							  action next-situation0)))
					 (in-situation next-situation0)
					 (mapc #'(lambda (del-item) (km-assert del-item action :in-list '#$del-list)) evaluated-del-list)
					 (mapc #'(lambda (blk-item) (km-assert blk-item action :in-list '#$add-list)) add-blk-list)
					 (mapc #'(lambda (add-item) (km-assert add-item action :in-list '#$add-list)) evaluated-add-list)
					 (prog1
					     (curr-situation)
					   (cond ((not change-to-next-situation) (in-situation old-situation))))))))))))))))))))

;;; ----------

;;; (:triple fexpr sexpr vexpr) -> (:triple f s v), or possibly (:triple f s (:set v1 v2))
;;; The *only* point of evaluate-triple is because find-propositions MAY not evaluate <v>, in the
;;; two special cases when <v> = an existential or a constraint expr. See (:triple ...) in KM handlers.
(defun evaluate-triple (triple)
  (cond ((and (pathp (arg3of triple))
	      (not (comparison-operator (arg2of triple))))
	 (km-trace 'comment "Evaluate the individual frame/slot/val paths in~%        ~a..." triple)
	 `(#$:triple ,(km-unique-int (arg1of triple) :fail-mode 'error)
		     ,(km-unique-int (arg2of triple) :fail-mode 'error)
		     ,(vals-to-val (km-int (arg3of triple)))))
	(t triple)))

;;; ----------------------------------------

#|
[1] KM1.4.0-beta17: If slot is single-valued, and (F S OldV) in prev-situation, and (F S V)
    in new situation, then we must also add (OldV InvS (<> F)) otherwise (OldV InvS F) will
    be projected.
ADD LIST:
(F S OldV) = (*TrojanHorse location _Place125)		[later Place125 to be unified with *outside]
(F S V) = (*TrojanHorse location *inside)
location is single-valued.
So need to add: (_Place125 location-of (<> *TrojanHorse)) in the NEW situation. Fine.

But why do this for PCS also??????
|#
(defun block-list (add-list)
  (remove-dup-instances
   (mapcan #'(lambda (proposition)				; [1]
	       (let ( (frame (second proposition))
		      (slot (third proposition))
		      (val (fourth proposition)) )	; necessarily a singleton, if slot is single-valued
		 (cond ((and (single-valued-slotp slot)
			     (not (constraint-exprp val)))
			(cond ((km-setp val)
			       (report-error 'user-error
				     "do-action trying to assert multiple values for single-valued slot!~%Trying to assert ~a for (the ~a of ~a)!~%"
				     (val-to-vals val) slot frame))
			      (t (mapcan #'(lambda (val0)
					     (cond ((kb-objectp val0)
						    `((#$:triple ,val0 ,(invert-slot slot) (<> ,frame))))))
					 (remove val (km-int `#$(the ,SLOT of ,FRAME))))))))))
	   add-list)))

;;; --------------------

;;; PCS-LIST and NCS-LIST are assumed SEMI-EVALUATED, ie. <frame> and <slot> are already evaluated
(defun consistent-to-do-action (action pcs-list ncs-list)
  (let ( (inconsistent-pcs (inconsistent-propositions pcs-list :in-list '#$pcs-list))
	 (inconsistent-ncs (inconsistent-propositions ncs-list :in-list '#$ncs-list)) )
    (cond (inconsistent-pcs
	   (km-format t "(do ~a): Can't do this action as it would be inconsistent to assert precondition(s):~%~{  ~a~%~}"
		      action (desource+decomment inconsistent-pcs))))
    (cond (inconsistent-ncs
	   (km-format t "(do ~a): Can't do this action as it would be inconsistent to assert negated precondition(s):~%~{  ~a~%~}"
		      action (desource+decomment inconsistent-ncs))))
    (and (null inconsistent-pcs)
	 (null inconsistent-ncs))))	; condition for success

(defun inconsistent-propositions (propositions &key in-list)
  (cond (propositions
	 (km-trace 'comment "Checking that the ~a propositions:~%~{  ~a~%~}   are not inconsistent with the current KB..." in-list propositions)
	 (remove-if #'(lambda (proposition) (is-consistent-to-assert proposition :in-list in-list)) propositions))))

(defun is-consistent-to-assert (proposition &key in-list)		; in-list = '#$add or '#$del
  (cond ((km-triplep proposition)
	 (let* ( (frame (second proposition))				; assumes frame and slot are already evaluated
		 (slot  (third proposition))
		 (inv-slot (invert-slot slot))
		 (values (val-to-vals (fourth proposition))) )		; NB don't evaluate - leave it to the later KM
	   (case in-list
		 (#$(pcs-list add-list)
		    (cond ((member slot *inequality-relations*)		; In this case, values will be unevaluated (see handling of :triple in
			   (cond ((null values)				;			interpreter.lisp)
				  (report-error 'user-error "Triple ~a: missing a value to compare against!" proposition))
				 ((not (singletonp values))
				  (report-error 'user-error "Triple ~a: the last element must be a single value for a comparison operation!"
						proposition))
				 ((minimatch frame '#$(the ?x of ?y))
				  (let* ( (x+y (minimatch frame '#$(the ?x of ?y)))
					  (x (first x+y))
					  (y (km-unique-int (second x+y) :fail-mode 'error)) )
				    (km-int `#$(,Y &? (a Thing with
						      (,X ((constraint (not (TheValue ,(INVERT-INEQUALITY-RELATION SLOT) ,(FOURTH PROPOSITION))))))))
					)))
				 (t (km-int `#$(not (,FRAME ,(INVERT-INEQUALITY-RELATION SLOT) ,(FOURTH PROPOSITION)))
					))))	 ; just test it.
			  (t (km-int `#$(,FRAME &? (a Thing with (,SLOT ,VALUES)))))))	 ; inverses installed automatically.
		 (#$(ncs-list del-list) (every #'(lambda (value)
						   (and ; (neq value '*)
						        (km-int `#$(,FRAME &? (a Thing with (,SLOT ((<> ,VALUE))))))
							(cond ((and (kb-objectp value)
								    (kb-objectp slot)
								    (not (non-inverse-recording-slot slot))
								    (not (non-inverse-recording-concept value)))
							       (km-int `#$(,VALUE &? (a Thing with (,INV-SLOT ((<> ,FRAME)))))))
							      (t))))
					       (km-int (fourth proposition))))
		 			       ; values))	OLD
		 (t (report-error 'program-error "Unknown is-consistent-to-assert in-list type `~a'!~%" in-list)))))
	(t (report-error 'user-error "~a contains a non-proposition `~a'!~%Ignoring it...~%" in-list proposition))))

;;; ----------

(defun unsatisfied-propositions (propositions)		; just pcs-list
  (cond (propositions
	 (km-trace 'comment "Checking that propositions:~%~{   ~a~%~}    are satisfied..." propositions)
	 (remove-if #'(lambda (proposition) (km-int `#$(is-true ,PROPOSITION))) propositions))))

;;; --------------------

;;; NOTE: - for pcs-list, ncs-list, the first two elements in the proposition have already been evaluated by KM (by semi-evaluate-triple)
;;;       - for add-list, del-list, the entire proposition has already been evaluated by KM (by evaluate-triple)
;;; We also assume that the check that propositions don't include constraints for ncs-list and del-list
;;; has already been done earlier (by find-propositions)
;;; value can be NIL, or an atom, or a set.
;;; [1] Don't use also-has!!!! also-has can only be safely used if Values are atomic, and as they are potentially unevaluated
;;;	then we must use "has" instead and let the unification system deal with it.
(defun km-assert (proposition action &key in-list)	; in-list = '#$add-list or '#$del-list. action is purely for explanation facility.
  (cond
   ((km-triplep proposition)
    (let* ( (frame (second proposition))
	    (slot  (third proposition))
	    (inv-slot (invert-slot slot))
;	    (values (val-to-vals (fourth proposition))) )
	    (values
	     (cond ((not (member slot *inequality-relations*))	 ; (if slot IS in *inequality-reliations*, then values is NOT used below)
		    (km-int (fourth proposition))))) ; NO!! Need to preserve constraints here!! But we *do* want to evaluate, so the
	    (constraints (extract-constraints
			  (val-to-vals (fourth proposition)))) )	; inverses get installed. We'll ignore this incompleteness for now
      									; (only for pcs-list). New: Let's fold constraints back in. We need to
      									; evaluate values for storage in the explanations.
      (case in-list
	    (#$(pcs-list add-list)
	       (cond
		((member slot *inequality-relations*)
		 (cond ((minimatch frame '#$(the ?x of ?y))
			(let* ( (x+y (minimatch frame '#$(the ?x of ?y)))
				(x (first x+y))
				(y (km-unique-int (second x+y) :fail-mode 'error)) )
			  (km-int `#$(,Y also-has
				      (,X ((constraint (not (TheValue ,(INVERT-INEQUALITY-RELATION SLOT) ,(FOURTH PROPOSITION))))))) :fail-mode 'error)))))
		; ELSE: nothing to assert, but constraint would have already been tested by is-consistent-to-assert
		(t (km-int `#$(,FRAME has (,SLOT ,(APPEND VALUES CONSTRAINTS))) :fail-mode 'error)))	 ; inverses installed automatically.  [1]
	       (mapc #'(lambda (value)
			 (case in-list
			       (#$pcs-list (record-explanation-for `(#$the ,slot #$of ,frame) value `(#$precondition-for ,action)))
			       (#$add-list (record-explanation-for `(#$the ,slot #$of ,frame) value `(#$result-of ,action)))
			       (t (report-error 'program-error "Bad in-list option ~a in km-assert (frame-io.lisp)!" in-list))))
		     values))
	    (#$(ncs-list del-list) (mapc #'(lambda (value)
					     (km-int `#$(,FRAME also-has (,SLOT ((<> ,VALUE)))) :fail-mode 'error)
					     (cond ((and (kb-objectp value)
							 (kb-objectp slot)
							 (not (non-inverse-recording-slot slot))
							 (not (non-inverse-recording-concept value)))
						    (km-int `#$(,VALUE also-has (,INV-SLOT ((<> ,FRAME)))) :fail-mode 'error))))
					 values))
;					 (km-int (fourth proposition))))
	    (t (report-error 'program-error "Unknown km-assert in-list type `~a'!~%" in-list)))))
   (t (report-error 'user-error "~a contains a non-proposition `~a'!~%Ignoring it...~%" in-list proposition))))

;;; Convert (a Triple with ...) to :triple notation.
;;; slot is expected to be one of: #$(pcs-list ncs-list add-list del-list)
;;; RETURNS a list of KM triples (:triple expr expr expr)
;;; For each (:triple <f> <s> <v>), <f>, <s> are evaluated, and <v>
;;; is evaluated UNLESS <v> = an existential or constraint expr.
;;; This evaluation is done in handling (:triple ...) in interpreter.lisp itself
(defun find-propositions (action slot)
  (remove nil
   (mapcar #'(lambda (triple)
;	       (km-format t "triple = ~a...~%" triple)
	       (cond ((km-triplep triple)
		      (cond ((and (member slot '#$(ncs-list del-list))
				  (constraint-exprp (fourth triple)))
			     (report-error 'user-error "~a found in (the ~a of ~a)~%   You can't include constraints in the triples of a ~a!"
					   triple slot action slot)
			     nil)
			    (t triple)))
		     (t (report-error 'user-error "Non-triple ~a found in (the ~a of ~a)" triple slot action)
			nil)))
	   (km-int `#$(the ,SLOT of ,ACTION)))))

#|
(defun convert-to-triple (triple)
  (cond ((km-triplep triple) triple)
	((isa triple '#$Triple)
	 (list '#$:triple
	       (km-unique-int `#$(the frame of ,TRIPLE) :fail-mode 'error)
	       (km-unique-int `#$(the  slot of ,TRIPLE) :fail-mode 'error)
	       (vals-to-val (km-int `#$(the value of ,TRIPLE)))))
	(t (report-error 'user-error "Non-triple ~s found in add-list or del-list of an action!~%" triple))))
|#

;;; ======================================================================
;;;		KM's THEORY MECHANISM
;;; ======================================================================

;;; In header.lisp
;;; (defvar *visible-theories* nil)

;;; Note *DOESN'T* include *global-situation*
(defun visible-theories () *visible-theories*)

(defun hide-theory (theory)
  (cond ((and (not (isa-theory theory))
	      (not (instance-of theory '#$Situation)))
	 (report-error 'user-error "(hide-theory ~a): ~a is not a theory!" theory theory))
	((not (member theory *visible-theories*))
	 (km-trace 'comment "[(hide-theory ~a): ~a is already hidden]" theory theory))
	(t (reset-done)			; note, answers may change when a theory becomes hidden
	   (km-setq '*visible-theories* (remove theory *visible-theories*)))))

(defun see-theory (theory)
  (cond ((and (not (isa-theory theory))
	      (not (instance-of theory '#$Situation)))
	 (report-error 'user-error "(see-theory ~a): ~a is not a theory!" theory theory))
	((member theory *visible-theories*)
	 (km-trace 'comment "[(see-theory ~a): ~a is already visible]" theory theory))
	(t (reset-done)		; note, answers may change when a theory becomes visible
	   (km-setq '*visible-theories* (cons theory *visible-theories*)))))

;;; Absolutely all theories
;;; Optimized and to avoid looping. This won't allow a Theory class hierarchy though.
(defun all-theories () (get-vals '#$Theory '#$instances :situation *global-situation*))

(defun isa-theory (theory) (member theory (all-theories)))

(defun am-in-local-theory () (and (neq (curr-situation) *global-situation*) (isa-theory (curr-situation))))

(defun in-theory (theory-expr &optional km-expr)
  (in-situation theory-expr km-expr t))					; theoryp = t

(defun all-situations-and-theories () (append (all-situations) (all-theories)))

#|
======================================================================
			DELETING FRAMES
======================================================================

Note that delete-frame will *ALSO* remove the bindings for it.
So if X is bound to Y, is bound to Z (X -> Y -> Z), and we delete frame Y,
then we also delete the binding that Y -> Z, and thus X is left hanging
(pointing to invisible Y). Thus must be very careful when deleting a single frame!
NEW: Only allow deletion of known (valid) frames, to avoid this problem.
NOTE: Suppose X -> Y and we delete Y: We better be sure that no X's are lying around in memory.
I *think* we are ok though: Consider:
	(Foo has (r (X)))
	(X has (invr (Foo)))	; [1]
	(Y == X)		; thus there's a binding X -> Y, and KM will have rebuild [1] as:
	(Y has (invr (Foo)))
Now (delete-frame Y) will trigger (uninstall-inverses Y invr (Foo)).
And as uninstall-inverses does a get-vals on Foo, *including a dereference*, X will be dereferenced.
For this reason we have to delete the inverses BEFORE deleting the frame itself.

What about this, though:
	(Foo has (r ((_X & _X2))))  ; [2] no inverses in this case
	(_Y == _X)	  	    ; thus there's a binding X -> Y, and KM will have rebuild [1] as:
	(delete-frame _Y)
Unfortunately [2] leaves a spurious concept _X lying around in [2], pointing to non-existent _Y. [2] becomes:
	(Foo has (r ((_Y & _X2))))
In fact, we get away with this because _Y is a null frame, i.e., is equivalent to NIL. Thus
(_Y & _X2) = (NIL & _X2) = _X2, so we are okay.
If we now recreate a new _Y, though, we'd now have problems as the pointer to the old Y is lying around.
The safest way would be to rebind _X to nil, done at the end.

NOTE: We *will* be in trouble if the user then attempts to re-use the Skolem name.
So do a (dereference-kb) to clean up the old junk.
|#
(defun delete-frame (frame0 &key (delete-inversesp t) unintern)
  (let ((frame (dereference frame0)))
  (cond ((known-frame frame)
	 ;;; Delete definition pointers
	 (cond (*are-some-definitions*
		(let ((own-definition-parents (get-vals frame '#$instance-of :facet 'own-definition))
		      (member-definition-parents (get-vals frame '#$instance-of :facet 'member-definition)))
		  (cond (own-definition-parents
			 (unpoint-parents-to-defined-concept frame own-definition-parents 'own-definition)))
		  (cond (member-definition-parents
			 (unpoint-parents-to-defined-concept frame member-definition-parents 'member-definition))))))
 	 ;;; Delete inverse links
	 (cond (delete-inversesp
		(mapc #'(lambda (situation)
			  (mapc #'(lambda (facet)
				    (mapc #'(lambda (slotvals)
					      (let ((slot (slot-in slotvals))
						    (vals (vals-in slotvals)))
						(uninstall-inverses frame slot vals situation)))
					  (get-slotsvals frame :situation situation :facet facet)))
				(cond (*are-some-definitions* '(own-properties own-definition))
				      (t '(own-properties)))))
		      (all-situations-and-theories))))
	 ;;; Delete from the object stack
	 (remove-from-stack frame)
	 ;;; Delete frame itself
	 (delete-frame-structure frame :unintern unintern) ; maybe other legacy references to frame, or to instances bound to frame
	 (cond ((not unintern) (push frame *deleted-frames*))) ; keep a note of these. dereference-kb will clean these up.
		; NOTE: if :unintern = t, then we are assuming there is no other reference to frame in the KB so we don't need to keep note of it
	 t)
	(t (report-error 'user-error "(delete-frame ~a): ~a is not a known frame.~%" frame frame)))))

(defun delete-slot (frame0 slot &key (delete-inversesp t) (situation (target-situation (curr-situation) frame0 slot)))
  (let ((frame (dereference frame0)))
  (cond ((known-frame frame)
 	 ;;; Delete inverse links
	 (cond (delete-inversesp
		(let* ((vals0 (get-vals frame slot :situation situation))
		       (vals (cond ((single-valued-slotp slot) (un-andify vals0)) ; ((a & b)) -> (a b)
				   (t vals0))))
		  (uninstall-inverses frame slot vals situation)))) ; includes explanations
	 (put-vals frame slot nil :situation situation) ; delete the vals
	 (delete-explanation frame slot '* :explanation-to-delete 'all :situation situation)
	 t)
	(t (report-error 'user-error "(delete-frame ~a): ~a is not a known frame.~%" frame frame)))))

;;; No taxonomic information.
(defun orphans () (remove-if-not #'orphanp (get-all-concepts)))

(defun scan-kb ()
  (let* ( (declared-symbols (get-all-concepts))
	  (all-objects (flatten-to-kb-objs (mapcar #'(lambda (situation)
					  (mapcar #'(lambda (concept)
						      (mapcar #'(lambda (facet)
								  (get-slotsvals concept :facet facet :situation situation))
							      *all-facets*))
						  declared-symbols))
				      (all-situations-and-theories))))
	  (all-symbols (remove-duplicates (remove-if-not #'kb-objectp all-objects)))
	  (user-symbols (set-difference all-symbols (append *built-in-frames*
							    *km-lisp-exprs*
							    *downcase-km-lisp-exprs*
							    *reserved-keywords*
							    *additional-keywords*)))
	 (undeclared-symbols (remove-if #'(lambda (symbol)
					    (or (member symbol declared-symbols)
						(assoc symbol *user-defined-infix-operators*) ; elements are (<sym> <fn>)
						(comment-tagp symbol)
						(dotted-slot symbol)	; e.g., |agent...|, used in explain
						(km-varp symbol)
						(member (invert-slot symbol) declared-symbols)))
					user-symbols))
	 (missing-classes (remove-if #'(lambda (symbol)
					 (or (get-vals symbol '#$instance-of)
					     (get-vals symbol '#$superclasses)
					     (member symbol *built-in-frames*)))
				     declared-symbols)))
    (cond (undeclared-symbols
	   (km-format t "A cursory check of the KB shows (at least) these symbols were undeclared:~%" (length undeclared-symbols))
	   (mapc #'(lambda (symbol) (km-format t "   ~a~%" symbol))
		 (sort (copy-list undeclared-symbols) #'string< :key #'symbol-name))
	   (format t "----- end -----~%")))
    (cond (missing-classes
	   (km-format t "The following ~a symbols have no instance-of or superclasses defined for them:~%"
		      (length missing-classes))
	   (mapc #'(lambda (symbol) (km-format t "   ~a~%" symbol))
		 (sort (copy-list missing-classes) #'string< :key #'symbol-name))
	   (format t "----- end -----~%")))
    '#$(t)))

;;; This removes quoted parts, e.g., (flatten-to-kb-objs '(a b (quote c) d)) -> (a b d)
;;; Note (flatten-to-kb-objs 'a) -> (a);
;;; apairs become normal pairs  (flatten-to-kb-objs '(a b c . d)) -> '(a b c d)
(defun flatten-to-kb-objs (expr)
  (cond
   ((not (listp expr)) (list expr))
   ((null expr) nil)
   ((apairp (last expr)) `(,@(flatten-to-kb-objs (butlast expr)) ,(first (last expr)) ,(rest (last expr))))
   ((member (first expr) '(quote function lambda)) nil) ; #'(lambda (x) ...)= (function (lambda (x) ...))
   (t (my-mapcan #'flatten-to-kb-objs expr))))

;;; ======================================================================
;;;		SITUATIONS MODE
;;; ======================================================================

(defvar *am-in-situations-mode* nil)

(defun set-situations-mode ()
  (or *am-in-situations-mode*
      (progn (make-comment "Switching on situations mode for this KB")
	     (km-setq '*am-in-situations-mode* t))))

(defun am-in-situations-mode () *am-in-situations-mode*)

#|
Under these special circumstances, DON'T compute the value of a slot
Specifically: You're in the global situation, but the slot is a fluent (so can only take on situation-specific values).
   Also you are working with situations mode on (*am-in-situations-mode*=t). If that was nil, then everything's in global and
   the fluent-status is irrelevant.
|#
(defun ignore-slot-due-to-situations-mode (slot)
  (and *am-in-situations-mode*
       (am-in-global-situation)
       (not (am-in-prototype-mode))
       (fluentp slot)))

;;; returns t and print error if there's a violation
(defun check-situations-mode (instance slot)
  (cond ((ignore-slot-due-to-situations-mode slot)
	 (report-error 'user-error "Attempt to call (the ~a of ~a) in the global situation!
(Not allowed, as `~a' is a fluent and you're using KM's situation mechanism).
DEBUGGING HINTS:
 * IF you issued your query for the `~a' slot from the global situation
   THEN you shouldn't do this! You should only issue queries for a fluent slot from
        within a situation, not from the global KB.
   SOLUTIONS:
     (i) Enter a situation by
		KM> (new-situation)
	 then reissue your query, or
    (ii) Declare the `~a' slot as a non-fluent (i.e. with time-independent values), by
	        KM> (~a has (fluent-status (*Non-Fluent)))~%
 * IF you issued your query from within a local situation
   THEN You may have a non-fluent slot depending on the value of a fluent slot (= bad!)
        and KM is trying to compute that non-fluent slot's values in the global situation.
   TO LOCATE THIS: Type `g' to see the goal hierarchy, and look for a
		   non-fluent slot's value being computed from a fluent's value.
   TO FIX THIS: Change the non-fluent to be a *Fluent/*Inertial-Fluent, or edit the
		   dependency.~%" slot instance slot slot slot slot)
	t)))

; old error message
;	 (report-error 'user-error "Attempt to call (the ~a of ~a) in the global situation!
;As you are currently using KM's situations mechanism in your KB, you should only issue queries
;for a fluent slot (here `~a') from within a situation, not from the global KB.
; - To enter a situation, type (new-situation), or
; - To declare the `~a' slot as a non-fluent (i.e. with time-independent values), enter
;       (~a has (fluent-status (*Non-Fluent)))~%" slot instance slot slot slot)


;;; ======================================================================
;;;		NOWEXISTENCE - experimental
;;; ======================================================================

(defun nowexists (frame)
  (cond ((not (kb-objectp frame)) t)
	((not (am-in-local-situation)) t)
	(t (neq (nowexists-val frame) '#$f))))

(defun nowexists-val (frame &key (situation (curr-situation)))
  (cond ((get-unique-val frame '#$nowexists :situation situation))
	(t (let ((prev-situation (prev-situation situation frame)))
	     (cond (prev-situation (nowexists-val frame :situation prev-situation))
		   (t (let ((inherited-rule-sets (inherited-rule-sets frame '#$nowexists)))
			(some #'(lambda (inherited-rule-set)
				  (some #'(lambda (rule)
					    (cond ((equal rule '#$(:default t)) '#$t)
						  ((equal rule '#$(:default f)) '#$f)
						  (t (report-error 'user-error
								   "Illegal inherited expression on nowexists slot for ~a (Only allowed values are (:default t) or (:default f)~%" frame))))
					inherited-rule-set))
			      inherited-rule-sets))))))))

