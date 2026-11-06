
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: header.lisp
;;; Purpose: Set some compilation flags etc.

;;; Suggestion from Francis Leboutte for improving KM's speed
;;; NOTE: This is left commented, as some users have requested to not
;;; have this optimization (with subsequent tradeoffs) imposed on them.
;;; Uncomment this for a tiny bit more speed, but at loss of some tracing
;;; info etc.
;;; (eval-when (:compile-toplevel)
;;;   (proclaim '(optimize (speed 3) (safety 1) (space 0) (debug 0))))

#|
======================================================================
		THE KM PACKAGE
======================================================================
KM is released with two versions
   (i) without an explicit package definition ([1] below commented out).
       KM will be in which ever package it is loaded into.
  (ii) with an explicit package definition ([1] below uncommented). KM will
       always be in this package.

The variable *km-package* is set to the KM package name that KM is in.
|#

;;; From Tim Menzies: Suppress style warnings under SBCL (Mac and Linux)
#+SBCL (DECLAIM (SB-EXT:MUFFLE-CONDITIONS CL:STYLE-WARNING))

;;; COMMENT THIS OUT FOR THE PACKAGED VERSION OF KM
; (defvar *using-km-package* nil)

;;; [1] UNCOMMENT THIS FOR PACKAGED VERSION OF KM
(eval-when
 (:compile-toplevel :load-toplevel :execute)
 (unless (find-package :km) (make-package :km :use '(:common-lisp))))
(in-package :km)
(defvar *using-km-package* nil)
(setq *using-km-package* t)	; flag used by fastsave-kb

;;; KM defines neq (in utils.lisp), except for Mac CommonLisp where it's
;;; a built-in. However, in MCL it's in the ccl not cl package, and so with
;;; KM's packaged version we need to explicitly import it to KM, in addition
;;; to the normal importing via :use '(:common-lisp) above
#+MCL
(eval-when (:compile-toplevel :load-toplevel :execute)
   (import 'ccl:neq))


;;; KM package is now the current package
(eval-when
 (:compile-toplevel :load-toplevel :execute)
 (defconstant *km-package* *package*))

;;; Define and switch to *km-readtable* a copy of *readtable* which (normally)
;;; points to the built-in, read-only system readtable.
;;; The purpose of this is that *km-readtable* can then be modified for the
;;; #$ macro, while (in some Lisps) the build-in system read-table cannot be.
(eval-when (:execute :load-toplevel :compile-toplevel)
   (defvar  *ACL-readtable* *readtable*)  ;; just to save a pointer to ACL's readtable
   (defvar *km-readtable* (copy-readtable *readtable*))
     #-allegro (setq *readtable* *km-readtable*)
     #+allegro (setf (excl:named-readtable :km) *km-readtable*) ;smh 2012-06-19
     )

;;; ======================================================================

;;; Personal preference
;(setq *print-case* :downcase)

;;; Dispatch mechanism not "compiled" be default, unless
;;; compiled-handlers.lisp is included.
(defparameter *compile-handlers* nil)

;;; ======================================================================
;;;		DECLARATION OF CONSTANTS
;;; ======================================================================

;;; This is really a constant, but I *really* don't want to put the definition
;;; here! It's setq'ed in interpreter.lisp.
(defparameter *km-handler-alist1* nil)
(defparameter *km-handler-alist2* nil)
(defparameter *km-handler-alist* nil)

(defconstant *var-marker-char* #\_)
(defparameter *var-marker-string* "_")
(defparameter *proto-marker-string* (concatenate 'string *var-marker-string* "Proto"))		; ie. "_Proto"
(defparameter *fluent-instance-marker-string* (concatenate 'string *var-marker-string* "Some"))	; ie. "_Some"
(defparameter *km-version-str* "2.5.45")
(defparameter *year* "2015")
(defparameter *newline-str* (make-string 1 :initial-element '#\Newline))

(defparameter *km-handler-function* nil) ; used in compiler.lisp

; (defconstant *global-situation* '|*Global|)
; Correction to allow compilation in CLisp (Thanks to Francis Leboutte).
(eval-when (:compile-toplevel :load-toplevel :execute)
   (defconstant *global-situation* '|*Global|))

;;; ------------------------------


; from prototypes.lisp
(defparameter *slots-not-to-clone-for* 	; Intent is defconstant, but SBCL doesn't like defconstants on lists
  '(|prototype-participant-of| |prototype-participants|
       |prototypes| |prototype-of| |instance-of| |cloned-from| |has-clones| |clone-built-from| |has-built-clones|))

;;; --------------------
;;; Optimization flags: note which bits of machinery are in use.
;;; --------------------

(defparameter *classes-using-assertions-slot* nil)
(defparameter *are-some-definitions* nil)
(defparameter *are-some-prototype-definitions* nil)
(defparameter *are-some-prototypes* nil)
(defparameter *are-some-subslots* nil)
(defparameter *are-some-constraints* nil)
(defparameter *are-some-tags* nil)
(defparameter *are-some-defaults* nil)
(defparameter *deleted-frames* nil)

;;; ======================================================================
;;;		KM'S PARAMETERS
;;; ======================================================================

;;; The following are user-tunable, controlling KM's behavior
;;; Most of these should never need to be changed by the user. The commented ones would
;;; never be changed by the user, and are really internal.
(defparameter *km-behavior-parameters*
  '(*recursive-classification*		; default t
    *indirect-classification*		; default t
    *recursive-prototypes*		; default nil
    *eagerly-unify-prototypes* 		; default t
    *sanity-checks*			; default t
    *slot-checking-enabled*		; default nil
    *logging*				; default nil
    *max-padding-instances*		; default 0
    *tolerance*				; default 0.001
    *output-precision*			; default 3
    *instance-of-is-fluent*		; default nil
    *km-depth-limit*			; default nil
    *linear-paths*			; default nil
    *project-cached-values-only*	; default nil
    *record-explanations-for-clones*    ; default nil
    *coerce-undeclared-slots*		; default nil
    *record-explanations*		; default t
    *record-sources*			; default t
    *add-comments-to-names*		; t - print _Car3 as: _Car3 #|"a Car&Dog"|#
    *check-kb*				; default nil
    *classify-slotless-instances*	; default t
    *built-in-remove-subsumers-slots*	; #$(instance-of classes superclasses member-type) (is changed in AURA appn)
    *built-in-remove-subsumees-slots*	; #$(subclasses prototype-of domain range) 	 (is changed in AURA appn)
    *default-fluent-status*		; #$*Fluent
    *active-obj-stack*			; nil
    *on-error*				; default = debug
    ;;; Formatting of justifications
    *justify-leaves*			; nil = by default, DON'T explain things that DON'T have comment tags
    *start-justifications-with-because* ; default t. If t, start justification text with "The s of f = v because:".
    ;;; Classification control
    *classification-enabled*
    *prototype-classification-enabled*
    *use-inheritance*
    *use-prototypes*
    *developer-mode*
    *unclonable-slots*			; may be extended (e.g., in AURA)
    *called-forces-unification*		; default t
    ))

(defparameter *recursive-classification* t)
(defparameter *indirect-classification* t)
(defparameter *recursive-prototypes* nil)
(defparameter *eagerly-unify-prototypes* t)
(defparameter *sanity-checks* nil)	; see constraints.lisp to toggle these on and off
(defparameter *slot-checking-enabled* nil)
(defparameter *logging* nil)
(defparameter *max-padding-instances* 0) ; [1]
(defparameter *tolerance* 0.0001)	; within this means the two numbers are the same
(defparameter *output-precision* 3)	; for make-sentence
(defparameter *instance-of-is-fluent* nil)
(defparameter *km-depth-limit* nil)	; nil = no limit
(defparameter *linear-paths* nil)	; DON'T recognize linear paths any more
(defparameter *project-cached-values-only* nil)
(defparameter *record-explanations-for-clones* t)	; change
(defparameter *coerce-undeclared-slots* nil) ; if t and slot isn't declared, assert it as (instance-of (Slot))
(defvar *record-explanations* t)    ; Allow users to turn this off (to save memory)
(defparameter *record-sources* t)	; Allow users to turn this off (to save memory)
(defparameter *add-comments-to-names* t) ; print _Car3 as: _Car3 #|"a Car&Dog"|#
(defvar *check-kb* nil)
; (defvar *classify-slotless-instances* t) - in frame-io.lisp
; (defparameter *built-in-remove-subsumers-slots* '#$(instance-of classes superclasses member-type)) - in frame-io.lisp
; (defparameter *built-in-remove-subsumees-slots* '#$(subclasses prototype-of domain range)) - in frame-io.lisp

; In frame-io.lisp
;(defconstant *default-default-fluent-status* '#$*Fluent) ; neah, don't change this!
;(defparameter *default-fluent-status* *default-default-fluent-status*)	; user can change this
(defparameter *active-obj-stack* nil)
(defparameter *called-forces-unification* t)

;;; ----------------------------------------------------------------------

;;; [1] above: For (at-least n Class) and (exactly n Class) constraints. KM will generate missing
;;; instances of Class if there are less than n on a slot, unless n > *max-padding-instances*.
;;; Setting *max-padding-instances* to 0 thus disables this feature.

(defconstant *classify-in-local-situations* t)    ; should never need to change

;;; ----------------------------------------

;;; The following are run-time state variables, computed automatically by KM
;;; during KB load and KB execution, which the user doesn't need to set.
;;; These are the variables that need to be preserved to restore the KM state.
(defparameter *km-state-parameters*
    '(*km-gensym-counter*
;      *clone-operation-id-counter*
    *visible-theories*
;   *obj-stack*			neah, this doesn't need to be saved.
    *curr-prototype*
    *curr-situation*
    *classes-using-assertions-slot*
    *are-some-definitions*
    *are-some-prototype-definitions*
    *are-some-prototypes*
    *are-some-subslots*
    *are-some-constraints*
    *are-some-tags*
    *are-some-defaults*
    *am-in-situations-mode*
;    *abort-on-error-report*
;    *error-report-silent*
;   *user-defined-infix-operators*	- these don't write out properly so ignore these
    ))

;;; These are internal during system development and are now fixed. They are parameters created
;;; during system development to allow easy switching off of new features if they break something.
(defparameter *km-fixed-parameters*
    '(*add-cloned-from-links*		; t
      *propogate-explanations-to-clones* ; t
;      *prototype-bookkeeping-slots*
      *installing-inverses-enabled*
      *less-aggressive-constraint-checking*
      *overriding-in-prototypes*
;     *clones-are-global*
      *force-with-cloned-from*		; take cloned-from as a tagging slot
      *classify-in-local-situations*
      ))

;;; Additional query-specific parameters. These change *during* reasoning.
(defparameter *km-runtime-variables*
    '(*trace*
      *depth*
      *internal-logging*
      *am-classifying*
      *looping*
      *spypoints*
      *profiling*
      *print-explanations*
      *show-comments*
      *deleted-frames*
      *partially-included-prototype*
      *deferred-unifications*
      *instances-being-unified*
      *failed-unification-attempts*
      ))

;;; --------------------

(defvar *curr-prototype* nil)		; For prototype mode
; (defvar *unifying-in-prototype* nil)	; New flag, so lazy-unify-vals knows when a prototype is being merged in
(defparameter *show-comments* t)	; for tracing
(defparameter *use-inheritance* t)	; Applied in get-slotvals.lisp

(defparameter *use-prototypes* t)	; Applied in get-slotvals.lisp
(defparameter *use-no-inheritance-flag* nil)	; for Shaken
(defvar *trace* nil)			; Tracer is on/off
(defvar *depth* 0)			; Tracing depth
(defvar *internal-logging* nil)		; for internal backtracking
(defvar *am-classifying* nil)		; Don't classify while classifying
(defvar *dereferencing-on* t)		; Allows dereferencing to be turned off when not needed, e.g., cloning
(defvar *partially-included-prototype* nil)
(defvar *deferred-unifications* nil)
(defvar *instances-being-unified* nil)
(defvar *failed-unification-attempts* nil)

; (defvar *backtrack-after-testing-unification* nil)   ; Obsolete parameter (always nil), but I'll leave the code there

;;; New mechanism
(defvar *visible-theories* nil)
;(defvar *clone-operation-id-counter* 0)

(defparameter *special-symbol-alist*
  '( (quote "'")
     (function "#'")
     (unquote "#,")
     (unquote-splice "#@")
     (#+allegro excl::backquote #-allegro backquote "`")
     (#+allegro excl::bq-comma #-allegro bq-comma ",")			; I'm not sure of the non-Allegro implementation
     (#+allegro excl::bq-comma-atsign #-allegro bq-comma-atsign ",@") ))

;;; when t, exposes the source info on frame data structures (for debugging purposes)
(defparameter *developer-mode* nil)

;;; ----------------------------------------

;;; encapsulate checking flag
; (defvar *check-kb* nil) - put earlier
(defun checkkbon ()  (km-setq '*check-kb* t))
(defun checkkboff () (km-setq '*check-kb* nil))
(defun checkkbp () *check-kb*)

;;; ======================================================================
;;;		STATISTICS COUNTERS
;;; ======================================================================

(defvar *statistics-classification-inferences* 0)
(defvar *statistics-query-directed-inferences* 0)
(defvar *statistics-kb-access* 0)
(defvar *statistics-cpu-time* (get-internal-run-time))
(defvar *statistics-skolems* 0)
(defvar *statistics-max-depth* 0)
(defvar *statistics-unifications* 0)
(defvar *statistics-classifications-attempted* 0)
(defvar *statistics-classifications-succeeded* 0)

(defparameter *user-defined-infix-operators* nil)

;;; Experiment with making them local - doesn't work so well though
; (defparameter *clones-are-global* t)
; 7/24/08: NEW: No equate *clones-are-global* with *am-in-situations-mode*

;;; Used in get-slotvals.lisp and explain.lisp
(defparameter *subslot-comment-tag* '|[subslot-reasoning]|)

