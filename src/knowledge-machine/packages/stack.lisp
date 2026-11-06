
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: stack.lisp
;;; Author: Peter Clark
;;; Date: 1994
;;; Purpose: Maintenance of the stack

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defvar *obj-stack* ())	; all objects created/touched during reasoning
(defvar *goal-stack* ())		; goal stack
(defvar *silent-spypoints-stack* ())    ; spying certain KM expressions (Jason Chaw)

;;; ----------

(defun clear-silent-spypoints-stack () (setq *silent-spypoints-stack* nil))
(defun silent-spypoints-stack () *silent-spypoints-stack*)

;;; ----------

;;; synonym
(defun new-context ()
;  (km-setq '*all-active-situations* nil)		; New!
  (clear-obj-stack))

(defun clear-goal-stack () (setq *goal-stack* nil))
(defun goal-stack () *goal-stack*)
(defun top-level-goal () (first (last-el *goal-stack*)))

#|
(defun push-to-goal-stack (expr &key target)
  (let ((item-to-stack (item-to-stack (desource+decomment expr) :target target)))
    (push item-to-stack *goal-stack*)))

(defun pop-from-goal-stack ()
  (pop *goal-stack*))
|#

;;; [1] Tiny bit slower, but allows spotting looping earlier (net loss timewise, gain inference wise)
;;; ALSO: See looping-on later

(defun push-to-goal-stack (expr &key target)
  (let* ((item-to-stack (item-to-stack (desource+decomment expr) :target target))
	 (original-expr (third item-to-stack)))
    (cond ((and ; nil		- UNCOMMENT this (only) to switch off the entire *deferred-unifications* mechanism
		(listp original-expr)
		(= (length original-expr) 3)
		(full-equality-assertion-operator (second original-expr)))
	   (let* ((instance1 (first original-expr))
		  (instance2 (third original-expr)))
; Strictly should be OR	not AND, but we end up with infinite loops otherwise :-( HLO-4583
;	     (cond ((kb-objectp instance1) (pushnew instance1 *instances-being-unified*)))
;	     (cond ((kb-objectp instance2) (pushnew instance2 *instances-being-unified*))))))
	     (cond ((and (kb-objectp instance1)
			 (kb-objectp instance2))
		    (pushnew instance2 *instances-being-unified*)
		    (pushnew instance1 *instances-being-unified*))))))
    (push item-to-stack *goal-stack*)))
;  (setq *goal-stack* (cons (item-to-stack (desource+decomment expr) :target target) *goal-stack*)))	; [1]

(defun pop-from-goal-stack ()
  (let* ((item-from-stack (pop *goal-stack*))
	 (original-expr (third item-from-stack)))
    (cond ((and *instances-being-unified*
		(listp original-expr)
		(= (length original-expr) 3)
		(full-equality-assertion-operator (second original-expr)))
	   (let* ((instance1 (first original-expr))
		  (instance2 (third original-expr)))
	     (cond ((and (kb-objectp instance1) (member instance1 *instances-being-unified*))
		    (setq *instances-being-unified* (remove instance1 *instances-being-unified*))))
	     (cond ((and (kb-objectp instance2) (member instance2 *instances-being-unified*))
		    (setq *instances-being-unified* (remove instance2 *instances-being-unified*)))))))
    item-from-stack))

;  (prog1
;      (first *goal-stack*)
;    (setq *goal-stack* (rest *goal-stack*))))

;;; ======================================================================
;;; 		THE EXPRESSION STACK
;;; ======================================================================

#|
Looping problem with disjuncts!!! I failed to fix this
  Suppose we ask X, and X <- Y or Z, and Y <- X.
  KM will give up on Y, even if Z can compute it. This is a problem, because then
  Y might be projected from the previous situation!

The problem is that KM's triggers too easily. If, when calculating X, I hit a
non-deterministic choice-point and take branch 1 of 2 (say), then hit a call to
calculate X again, KM *should* continue, but this time take branch 2 of 2 at the
same choice-point. Instead, KM just gives up. A fix would be to (i) identify
non-deterministic choice-points (ii) mark them in the stack and (iii) steer as above.

We can do this with a REVISED LOOPING CHECK:
IF  the current call C' matches an earlier call C
THEN abort
UNLESS there is an "or" clause between C and C'.

#$or clauses: Select an option which ISN'T in the current stack (see interpreter.lisp).
|#

;;; [1] Tiny bit slower, but allows spotting looping earlier (net loss timewise, gain inference wise)
;;; ALSO: See push-to-goal-stack, earlier
(defun looping-on (expr) (on-goal-stackp (desource+decomment expr))) ; [1]

#|
(pending-equality x y) - Returns t if x and y WILL be unified, so that deeper in the
stack we can assume they are equal, even though the equality has not yet been asserted.

KM: (show-goal-stack)
 CURRENT GOAL STACK IS AS FOLLOWS:
 -> (the has-part* of (a DNA))                      [called in _Situation10940]
   ;;;
       -> (unify-with-clone-of _Nucleic-Acid82) [called in _Situation10940]
        -> (_DNA-strand15400 &! _Nucleic-Acid15425) [called in |all situations|]

KM: (pending-equality '#$_DNA-strand15400 '#$_Nucleic-Acid15425)
t
|#
(defun pending-equality (x0 y0)
  (let ((x (dereference x0))
	(y (dereference y0)))
    (some #'(lambda (item)
	      (let ((original-expr (third item)))
		(or (pending-equality-expr original-expr x y)		; (x &! y)
		    (and (km-setp original-expr)			; (:set a b (x &! y) (w &! v))
			 (some #'(lambda (subexpr)
				   (pending-equality-expr subexpr x y))
			       original-expr)))))
  (goal-stack))))

(defun pending-equality-expr (original-expr x y)
  (and (listp original-expr)
       (= (length original-expr) 3)
       (equality-assertion-operator (second original-expr))
       (or (and (eq x (dereference (first original-expr))) (eq y (dereference (third original-expr))))
	   (and (eq y (dereference (first original-expr))) (eq x (dereference (third original-expr)))))))

;;; ------------------------------

(defun on-goal-stackp (expr)
; (km-format t "on-goal-stackp: expr = ~a. Stack =~%~{   ~a~%~}" expr *goal-stack*)
  (member (item-to-stack expr) *goal-stack* :test #'stack-equal))		; more efficient

;;; Note: non-canonicalized expressions (element 3 of itemN) are NOT compared
;;; NEW: ***NOT** symmetrical now: item1 is a NEW item, item2 is an item on the existing goal stack.
(defun stack-equal (item1 item2)
  (let ((canonical1 (dereference (first item1)))
	(canonical2 (dereference (first item2))))
  (and (or (equal canonical1 canonical2)		; match canonicalized expressions
;	   (equal (first item1) (first item2))		; [1]
	   (and (listp canonical1)
		(listp canonical2)
		(eq (second canonical1) '#$set-unified-with) ; Doing ((x) &&! (y)) for (x &! y)
		(eq (second canonical2) '#$unified-with)
		(or (and (equal (first canonical1) (list (first canonical2)))  ; (x) equals (list x)
			 (equal (third canonical1) (list (third canonical2)))) ; (y) equals (list y)
		    (and (equal (first canonical1) (list (third canonical2)))  ; Reverse: Doing ((y) &&! (x)) for (x &! y)
			 (equal (third canonical1) (list (first canonical2)))) ;
		)))
       (eql (second item1) (second item2))))) ; match situation

;(defun stack-equal (item1 item2)
;  (and (equal (first item1) (first item2))		; match canonicalized expressions
;       (eql (second item1) (second item2))))		; match situation

#|
Here we canonicalize the item for stacking.

Must add a note of the current situation.
[1] for &, the canonical form *isn't* situation-dependent as we unify in all situations,
    hence returns 2nd element = *global-situation* rather than (curr-situation)
|#
(defun item-to-stack (expr &key target)
;  (declare (ignore target))		; neah, not that helpful
  `(,(km-canonicalize expr)
    ,(cond ((and (listp expr) (unification-operator (second expr))) '|all situations|)  ; better - trace is confusing otherwise!
	   (t (curr-situation)))
    ,expr
    ,(inference-number)
    ,target
    ))

;;; The three parts of an item on the stack
(defun stacked-canonical-expr (stacked-item) (first stacked-item))
(defun stacked-situation (stacked-item) (second stacked-item))
(defun stacked-expr (stacked-item) (third stacked-item))
(defun stacked-inference-number (stacked-item) (fourth stacked-item))
(defun stacked-target (stacked-item) (fifth stacked-item))

;;; [2] Must canonicalize the two forms of paths:
;;;	(_Car23 parts) -> stack as (the parts of _Car23)
;;; [3] Make (a & b), (b & a) into a canonical form. Strictly we should also do this for non-symbols,
;;; 	but I don't want to do expensive structure1 @< structure2 tests to derive the canonical form.
(defun km-canonicalize (expr)
  (cond ((and (pairp expr)
	      (not (member (first expr) *reserved-keywords*)))
	 `#$(the ,(SECOND EXPR) of ,(FIRST EXPR)))
	((and (triplep expr)
	      (set-unification-operator (second expr)))			; fold &&, &&?, &&! into a single canonical form
	 `(,(first expr) #$set-unified-with ,(third expr)))		; [1] must distinguish set-unified and unified,
;	 `(,(first expr) #$unified-with ,(third expr)))			; see test-suite/unification.km for bug if they're
									; the same.
	 ((and (triplep expr)		; fold &, &?, &! into a single canonical form
	       (val-unification-operator (second expr))
	       (neq (second expr) '&+!)	; This isn't really a primitive unification operator -- it is decomposed in
					; interpreter.lisp to &+? plus &!. Thus we don't canonicalize it, as we don't
	       				; want the subsequent &+? or &! to be taken as looping
;	       (neq (second expr) '&+)	; EXCEPT: These *is* a valid subgoal of &&, etc.
;	       (member (second expr) '(&! &+?))	; EXCEPT: These *are* valid subgoals of &+!
;	       (member (second expr) '(&+ &+!))	; Allow &? as a valid subgoal of these
	       )
	  (cond ((and (symbolp (first expr))
		     (symbolp (third expr))
		     (string> (symbol-name (first expr)) (symbol-name (third expr))))
		`(,(third expr) #$unified-with ,(first expr)))
	       (t `(,(first expr) #$unified-with ,(third expr)))))
;		`((,(third expr)) #$unified-with (,(first expr))))
;	       (t `((,(first expr)) #$unified-with (,(third expr))))))
	(t expr)))

;;; (a && b) (a & b)

;;; ----------------------------------------
;;;	DISPLAY OF EXPRESSION STACK
;;; ----------------------------------------

#|
  <- (_Chassis70)             "(the body-parts of *MyCar)"
  (3) Look in supersituation(s)
  -> (in-situation *Global (the parts of *MyCar))g
----------------------------------------

 CURRENT GOAL STACK IS AS FOLLOWS:
 -> (the parts of *MyCar)                              [called in _Situation69]
  -> (in-situation *Global (the parts of *MyCar))      [called in _Situation69]

|#

(defun show-goal-stack (&optional (stream *standard-output*))
  (let ( (show-situationsp (some #'(lambda (item) (neq (second item) *global-situation*)) (goal-stack))) )
    (format stream "--------------------~%~%")
    (format stream " CURRENT GOAL STACK IS AS FOLLOWS:~%")
    (show-goal-stack2 (reverse (goal-stack)) 1 show-situationsp stream)
    (format stream "~%--------------------~%")))

;;; Can turn this on for nicer formatting
(defvar *show-inference-numbers* nil)

(defun show-goal-stack2 (stack depth show-situationsp &optional (stream *standard-output*))
  (cond
   ((endp stack) nil)
   (t (let* ((item (first stack))
	     (expr (stacked-expr item))
	     (situation (stacked-situation item))
	     (inference-number (stacked-inference-number item))
	     (target (stacked-target item))
	     )
	(cond (*show-inference-numbers*
	       (km-format stream "~a~vT-> ~a" inference-number (+ depth 7) (desource expr)))
	      (t (km-format stream "~vT-> ~a" depth (desource expr))))
; truncated version
;		 (format t (truncate-string (apply #'km-format `(nil "~vT -> ~a" ,depth ,(desource expr))) 80))
	(cond ((and target show-situationsp) (km-format stream "~%~vT[for ~a, in ~a]~%" (+ depth 3) target situation))
	      (show-situationsp (km-format stream "~vT[called in ~a]~%" 55 situation))
	      (target (km-format stream "~%~vT[for ~a]~%" (+ depth 3) target))
	      (t (format stream "~%")))
	(show-goal-stack2 (rest stack) (1+ depth) show-situationsp stream)))))

;;; ======================================================================
;;;		THE OBJECT STACK
;;; ======================================================================

(defun clear-obj-stack () (km-setq '*obj-stack* nil))

;;; Note we filter out duplicates and classes at access time (obj-stack), rather than
;;; build-time (here), for efficiency.
(defun push-to-obj-stack (instance)
  (cond ((and (not (member instance *obj-stack*))
	      (stackable instance))
;	  (make-transaction `(setq *obj-stack* ,(cons instance *obj-stack*))))))
;	  (setq *obj-stack* (cons instance *obj-stack*)))))		; don't need to unwind this
	  (km-push instance '*obj-stack*))))

(defparameter *unstackable-kb-instances* '#$(t))

(defun stackable (instance)
  (and (kb-objectp instance)
       (not (classp instance))
       (not (slotp instance))
       (not (member instance *unstackable-kb-instances*))))

;;; Only called by delete-frame, which is NOT part of the normal KM.
;;; Note that this removal is *NOT* unwound by undo commands, to save memory.
;;; [1] Call to (obj-stack) is WAY too slow!
(defun remove-from-stack (instance)
; (make-transaction `(setq *obj-stack* ,(remove instance (obj-stack)))))
  (setq *obj-stack* (remove instance (obj-stack)))) ; don't need to unwind this [1]. remove removes ALL entries

;;; ----------------------------------------

;;; Find the first instance on *obj-stack* in class
(defun search-stack (class)
   (find-if #'(lambda (instance) (isa instance class)) *obj-stack*))

;;; ----------

(defun show-obj-stack ()
   (mapcar #'(lambda (instance) (km-format t "   ~a~%" instance)) (obj-stack))
   t)

;;; Obsolete now
(defun show-context () (show-obj-stack))

;;; Not used
;(defun showme-context () (showme (vals-to-val (reverse (obj-stack)))) t)

(defun unfiltered-obj-stack () *obj-stack*)

;(defun obj-stack ()
;  (let ( (clean-stack (remove-dup-atomic-instances *obj-stack*)) )
;    (cond ((not (equal clean-stack *obj-stack*))
;	   (setq *obj-stack* clean-stack)))
;    clean-stack))

; (defun obj-stack () (remove-dup-atomic-instances *obj-stack*)) ; new - too slow!!!

(defun obj-stack ()
  (let ((clean-stack			; (remove-dup-atomic-instances *obj-stack*)) )
	 (dereference *obj-stack*)))	; better
    (cond ((not (equal clean-stack *obj-stack*))
	   (setq *obj-stack* clean-stack)))
    clean-stack))

(defun showme-strings (km-expr &optional (situations (all-situations))
                       (theories (all-theories))
					 ;; RVA 21Aug2006 fix km rep loop input output
					 ;; stream defaulting to nil (*standard-input*) instead of t (*terminal-io*)
					 ;; PEC 11/26/11 - no, NIL suppresses the important information message! Setting default back to t
                       (stream *standard-output*))
  (showme km-expr situations theories stream t))

;; [1] FLE 04Aug2005 - Updated by Francis Leboutte, return-strings-p flag
;;; If t, returns a string or a list of strings of the output instead of the frames
(defun showme (km-expr &optional (situations (all-situations))
                       (theories (all-theories))
                       ;; RVA 21Aug2006 fix km rep loop input output problem
				 ;; stream defaulting to nil (*standard-input*) instead of t (*terminal-io*)
				 ;; PEC 11/26/11 - no, NIL suppresses the important information message! Setting default back to t
                       (stream *standard-output*) return-strings-p)
  (let* (;;(frames (km-int km-expr :fail-mode 'error))
         (frames (km km-expr))	; NEW: Might be called from within KM or as top-level call; need to account for both.
	 			; (OLD: when was km-int, won't catch any throws that occur and won't reset trace depth)
;        (frames (km-int km-expr))
         (frame (first frames))
         ;; FLE 04Aug2005
         (result nil))
    (cond ((and (singletonp frames)
		(neq km-expr frame)
		(kb-objectp km-expr)	; ie. _Car23
		(is-km-term frame))	; eg. _Car23, or "MyCar"
	   (km-format stream ";;; (~a is bound to ~a)~%~%" km-expr frame)))
    (cond ((null frames)
           (km-format t ";;; (No frames to show: ~a evaluates to NIL)~%" km-expr))
          ((singletonp frames)
           (setf result
                 (showme-frame frame situations theories stream)))
	  (t (mapc #'(lambda (frame)
                       (push
                        (showme-frame frame situations theories stream)
                        result)
		       (princ ";;; ----------" stream)
		       (terpri stream)
		       (terpri stream))
		   frames)))
    (cond (return-strings-p result)
	  (t frames))))

(defun showme-frame (frame &optional (situations (all-situations)) (theories (all-theories))
                           ;; RVA 21Aug2006 fix km rep loop input output problem
				     ;; stream defaulting to nil (*standard-input*) instead of t (*terminal-io*)
				     ;; PEC 11/26/11 - no, NIL suppresses the important information message! Setting default back to t
                           (stream *standard-output*))
  (cond ((not (is-km-term frame))
	 (report-error 'nodebugger-error "Doing (showme-frame ~a) - the frame name `~a' should be a KB term!~%" frame frame))
	(t (princ (write-frame frame :situations situations :theories theories) stream))))

;;; ======================================================================

;;; This shows all valid slots!
(defun showme-all (km-expr &optional (situations (all-situations)))
  (let* ( (frames (km-int km-expr :fail-mode 'error))
	  (frame (first frames)) )
    (cond ((and (singletonp frames)
		(neq km-expr frame)
		(kb-objectp km-expr)	; ie. _Car23
		(is-km-term frame))	; eg. _Car23, or "MyCar"
	   (km-format t ";;; (~a is bound to ~a)~%" km-expr frame)))
    (cond ((singletonp frames) (showme-all-frame frame situations))
	  (t (mapc #'(lambda (frame)
		       (showme-all-frame frame situations)
		       (princ ";;; ----------")
		       (terpri)
		       (terpri))
		   frames)))
    frames))

(defun showme-all-frame (instance &optional (situations (all-situations)))
  (cond ((not (is-km-term instance))
	 (report-error 'nodebugger-error "Doing (showme-all-frame ~a) - the instance name `~a' should be a KB term!~%" instance instance))
	(t (mapc #'(lambda (situation)
		     (showme-own-slots-in-situation instance situation)
		     (showme-member-slots-in-situation instance situation))
		 situations)
	   t)))

;;; e.g. (Car has (superclasses (Vehicle))), (*MyCar has (instance-of (Car)))
;;; [1] Bit inefficient, but simple:
(defun showme-own-slots-in-situation (instance situation)
  (let* ( (own-slots-to-show1 (mapcar #'used-slot-in (get-slotsvals instance :facet 'own-properties :situation situation)))		; [1]
	  (own-slots-to-show2 (mapcar #'used-slot-in (get-slotsvals instance :facet 'own-definition :situation situation)))		; [1]
	  (inherited-slots-to-show (my-mapcan #'(lambda (class)
						  (mapcar #'used-slot-in
							  (append (get-slotsvals class :facet 'member-properties :situation situation)
								  (get-slotsvals class :facet 'member-definition :situation situation))))
					      (all-classes instance)))
	  (slots-to-show (remove-duplicates (append own-slots-to-show1 own-slots-to-show2 inherited-slots-to-show))) )
    (cond
     (slots-to-show
      (cond ((eq situation *global-situation*) (km-format t "(~a has" instance))
	(t (km-format t "(in-situation ~a~% (~a has" situation instance)))
      (mapc #'(lambda (slot)
	      (let* ( (inherited-rule-sets (inherited-rule-sets2 slot (all-classes instance) (list situation)))
		      (own-rule-sets (remove nil (list (get-vals instance slot :facet 'own-properties :situation situation)
						       (get-vals instance slot :facet 'own-definition :situation situation))))
		      (all-rule-sets (desource
				      (bind-self (remove-duplicates (append own-rule-sets inherited-rule-sets) :test #'equal :from-end t) instance)))
		      (joiner (cond ((single-valued-slotp slot) '&)
				    (t '&&))) )
;		(cond ((singletonp all-rule-sets) (km-format t "~%  (~a ~a)" slot (first all-rule-sets)))
		(cond ((singletonp all-rule-sets) (km-format t "~%  (~a " slot) (format t (expr2string (first all-rule-sets))) (format t ")"))
		      (t (print-slot-exprs slot all-rule-sets joiner)))))
	    (sort (copy-list slots-to-show) #'string< :key #'symbol-name))
      (cond ((eq situation *global-situation*) (km-format t ")~%~%"))
	    (t (km-format t "))~%~%")))))))

;;; e.g. (every Car has (parts ((a Wheel))))
(defun showme-member-slots-in-situation (class situation)
  (let* ( (all-classes (cons class (all-superclasses class)))
	  (slots-to-show (remove-duplicates
			  (my-mapcan #'(lambda (class)
					 (mapcar #'used-slot-in (append (get-slotsvals class :facet 'member-properties :situation situation)
									(get-slotsvals class :facet 'member-definition :situation situation))))
				     all-classes))) )
    (cond
     (slots-to-show
      (cond ((eq situation *global-situation*) (km-format t "(every ~a has" class))
	    (t (km-format t "(in-situation ~a~% (every ~a has" situation class)))
      (mapc #'(lambda (slot)
	      (let* ( (all-rule-sets (desource
				      (inherited-rule-sets2 slot all-classes (list situation))))	; find all rule sets in all classes in situation
		      (joiner (cond ((single-valued-slotp slot) '&)
				    (t '&&))) )
		(cond ((singletonp all-rule-sets) (km-format t "~%  (~a " slot) (format t (expr2string (first all-rule-sets))) (format t ")"))
		      (t (print-slot-exprs slot all-rule-sets joiner)))))
	    (sort (copy-list slots-to-show) #'string< :key #'symbol-name))
      (cond ((eq situation *global-situation*) (km-format t ")~%~%"))
	    (t (km-format t "))~%~%")))))))

;;; (used-slot-in '(age (20))) -> age
;;; (used-slot-in '(age ())) -> nil
(defun used-slot-in (slotvals)
  (cond ((not (null (vals-in slotvals))) (slot-in slotvals))))

(defun print-slot-exprs (slot all-rule-sets joiner &key (first-time-through t))
  (cond (first-time-through
	 (case joiner
	       (&  (km-format t "~%  (~a ((  " slot))
	       (&& (km-format t "~%  (~a ((   " slot))))
	(t (km-format t (spaces (+ 6 (length (symbol-name slot)))))
	   (km-format t "~a " joiner)))
  (cond ((single-valued-slotp slot)	; (km-format t "~a" (vals-to-&-expr (first all-rule-sets))))
	 (format t (expr2string (vals-to-&-expr (first all-rule-sets)))))
	(t ; (km-format t "~a" (first all-rule-sets))))
	 (format t (expr2string (first all-rule-sets))))) ; e.g. convert (UNQUOTE fred) to #,fred
  (cond ((null all-rule-sets)
	 (report-error 'program-error "Null all-rule-sets in print-slot-exprs (stack.lisp!)~%"))
	((singletonp all-rule-sets) (format t "))"))
	(t (format t "~%")
	   (print-slot-exprs slot (rest all-rule-sets) joiner :first-time-through nil))))

;;; ======================================================================

;;; This shows all valid slots!
(defun evaluate-all (km-expr &optional (situations (all-situations)))
  (let* ( (frames (km-int km-expr :fail-mode 'error))
	  (frame (first frames)) )
    (cond ((and (singletonp frames)
		(neq km-expr frame)
		(kb-objectp km-expr)	; ie. _Car23
		(is-km-term frame))	; eg. _Car23, or "MyCar"
	   (km-format t ";;; (~a is bound to ~a)~%~%" km-expr frame)))
    (cond ((singletonp frames) (evaluate-all-frame frame situations))
	  (t (mapc #'(lambda (frame)
		       (evaluate-all-frame frame situations)
		       (princ ";;; ----------")
		       (terpri)
		       (terpri))
		   frames)))
    frames))

(defun evaluate-all-frame (instance &optional (situations (all-situations)))
  (cond ((not (is-km-term instance))
	 (report-error 'nodebugger-error "Doing (evaluate-all-frame ~a) - the instance name `~a' should be a KB term!~%" instance instance))
	(t (mapc #'(lambda (situation)
		     (evaluate-all-frame-in-situation instance situation))
		 situations)
	   t)))

(defun evaluate-all-frame-in-situation (instance situation)
  (cond ((eq situation *global-situation*) (km-format t "(~a has~%" instance))
	(t (km-format t "(in-situation ~a~% (~a has~%" situation instance)))
  (mapc #'(lambda (slot)
	    (let ( (domain (or (km-unique-int `#$(the domain of ,SLOT)) '#$Thing)) )
	      (cond ((instance-of instance domain)
		     (let ( (vals (km-int `#$(the ,SLOT of ,INSTANCE))) )
		       (cond ((null vals) (km-format t "  (~a ())~%" slot))
			     (t (km-format t "  (~a ~a)~%" slot vals))))))))
	(sort (copy-list (all-instances '#$Slot)) #'string< :key #'symbol-name))		; copy list just to be safe, as sort is destructive
  (cond ((eq situation *global-situation*) (km-format t ")~%~%"))
	(t (km-format t "))~%~%"))))




