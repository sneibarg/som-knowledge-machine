
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: interpreter.lisp
;;; Author: Peter Clark
;;; Date: July 1994
;;; Purpose: KM Query Language interpreter

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defvar *looping* nil)
(defvar *warnings* nil)
(defvar *errors* nil)
(defvar *error-structures* nil)

(defparameter *multidepth-path-default-searchdepth* 5)

;;; *additional-keywords* ARE allowed as slot names
(defparameter *additional-keywords*
  '#$(TheValue TheValues * called uniquely-called Self QUOTE UNQUOTE == /== > <))	; used for (scan-kb) in frame-io.lisp.
(defparameter *infinity* 999999)

(defparameter *structured-list-val-keywords* '#$(:seq :bag :args :triple :pair :function))

(defparameter *reserved-keywords* 			 ; NOT allowed as class or slot names
  '#$(a some must-be-a mustnt-be-a print format km-format an instance @ retain-expr
;	sometimes
	possible-values excluded-values spy unspy anonymous-instancep sanity-check
	every the the1 the2 the3 theN theNth of forall forall2 with where theoneof theoneof2
	forall-seq forall-seq2 forall-bag forall-bag2 the-class constraints-for rules-for
	the+ a+ evaluate-paths clone a-prototype
	oneof oneof2 It It2 if then else allof allof2 in and or not is & && &? &+ &+? &+! &! &&! = === /= + - / ^
	>= <= isa #|expand-text add-clones-to in-which|# append
	are includes thelast
	:set :seq :bag :args :triple :pair :function :default
	showme-here showme showme-all evaluate-all quote
	delete evaluate has-value andify make-sentence make-phrase #|pluralize|#
	every has now-has also-has also-hasnt now-has-definition
	must is-superset-of covers subsumes has-definition numberp bag seq #|override|#
	no-inheritance comm get-justification
	trace untrace fluent-instancep at-least at-most exactly constraint <> reverse
	is-subsumed-by is-covered-by set-constraint set-filter
	in-situation in-every-situation end-situation do do-and-next in-theory end-theory see-theory hide-theory visible-theories
	curr-situation ignore-result do-script new-context do-plan))

(defparameter *km-lisp-exprs*  		;; KM functions which should function both at the KM> and Lisp prompt.
					;; Note these ALL RETURN (t), hence new-situation and global-situation are not here.
  '(save-kb reset-kb write-kb fastsave-kb fastload-kb faslsave-kb load-newest-kb load-triples orphans
    show-context checkkbon checkkboff show-bindings version dereference-kb
    show-obj-stack clear-obj-stack reset-done kb-size
    clear-evaluation-cache install-all-subclasses clean-taxonomy scan-kb
    disable-classification enable-classification explain-all clear-explanations
    disable-installing-inverses enable-installing-inverses
    start-logging stop-logging set-checkpoint
    start-creations-logging stop-creations-logging set-creations-checkpoint undo-creations
    no-explanations explanations clear-situations
    sanity-checks no-sanity-checks store-kb restore-kb
    fail-quietly fail-noisily requires-km-version catch-explanations show-explanations show-explanations-xml
    instance-of-is-fluent instance-of-is-nonfluent
    eval setq tracekm untracekm license enable-slot-checking disable-slot-checking
    comments nocomments
    trace-to-file-on trace-to-file-off t2f-on t2f-off     ;;; From Raphael Van Dyck, for switching tracing on to a file
    ))

(defparameter *downcase-km-lisp-exprs*
    (mapcar #'(lambda (expr) (intern (string-downcase expr) *km-package*)) *km-lisp-exprs*))

;;; Directs KM to use process-load-expression for these commands used at the KM prompt
(defparameter *loadsave-commands-with-keywords*
    '(load-kb #$load-kb reload-kb #$reload-kb save-kb #$save-kb fastsave-kb #$fastsave-kb
      fastload-kb #$fastload-kb faslsave-kb #$faslsave-kb write-kb #$write-kb load-newest-kb #$load-newest-kb))

;;; Don't strip out (@ ...) structures for lists beginning with these items.
(defparameter *no-decomment-headwords* '#$(comment show-comment explanation))

;;; 10/28/02: These are calls where all the subcalls are direct calls to km-int, so we can defer decommenting down
;;; to there for the elements. i.e., we DON'T decomment the embedded structures when passing to km-int
;;; (defparameter *decomment-top-level-only-headwords* '#$(:set if))
(defparameter *decomment-top-level-only-headwords*
    '#$(if forall allof oneof theoneof forall-seq forall-bag
	forall2 allof2 oneof2 theoneof2 forall-seq2 forall-bag2
	:set :seq :bag :args :triple :pair :function
	))

; from frame-io.lisp, as we want to reference it here
(defparameter *built-in-classes-with-nonfluent-instances-relation* '#$(Situation Slot Partition Theory))
(defparameter *built-in-nonfluent-lookup-only-slots* nil)  ; then setq it later in frame-io.lisp

; No longer used...
;;; For annotation in explain.lisp
;;; Format (<pattern> <vars-to-annotate>). Note a var will only be annotated providing it's a list.
;(defvar *patterns-to-annotate*
;    '#$(((the ?x of ?y) (?y))
;	((the ?x ?y of ?z) (?z))))

;;; --------------------
;;; Change to 'error for test-suite
(defparameter *top-level-fail-mode* 'fail)
(defun fail-noisily () (km-setq '*top-level-fail-mode* 'error) t)
(defun fail-quietly () (km-setq '*top-level-fail-mode* 'fail) t)

(defconstant *default-fail-mode* 'fail)
(defvar *am-reasoning* nil)

;;; --------------------

;;; Backwards-compatibility: (km0 ...) now synonymous with (km ...)
(defun km0 (&optional (kmexpr 'ask-user) &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
							       (t *top-level-fail-mode*))))
  (km kmexpr :fail-mode fail-mode))

;;; The top level call, either by person or machine
;;; RETURNS 3 values:
;;;        - result of evaluating <expr>
;;;	   - if an error occurred, a string describing it
;;;	   - if an error occurred, a structure describing it
;;; NOTE: If *am-reasoning*, then km is equivalent to km-int
;;; [1] NOTE: internal calls WILL do the dereferencing automatically, but the TOP LEVEL call may not, so need to
;;;	do it here. Otherwise, the looping detector will trigger, as looping-on now (KM 2.3.4) does a dereference:
;;;		1 -> (the parts of _X)
;;;		2  -> (the parts of _Engine1)
;;;		      Looping on the parts of _Engine1!
;;; [2] Don't deref for showme, as we want to report "X is bound to Y"
(defun km (&optional (kmexpr 'ask-user) &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
							      (t *top-level-fail-mode*)))
					     (reset-statistics t))
; (km-format t "fail-mode = ~a~%" fail-mode)
  (cond
   ((eq kmexpr 'ask-user) (km-read-eval-print))
   (*am-reasoning* (km-int kmexpr :fail-mode fail-mode)) ; km -> km-int if *am-reasoning* already
   (t (let ((*am-reasoning* t)		; so must be top-level KM call
	    (*warnings* nil)
	    (*errors* nil)
	    (*error-structures* nil))
	(reset-for-top-level-call kmexpr :reset-statistics reset-statistics)
	(let* ((kmexpr0 (cond ((and (listp kmexpr) (member (first kmexpr) '#$(showme showme-all))) kmexpr) ; [2]
			      (t (dereference kmexpr))))
	       (answer0 (catch 'km-abort (desource (km-int kmexpr0 :fail-mode fail-mode))))	; [1]
	       (answer (cond ((and (listp answer0) (eq (first answer0) 'km-abort))
			      (km-format t "(Execution aborted)~%")
			      nil)	; user or KM abort
			     (t answer0))))
	  (cond ((and (null *errors*)
		      (null *error-structures*)
		      (null *warnings*))
		 answer)
		(t (values answer (reverse *errors*) (reverse *error-structures*) (reverse *warnings*)))))))))

;;; [1] See cache-problem.km in test-suite. (reset-done) might be rather inefficiently implemented (?).
;;; [2] For load-kb, load-kb does a (reset-inference-engine) right at the start, and then for specific KM calls
;;;	within load-kb we keep statistics counters going (skip redoing (reset-inference-engine) for each KM call)
(defun reset-for-top-level-call (km-expr &key (reset-statistics t))
;  (km-format t "Resetting for top level call...~%")
  (cond (reset-statistics (reset-inference-engine)))	; [2]
  (cond (*looping*			; better: Only need to reset the cache if you were looping.
	 (reset-done) (setq *looping* nil)))
  (cond ((and km-expr (am-in-prototype-mode)) ; cosmetic: Store prototype build commands and print out if you do a save-kb
	 (add-to-prototype-definition *curr-prototype* km-expr)))
  (cond ((and km-expr (km-assertion-expr km-expr)) (reset-done) #|(clear-cached-explanations)|#))) ; [1]

;;; ----------

(defvar *last-question* nil)		; so we can simply ask "why" rather than "why" with a whole list of arguments
(defvar *last-answer* nil)		; so we can simply ask "why" rather than "why" with a whole list of arguments

#|
21Aug2006
Thanks to Raphael Van Dyck for these improvements!

The KM read-eval-print loop doesn't work well in Lispworks, especially when km
enters the debugger.
The problem arises because a T stream argument is often used in km functions and a T stream
hasn't the same meaning in all the IO CL functions:
- For the CL function format, a stream agument of t means writing to the standard output.
- For the CL functions write, prin1, print, pprint and princ, a stream argument of t means
writing to the terminal.
- For the CL function read, a stream argument of t means reading from the terminal.

The km read-eval-print loop should probably always write to the standard output and
read from the standard input.
Consequently this patch passes a stream argument of nil instead of t to the
functions write, prin1, print, pprint, princ and read.
This patch also adds a fresh-line after the case-sensitive-read-km in the rep loop. This
is because in Lispworks the read function returns as soon as the expression is complete,
causing the value of the expression to be printed on the same line as the expression.

Note
Maybe some other KM functions will need to be fixed in the same way.

[1] We set-checkpoint here, rather than in km-eval-print, as (load-kb ... :verbose t) also calls km-eval-print, and
we DON'T (?) want checkpointing used there too.
|#
(defun km-read-eval-print ()
  (loop
   (reset-inference-engine)
   (print-km-prompt)
   (finish-output)			; flush output if stream is buffered
   (let ( (query (case-sensitive-read-km)) )
     ;; RVA 21Aug2006
     ;; added fresh-line because in lispworks the read function returns the expression as soon as it is complete,
     ;; before the user has pressed the return key
     (fresh-line)
     (cond ((minimatch query '#$(the ?slot of ?expr)) (setq *last-question* query)))
     (cond ((eq query '#$q) (return))
	   (t (cond ((not (skip-checkpoint query)) (set-checkpoint query)))		; [1]
	      (multiple-value-bind
	       (answer error)
	       (km-eval-print query)
	       (values answer error)))))))

(defun skip-checkpoint (query)
  (and (listp query)
       (member (first query) '#$(showme undo why))))

;;; Print out answer...(also reset counters and checkpoint)
(defun km-eval-print (query &key (fail-mode *top-level-fail-mode*))
  (cond ((null query) nil)
	((equal query '#$(undo))
	 (cond ((undo-possible)
		(let* ( (undone-command (undo)) )
		  (km-format t "Undone ~a...~%~%" undone-command) '#$(t)))
	       (t (km-format t "Nothing more to undo!~%~%"))))
       (t ; (reset-done) ;;; moved to km-eval, below. Calls to km-eval and km-eval-print MUST have same behavior!
	   (multiple-value-bind
	       (answer error error-str)
;	       (km-eval query :fail-mode fail-mode)
	       (km query :fail-mode fail-mode)		; phase out km-eval
	     (declare (ignore error-str))
	     (cond (*add-comments-to-names* (write-km-vals answer))
		   (t (km-format t "~a" answer)))
	     (cond (error (format t "   ; (WARNING: Errors occurred during reasoning)~%"))
		   (t (terpri)))
	     (princ (report-statistics))
;;;        (cond (*frame-accessp* (report-frame-access-count)))
	    (terpri)
	    (cond ((minimatch query '#$(the ?slot of ?expr)) (setq *last-answer* answer)))
	    (values answer error)))))

#|
Call to km-int:
answer = EITHER the answer
         OR a list of three things: (km-abort <error-str> <error-struct>)
RETURNS 3 values:
        - result of evaluating <expr>
	- if an error occurred, a string describing it
	- if an error occurred, a structure describing it
reset-inference-engine done up in (km), or NOT, if called by load-kb (don't want to keep resetting counters)
also no checkpointing done
[1] New - see cache-problem.km in test-suite. (reset-done) might be rather inefficiently implemented (?). I wonder if it's too slow.
|#

;;; NEW: Make km-eval synonymous with km. Phase out km-eval in the code at a later time
; (defun km-eval (km-expr &key (fail-mode *top-level-fail-mode*)) (km km-expr :fail-mode fail-mode))

;;; ----------

(defun print-km-prompt (&optional (stream t))
  (cond ((and (am-in-local-situation) (am-in-prototype-mode))
	 (report-error 'user-error "You are in both prototype-mode and in a Situation, which isn't allowed!~%"))
	((and (am-in-local-theory) (am-in-prototype-mode))
	 (report-error 'user-error "You are in both prototype-mode and in a Theory, which isn't allowed!~%"))
;  (cond ((and (am-in-prototype-mode) (am-in-local-situation)) (km-format stream "[prototype-mode, ~a] KM> " (curr-situation)))
        ((am-in-prototype-mode) (km-format stream "[prototype-mode] KM> "))
	((am-in-local-situation) (km-format stream "[~a] KM> " (curr-situation)))
	((am-in-local-theory) (km-format stream "{~a} KM> " (curr-situation)))
	(t (km-format stream "KM> "))))

;;; ======================================================================
;;;		KM HANDLER METHODS
;;;  (km-int <expr>) is the recursive to KM *internal* to the KM Engine
;;; ======================================================================

;;; 		(km-int <expr>) will evaluate <expr>
;;;
;;; km evaluates the expression (a path) which is given to it, and returns a
;;; list of instances which the path points to.
;;; <expr> must be either an INSTANCE or a PATH. (NB: A list of instances is
;;; treated as a path. If you do want a set, you must precede the list by the
;;; keyword ":set")
;;;
;;; Fail-modes: If km fails to find a referent at the end of the path,
;;; it can either fail quietly and return nil (), or
;;; gives a warning (:fail-mode 'error). 'error is very useful for debugging
;;; the KB.

(defvar *spypoints* nil)
(defvar *profiling* nil)

;;; For Jason Chaw. Accessors in trace.lisp
(defvar *silent-spypoints* nil)
(defvar *silent-spypoints-log* nil)
(push '*silent-spypoints* *km-runtime-variables*)
(push '*silent-spypoints-log* *km-runtime-variables*)

#|
Called by lazy-unify, where we want to look like trace-expr has gone through km-int, with kmexpr as the subgoal,
even though this isn't literally true.
In other words, this splices an extra step in the trace output which doesn't really exist in KM.
Rather than displaying:
	-> (_Car1 &? _Car2)
         -> ((a Engine) (a Chassis))
	 <- (_Engine1 _Chassis3)
         -> ((a Engine) (a Chassis))
	 <- (_Engine4 _Chassis5)
It displays:
	-> (_Car1 &? _Car2)
         -> (the parts of _Car1)
          -> ((a Engine) (a Chassis))
	  <- (_Engine1 _Chassis3)
         -> (the parts of _Car2)
          -> ((a Engine) (a Chassis))
	  <- (_Engine4 _Chassis5)
Note the "virtual" extra steps inserted. The (the parts of _Car1) are in fact done by a direct
get-vals in lazy-unify, rather than by a recursive call to KM, but we still want to show this to
the user.
|#
(defun km-int-with-trace (trace-expr kmexpr &key (fail-mode *default-fail-mode*) (check-for-looping t) target)
  (prog2
      (push-to-goal-stack trace-expr :target target)
      (let* ((users-goal (km-trace 'call "-> ~a" trace-expr))
	     (answer (cond ((eq users-goal 'fail) nil)
			   (t (km-int kmexpr :fail-mode fail-mode :check-for-looping check-for-looping :target target))))
	     (users-response (cond ((or answer
					(not (km-boolean-exprp kmexpr)))
				    (km-trace 'exit "<- ~a~30T\"~a\"" answer trace-expr))
				   (t (km-trace 'fail "<- FAIL!~30T\"~a\"" trace-expr)))) )
	(cond ((eq users-response 'redo)
	       (reset-done)
	       (km-int-with-trace trace-expr kmexpr :fail-mode fail-mode :check-for-looping check-for-looping :target target))
	      ((eq users-response 'fail) nil)
	      (t answer)))
    (pop-from-goal-stack)))

;;; --------------------

;;; Wrapper, to maintain a stack and check for looping
#|
 kmexpr-with-comments is the expression passed to km-int. It may include comments.
 kmexpr is the ACTUAL expression to evaluate by km.
    This requires remove all comments, EXCEPT for assertion statements (has, a, some) in which only the TOP LEVEL comments are stripped
    (so that the sub-level comments get asserted in the KB)
|#
(defun km-int (kmexpr-with-comments &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
							  (t *top-level-fail-mode*)))
					 (check-for-looping t) target rewritep)
;  (cond ((null kmexpr-with-comments) (break)))
  (cond
   ((null *am-reasoning*) (km kmexpr-with-comments :fail-mode fail-mode)) ; eg. top-level (in-situation <x>) calls km-int

;;;   FAILED similification
   (t (let*
	  ((kmexpr
	     (cond ((km-assertion-expr kmexpr-with-comments) ; (every Car has (parts ((a Engine [Car1])))
		    (desource+decomment-top-level kmexpr-with-comments)) ; NB leave embedded comments in here
		   ((and (listp kmexpr-with-comments) ; (comment [Cat1] "a cat" "people like cats")
			 (or (member (first kmexpr-with-comments) *no-decomment-headwords*)
			     (and (eq (first kmexpr-with-comments) '#$in-situation)
				  (listp (third kmexpr-with-comments))
				  (member (first (third kmexpr-with-comments)) *no-decomment-headwords*))))
		    kmexpr-with-comments)
		   ((or			; for these cases we DON'T want to decomment the embedded comments, they're
					; need as the expr is broken up
		     (and target	; target= (the pets of Pete)
			  (record-explanation-later kmexpr-with-comments)) ; ((a Cat [Cat1]) & (a Pet [Pet1]))
		     (and (listp kmexpr-with-comments)
			  (member (first kmexpr-with-comments) *decomment-top-level-only-headwords*)))
		    (desource+decomment-top-level kmexpr-with-comments))
;;; NEW: Decomment *everything* ONLY at the top level
		   (t (desource-top-level (decomment kmexpr-with-comments))))

;;; Why did I comment this out? Reinstate bits of it above...
	#|
             (cond ((or (km-assertion-expr kmexpr-with-comments) ; (every Car has (parts ((a Engine [Car1])))
			     (and target 							; target=(the pets of Pete)
				  (record-explanation-later kmexpr-with-comments))  		; ((a Cat [Cat1]) & (a Pet [Pet1]))
			     (and (listp kmexpr-with-comments)
				  (member (first kmexpr-with-comments) *decomment-top-level-only-headwords*))
;			     (let ((kmexpr0 (desource+decomment-top-level kmexpr-with-comments)))
;			       (some #'(lambda (pattern+vars) ; patterns by definition don't have top-level annotated
;					 (minimatch kmexpr0 (first pattern+vars)))
;				     *patterns-to-annotate*))
			     )
			   (desource+decomment-top-level kmexpr-with-comments))
		     ((and (listp kmexpr-with-comments) ; (comment [Cat1] "a cat" "people like cats")
			   (or (member (first kmexpr-with-comments) *no-decomment-headwords*)
			       (and (eq (first kmexpr-with-comments) '#$in-situation)
				    (listp (third kmexpr-with-comments))
				    (member (first (third kmexpr-with-comments)) *no-decomment-headwords*))))
		      kmexpr-with-comments)
		     (t (desource+decomment kmexpr-with-comments)))
|#
        ))

;    (km-format t "~%kmexpr-with-comments:~%  ~a~%" kmexpr-with-comments)
;    (km-format t "kmexpr-without-assignment:~% ~a~%" kmexpr-without-assignment)
;    (km-format t "kmexpr (to actually process):~% ~a~%" kmexpr)
  (cond ((and *spypoints*
	      (some #'(lambda (spypoint) (minimatch kmexpr spypoint)) *spypoints*))
	 (km-format t "(Spypoint reached!)~%")
	 (tracekm)))
  (cond ((and *silent-spypoints*
	      (some #'(lambda (spypoint) (minimatch kmexpr spypoint)) *silent-spypoints*))
	 (push kmexpr *silent-spypoints-log*)))
  (cond ((and (not *are-some-constraints*) (constraint-exprp kmexpr)) (note-are-constraints)))
  (cond
   ((member kmexpr '#$((tracekm) (TRACEKM) (trace) (TRACE)) :test #'equal)
    (reset-trace-depth)
    (tracekm)
    '#$(t))
   ((member kmexpr '#$((untracekm) (UNTRACEKM) (untrace) (UNTRACE)) :test #'equal)
    (reset-trace-depth)
    (untracekm)
    '#$(t))
   ((and (listp kmexpr)				; handle case-sensitivity for keywords in load-kb
	 (member (first kmexpr) *loadsave-commands-with-keywords*))
    (process-load-expression kmexpr))
   ((and (listp kmexpr) (member (first kmexpr) *km-lisp-exprs*))
;   (eval kmexpr) '#$(t) ; old
    (let ((answer (listify (eval kmexpr))))
      (cond ((and (null answer)
		  (eq fail-mode 'error)
		  (not (and (triplep kmexpr) (eq (first kmexpr) 'setq))))
	     (report-error 'user-error "No values found for ~a!~%" kmexpr)))
      answer))
   ((and (listp kmexpr) (member (first kmexpr) *downcase-km-lisp-exprs*))
;   (eval (cons (intern (string-upcase (first kmexpr)) *km-package*) (rest kmexpr))) '#$(t) ; old
    (let ((answer (listify (eval (cons (intern (string-upcase (first kmexpr)) *km-package*) (rest kmexpr)))))) ; new
      (cond ((and (null answer)
		  (eq fail-mode 'error)
		  (not (and (triplep kmexpr) (eq (first kmexpr) '#$setq))))
	     (report-error 'user-error "No values found for ~a!~%" kmexpr)))
      answer))
   ((and (am-in-local-situation) (am-in-prototype-mode))
    (report-error 'user-error "You are in both prototype-mode and in a Situation, which isn't allowed!~%"))
   ((and (am-in-local-theory) (am-in-prototype-mode))
    (report-error 'user-error "You are in both prototype-mode and in a Theory, which isn't allowed!~%"))
   ((or (null kmexpr)   	 ; fast handling of these special cases, copied from *km-handler-function*
	(eq kmexpr '#$nil)	 ; This IS allowed to fail quietly
	(and (constraint-exprp kmexpr)
	     (not (retain-exprp kmexpr))))
    (cond ((eq fail-mode 'error) (report-error 'user-error "No values found for ~a!~%" kmexpr)))
    nil)
   ((and (atom kmexpr)
	 (not (no-reserved-keywords (list kmexpr))))	; User error! Contains keywords, so fail out
    nil)
   ((km-varp kmexpr)
    (report-error 'user-error "Unbound variable ~a encountered!~%" kmexpr))
   ((and  ; (fully-evaluatedp kmexpr)  ; fast handling, & don't clutter up the program trace with reflexive calls
	    (fully-evaluatedp kmexpr-with-comments) ; NEW: Need to pass through interpreter to catch explanation
     (eql (dereference kmexpr) kmexpr))	; Is this the reflexive case? see
    (cond ((km-setp kmexpr) (set-to-list kmexpr))
	  ((and (listp kmexpr)
		(eq (first kmexpr) '#$:triple)
		(not (= (length (rest kmexpr)) 3))
		(report-error 'user-error "~a: A triple should have exactly three elements!~%" kmexpr)))
	  ((and (listp kmexpr)
		(eq (first kmexpr) '#$:pair)
		(not (= (length (rest kmexpr)) 2))
		(report-error 'user-error "~a: A pair should have exactly two elements!~%" kmexpr)))
	  (t (list kmexpr))))
   ((internal-commentp kmexpr-with-comments)
    (let ( (comment-tag (second kmexpr-with-comments)) )
      (report-error 'user-error "Comment tag ~a was encountered as a free-standing
       slot-value in the KB - not allowed! It should be embedded within a KM expression.~%" comment-tag)))
   ((and check-for-looping
	 (looping-on kmexpr-with-comments))			; LOOPING! Defined in stack.lisp
    (km-trace 'comment "Looping on ~a!" kmexpr)
;    (break)
    (handle-looping kmexpr))
   ((and *km-depth-limit*
	 (> *depth* *km-depth-limit*))
    (km-trace 'comment "Maximum depth limit reached, doing ~a!" kmexpr)
    (handle-looping kmexpr :reason 'depth-limit-reached))
   ((and *instances-being-unified*
	 (listp kmexpr)
	 (= (length kmexpr) 3)
	 (full-equality-assertion-operator (second kmexpr))
	 (let* ((instance1 (first kmexpr))
		(instance2 (third kmexpr)))
	   (need-to-defer-unification instance1 instance2)))
;	   (or (and (kb-objectp instance1) (member instance1 *instances-being-unified*))
;	       (and (kb-objectp instance2) (member instance2 *instances-being-unified*)))))
    (let* ((instance1 (first kmexpr))
	   (instance2 (third kmexpr))
	   (instance-already-being-unified
	    (cond ((member instance1 *instances-being-unified*) instance1)
		  ((member instance2 *instances-being-unified*) instance2))))
      (make-comment "~a: Deferring unification: ~a is already undergoing unification higher up in the goal stack!"
		 (desource kmexpr) instance-already-being-unified)
      (pushnew kmexpr *deferred-unifications* :test #'equal)
      (list instance-already-being-unified)))
   (t (prog2
	  (push-to-goal-stack kmexpr-with-comments :target target)
	  (km1 kmexpr kmexpr-with-comments :fail-mode fail-mode :target target :rewritep rewritep)
	(pop-from-goal-stack)
	(cond ((and *deferred-unifications*
		    (listp kmexpr)	; &-exprp too specific; want to include &? and &+? also
		    (equality-assertion-operator (second kmexpr))) ; (& &+ &+! &! ==)
	       (mapc #'(lambda (deferred-unification)
			 (let ((i1 (first deferred-unification))
			       (i2 (third deferred-unification)))
			   (cond ((not (need-to-defer-unification i1 i2)) ; i.e., no longer need to defer it...
				  (setq *deferred-unifications* (remove deferred-unification *deferred-unifications*))
				  (cond ((member deferred-unification *failed-unification-attempts* :test #'equal)
					 (make-comment "~a complete. But NOT attempting the deferred unification ~a as it is already known to fail!"
						       kmexpr deferred-unification))
					(t (make-comment "~a complete. Now attempting the deferred unification ~a..."
							 kmexpr deferred-unification)
					   (km-int deferred-unification)))))))
		     *deferred-unifications*)))
	)))))))

(defun need-to-defer-unification (i1 i2)
  (and (kb-objectp i1)
       (kb-objectp i2)
       (or (member i1 *instances-being-unified*)
	   (member i2 *instances-being-unified*))))

;;; ----------------------------------------
;;;	Handling of loops - allow inductive completion of proofs
;;; ----------------------------------------

;;; reason = loop-detected OR depth-limit-reached
;;; [2] Not having the correct target-situation specified seems like an error to me.
(defun handle-looping (kmexpr &key (reason 'loop-detected))
  (setq *looping* t)
  (let ( (cexpr (km-canonicalize kmexpr)) )
    (cond ((and (minimatch cexpr '#$(the ?slot of ?instance))  ; SPECIAL CASE: (the <slot> of <instance>)
		(symbolp (second cexpr))			 ; Do the best you can (even if incomplete!)
;	        (is-km-term (fourth cexpr)))		; [1] (see below)
		(kb-objectp (fourth cexpr)))		; [1] (see below)
	   (let* ( (instance (fourth cexpr))
		   (slot (second cexpr))
; [2]		   (vals (get-vals instance slot)) )	; no remove-constraints, as [1] prevents exprs with constraints in ; 5/3/01 - how???
		   (vals (get-vals instance slot :situation (target-situation (curr-situation) instance slot))) ) ; no remove-constraints, as [1] prevents exprs
	     (km-trace 'comment "Just using values found so far, = ~a..." vals)					  ; with constraints in ; 5/3/01 - how???
	     (cond ((every #'fully-evaluatedp vals) vals)
		   (t (let ((kmexpr2 (vals-to-val vals))) ; vals may be an expression! ? see test-suite/looping.km
			(cond ((not (looping-on kmexpr2))  ; very important!!!!
			       (let ((new-vals (km-int kmexpr2)))

;			       (let ((new-vals (prog2   ; No  don't stack - will ALWAYS seem like looping!
;						   (push-to-goal-stack kmexpr2)    ; NOTE: must stack to spot looping during looping
;						   (km-int kmexpr2)	; recovery
;						 (pop-from-goal-stack))))

				 (cond ((not (dont-cache-values-slotp slot))
;			       (put-vals instance slot new-vals :install-inversesp nil))) ; constraints will be added + note-done when loop is unwound
;;; No: The "nil" causes a bug - see inverses-bug.km in test-suite
					(put-vals instance slot new-vals))) ; constraints will be added + note-done when loop is unwound
				 new-vals)))))))) ;						to upper calling level
	  ((and (listp kmexpr)		; &-exprp too specific; want to include &? and &+? also
		(val-unification-operator (second kmexpr))) ; (a &/&?/&! b): Inductive proof: Can assume (X &? Y) when proving (X &? Y)
	   (cond ((member (second kmexpr) '(&? &+?))
		  (case reason
			(loop-detected (km-trace 'comment "Assuming ~a to prove ~a (ie. Inductive proof)" kmexpr kmexpr) '#$(t))
			(depth-limit-reached (km-trace 'comment "Assuming success...") '#$(t))))			; Very questionable assumption!
		 (t (let ( (val (find-if #'kb-objectp (&-expr-to-vals kmexpr))) )	; find first fully evaluated val
		      (cond (val
			     (case reason
				   (loop-detected (km-trace 'comment "Assuming ~a to prove ~a (ie. Inductive proof)" kmexpr kmexpr))
				   (depth-limit-reached (km-trace 'comment "Just using value found so far, = ~a..." val)))
			     (list val)))))))
	  ((&&-exprp kmexpr)
	   (let ( (answer (find-if #'(lambda (set) (every #'kb-objectp set)) (&&-exprs-to-valsets (list kmexpr)))) )
	     (cond (answer
		    (case reason
			  (looping-detected (km-trace 'comment "Assuming ~a to prove ~a (ie. Inductive proof)" kmexpr kmexpr))
			  (depth-limit-reached (km-trace 'comment "Just using value found so far, = ~a..." answer)))
		    answer))))
	  (t (km-trace 'comment "Giving up...)" kmexpr)
	     nil))))

;;; ----------------------------------------

;;; Extensions for Jihie:
;(defvar *trace-log* nil)		 ; **** NEW LINE
;(defvar *trace-log-on* nil)		 ; **** another NEW LINE

(defvar *print-explanations* nil)
(defvar *catch-explanations* nil)
(defvar *catch-next-explanations* nil)
(defvar *explanations* nil)

;;; (km1 ...)
;;; [1] Note we can't do a remove duplicates, as we often need duplicate
;;; entries in. Eg. ("remove" _car1 "and put" _car1 "into the furnace")
;;; target = the target slot and frame for the result, in the form '#$(the <slot> of <instance>). NIL if none known eg. top-level query
(defun km1 (kmexpr kmexpr-with-comments &key (fail-mode *default-fail-mode*) target rewritep)
  (increment-inference-statistics)
;  (km-format t "*deferred-unifications* = ~a~%" *deferred-unifications*)
  (cond (*profiling* (profile-call (desource kmexpr))))
;  (if (and *trace-log-on* (not *am-classifying*))								; **** another NEW LINE
;      (setq *trace-log* (cons `(,(1+ *depth*) call ,kmexpr-with-comments) *trace-log*))) ; **** NEW LINE
  (let* (
	(users-goal (cond (target (km-trace 'call "-> ~a~40T [for ~a]"  				; "-> (a Car)  [for (the parts of _Car3)]"
				     kmexpr-with-comments target))
			  (t (km-trace 'call "-> ~a" kmexpr-with-comments))))
	(dummy (cond ((or *catch-explanations* *print-explanations*) (catch-explanation kmexpr-with-comments 'call)))))
    (declare (ignore dummy))
    (multiple-value-bind
     (answer0 handler-pattern)				; handler-pattern now used
     (cond ((eq users-goal 'fail) nil)
	   ((atom kmexpr) (list kmexpr))		; [2]: Checks for keywords and add-to-obj-stack in km [1] above
	   (*compile-handlers* (funcall *km-handler-function* fail-mode target kmexpr)) ; COMPILED DISPATCH MECHANISM
	   (t (let* ( (handler (find-handler kmexpr *km-handler-alist*))  ; INTERPRETED DISPATCH MECHANISM
		      (answer00 (apply (first handler) `(,fail-mode ,target ,@(second handler))))
		      (pattern (third handler)) )
		(values answer00 pattern))))
     (let ( (answer (remove-dup-instances (remove nil answer0))))		; NOTE includes dereferencing
       (cond ((and (null answer)
		   (eq fail-mode 'error))
	      (report-error 'user-error "No values found for ~a!~%" kmexpr-with-comments)))
       (process-km1-result answer kmexpr kmexpr-with-comments :fail-mode fail-mode :target target :handler-pattern handler-pattern :rewritep rewritep)))))

;;; This allows handling of redo and fail options when tracing.
#|
*failed-unification-attempts*: To make sure we don't get stuck in a loop with *deferred-unifications*
-> (_X & _Y1)
 -> (_X & _Y2)
 <- defer (_X & _Y2)
<- (_X & _Y1) FAILS due to KB error
-> (_X & _Y2) - now do the deferred unification
 -> (_X & _Y1)
 <- defer (_X & _Y1)
<- (_X & _Y2) FAILS due to KB error
-> (_X & _Y1) - now do the deferred unification
  etc. etc.

To break this pattern, if we've attempted and failed out of (_X & _Y1), we *don't* reattempt it
|#
(defun process-km1-result (answer kmexpr kmexpr-with-comments &key (fail-mode *default-fail-mode*) target handler-pattern rewritep)
 (mapc #'(lambda (val) (cache-explanation-for val kmexpr)) answer) ; NOW: store the *decommented* version. NB kmexpr isn't
 (cond ((and target						   ;      fully decommented for (a ... with ...) exprs
	     (not rewritep)				; don't record all the rewrites
	     *record-explanations*
	     (not (record-explanation-later kmexpr-with-comments)) )
	(mapc #'(lambda (val) (record-explanation-for target val kmexpr-with-comments)) answer)))
 (cond ((and (not rewritep)
	     *record-explanations*
	     (existential-exprp kmexpr))
	(cond
	 ((not (singletonp answer))
	  (report-error 'program-error "Multiple values from an existential expr ~a!~%" kmexpr))
	 (t (let ((class (second kmexpr))) ; (a Car [with ...])
	      (record-explanation-for `#$(the instance-of of ,(FIRST ANSWER)) class kmexpr-with-comments))))))
; (if (and *trace-log-on* (not *am-classifying*)) ; **** another NEW LINE
;      (setq *trace-log* (cons `(,*depth* exit ,kmexpr-with-comments ,answer) *trace-log*))) ; **** NEW LINE
 (cond ((or *catch-explanations* *print-explanations*) (catch-explanation kmexpr-with-comments (cond (answer 'exit) (t 'fail)))))
 (cond (*profiling* (profile-exit (desource kmexpr))))
 (let ( (users-response
	 (cond ((or answer (not (km-boolean-exprp kmexpr)))
		(cond (target (km-trace 'exit "<- ~a~40T [~a, for ~a]" answer kmexpr-with-comments target))
		      (t (cond ((and *deferred-unifications*
				     (listp kmexpr)
				     (= (length kmexpr) 3)
				     (full-equality-assertion-operator (second kmexpr))
				     (kb-objectp (first kmexpr))
				     (kb-objectp (third kmexpr)))
				(push kmexpr *failed-unification-attempts*)
				))
			 (km-trace 'exit "<- ~a~40T [~a]" answer kmexpr-with-comments))))
	       (t (cond (target (km-trace 'fail "<- FAIL!~40T [~a, for ~a]" kmexpr-with-comments target))
			(t (km-trace 'fail "<- FAIL!~40T [~a]" kmexpr-with-comments)))))) )
    (cond ((eq users-response 'redo)
	   (reset-done)
	   (km1 kmexpr kmexpr-with-comments :fail-mode fail-mode :target target :rewritep rewritep))
	  ((eq users-response 'fail)					; resets answer to be NIL [doesn't destroy cached non-nil answers though!]
	   (increment-trace-depth)					; put *depth* back to where it was
	   (process-km1-result nil kmexpr kmexpr-with-comments
			       :fail-mode fail-mode :target target :handler-pattern handler-pattern))
	  (t answer))))

;;; ----------------------------------------
;;; km-unique: Expected to return EXACTLY *one* value, otherwise a warning is generated.
;;; ----------------------------------------

;;; Backwards-compatibility: (km-unique0 ...) now synonymous with (km-unique ...)
(defun km-unique0 (kmexpr &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
							       (t *top-level-fail-mode*))))
  (km-unique kmexpr :fail-mode fail-mode))

;;; EXTERNAL, from some other application - rewritten 1/19/08 to be identical in structure to (defun km ...)
;;; [1] must dereference top-level call to make sure looping isn't accidentally mis-triggered [see (defun km ...) comment]
(defun km-unique (kmexpr &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
					       (t *top-level-fail-mode*))))
  (cond
   (*am-reasoning* (km-unique-int kmexpr :fail-mode fail-mode)) ; km-unique -> km-unique-int if *am-reasoning* already
   (t (let ((*am-reasoning* t)		; so must be top-level KM call
	    (*warnings* nil))
	(reset-for-top-level-call kmexpr)
	(let ((answer (catch 'km-abort (desource (km-unique-int (dereference kmexpr) :fail-mode fail-mode))))) ; [1]
	  (cond ((and (listp answer)
		      (eq (first answer) 'km-abort)) ; error encountered
		 (values nil (second answer) (third answer) (reverse *warnings*)))
		(*warnings* (values answer nil nil (reverse *warnings*)))
		(t answer)))))))

#|
;;; EXTERNAL, from some other application
(defun km-unique (kmexpr &key (fail-mode *top-level-fail-mode*))
  (reset-inference-engine)
  (let ( (answer (catch 'km-abort (km-unique-int kmexpr :fail-mode fail-mode))) )
    (cond ((and (pairp answer)
		(eq (first answer) 'km-abort))		; error encountered
	   (values nil (second answer)))
	  (t answer))))
|#

;;; ----------

;;; INTERNAL, from within KM itself.
(defun km-unique-int (kmexpr &key (fail-mode (cond (*am-reasoning* *default-fail-mode*)
						   (t *top-level-fail-mode*)))
				  target rewritep)
  (cond
   ((null *am-reasoning*) (km-unique kmexpr :fail-mode fail-mode))  ; if called from top-level call (in-situation ...) say
   (t (let ( (vals (km-int kmexpr :fail-mode fail-mode :target target :rewritep rewritep)) )
    (cond ((singletonp vals) (first vals))
	  (vals (report-error 'user-error
"Expression ~a was expected to return a single value,
but it returned multiple values ~a!
Just taking the first...(~a) ~%" kmexpr vals (first vals))
		(first vals))
	  ((eq fail-mode 'error)
	   (report-error 'user-error "Expression ~a didn't return a value!~%" kmexpr)))))))

;;; ======================================================================

;;; Handle case-sensitivity and quoted morphism table in load-kb expression
;;; (load-kb "foo.km" :verbose t :with-morphism '((a -> 1) (b -> 2)))
(defun process-load-expression (load-expr0)
  (let* ((load-expr1 (sublis '((#$:verbose . :verbose)				; :verbose -> :VERBOSE etc.
			       (#$:eval-instances . :eval-instances)
			       (#$:with-morphism . :with-morphism)
			       (#$:load-patterns . :load-patterns)
			       (#$:reset-kb . :reset-kb)
			       (#$:force-fkm . :force-fkm)
			       (#$:compile . :compile)
			       (#$:include-explanationsp . :include-explanationsp)
			       (#$t . t))
			     load-expr0))
	(load-expr (cons (intern (string-upcase (first load-expr1)) *km-package*) ; (|load-kb| ...) -> (LOAD-KB ...)
			 (rest load-expr1))))
;    (km-format t "load-expr = ~a~%" load-expr)
    (multiple-value-bind
	(result error)
	(eval load-expr)
      (declare (ignore result))
      (cond (error (princ error) (throw 'km-abort (list 'km-abort error))) ; (format t "~/home") gives format error!
	    (t '#$(t))))))

;;; ======================================================================

;;; The association list is a set of pairs of form (pattern function).
;;; Function gets applied to the values of variables in pattern, the
;;; values stored in a list in the order they were encountered
;;; when (depth-first) traversing the km expression.

;;; Below: two alternative ways of embedding Lisp code
;;; `,#'(lambda () ....) 	<- marginally faster, but can't be manipulated
;;; '(lambda (...))
;;; 4.15.99 Changed `(a ,frame with . ,slotsvals) to `(a ,frame with ,@slotsvals), as Lucid problem
;;; for writing out the flattened-out code:
;;; 	(write '`(a ,frame with . ,slotsvals)) -> `(A ,FRAME WITH EXCL::BQ-COMMA SLOTSVALS) = Lucid-specific!!
;;; 	(write '`(a ,frame with ,@slotsvals)) -> `(A ,FRAME WITH ,@SLOTSVALS) = readable by other Lisps

;;; v1.4.0 - order in terms of utility for speed!

;; split this list initialization into 2, since ABCL can't handle such a long structure def
(setf
  *km-handler-alist1*
  '(
;;; [1] NEW: Here make another top level call, so
;;;	(i) the trace is easier to follow during debugging
;;;	(ii) the looping checker jumps in at the right moment
;;; [2] This is a bit of a hack; with looping, e.g. another query higher in the stack for (((a Cat)) && (the cats of Sue)),
;;;     KM may possibly return structured answers e.g. ((a Cat) (the cats of Sue)). Need to remove the non-evaluated ones (urgh).
;;;     See test-suite/restaurant.km for the source of this patch.
;;; [3] New! Remove the transitivity incompleteness described in the user manual
    ( (#$the ?slot #$of ?frameadd)
      (lambda (fmode0 _target slot frameadd)
	(declare (ignore _target))
;	(cond ((neq slot '#$instances) (check-situations-mode))) ; allow query for instances to slip through, for internal (all-instances) queries
	(cond ((structured-slotp slot)
	       (follow-multidepth-path (km-int frameadd :fail-mode fmode0)   ; start-values
				   slot '* :fail-mode fmode0))	     ; target-class = *
	      ((pathp slot)
	       (let ( (eval-slot (km-unique-int slot :fail-mode 'error)) )
		 (km-int `#$(the ,EVAL-SLOT of ,FRAMEADD) :fail-mode fmode0)))
	 (t  ; (km-format t "frameadd = ~a~%" frameadd)
	  (let* ( (fmode (cond ((built-in-aggregation-slot slot) 'fail)
				      (t fmode0)))
; OLD			 (frames (km-int frameadd :fail-mode fmode)) )
; Now we at least see the looping and collect cached values
 			 (frames (cond ((every #'is-simple-km-term (val-to-vals frameadd))		; [4]
;					(km-format t "Infinite recursion avoided for ~a!~%" `#$(the ,SLOT of ,FRAMEADD))
					(remove-dup-instances (val-to-vals frameadd)))		; includes dereferencing
				       (t (km-int frameadd :fail-mode fmode :check-for-looping nil)))) ) 	; [3]
		   (cond ((= *depth* 1) (setq *last-question* `(#$the ,slot #$of ,(vals-to-val frames)))))	; for explanation
		   (cond ((not (equal frames (val-to-vals frameadd)))
			  (remove-if-not #'is-km-term (km-int `#$(the ,SLOT of ,(VALS-TO-VAL FRAMES)) :fail-mode fmode)))	; [1], [2]
			 (t (remove-if-not #'is-km-term (km-multi-slotvals frames slot :fail-mode fmode)))))))) )	; [2]

; No, filter needs to be on ALL retrieved values, not just (the <slot> of <x>) expressions
;		   (let ((vals (cond ((not (equal frames (val-to-vals frameadd)))
;				      (remove-if-not #'is-km-term
;					 (km-int `#$(the ,SLOT of ,(VALS-TO-VAL FRAMES)) :fail-mode fmode))) ; [1], [2]
;				     (t (remove-if-not #'is-km-term
;						       (km-multi-slotvals frames slot :fail-mode fmode)))))) ; [2]
;		     (case slot
;		       (#$nowexists vals)
;		       (t (remove-if-not #'nowexists vals)))))))) )

    ( (#$a ?class)
      (lambda (_fmode target class)
	(declare (ignore  _fmode))
	(list (create-instance class nil :target target))) )

    ( (#$a ?class #$called ?tag)
      (lambda (_fmode target class tag)
	(declare (ignore  _fmode))
	(km-setq '*are-some-tags* t)
	(cond ((km-tagp tag) (list (create-instance class `((#$called ,(VAL-TO-VALS TAG))) :target target)))
	      (t (report-error 'user-error "~a~%    - The tag `~a' must be an atom or a constraint!" `#$(a ,CLASS called ,TAG) tag)))))

    ( (#$a ?class #$uniquely-called ?tag)
      (lambda (_fmode target class tag)
	(declare (ignore  _fmode))
	(km-setq '*are-some-constraints* t)
	(km-setq '*are-some-tags* t)
	(cond ((km-tagp tag) (list (create-instance class `((#$uniquely-called ,(VAL-TO-VALS TAG))) :target target)))
	      (t (report-error 'user-error "~a~%    - The tag `~a' must be an atom or a constraint!" `#$(a ,CLASS uniquely-called ,TAG) tag)))))

    ( (#$a ?class #$with &rest)
      (lambda (_fmode target class slotsvals)
	   (declare (ignore _fmode))
	   (cond ((are-slotsvals slotsvals)
		  (let ( (instance (create-instance class (convert-comments-to-internal-form slotsvals) :target target)) )
		    (cond ((am-in-prototype-mode) (km-int '#$(evaluate-paths))))	; route through interpreter for tracing + loop detection
		    (list instance))))) )

    ( (#$a ?class #$uniquely-called ?tag #$with &rest)
      (lambda (_fmode target class tag slotsvals)
	   (declare (ignore _fmode))
	   (km-setq '*are-some-constraints* t)
	   (km-setq '*are-some-tags* t)
	   (cond ((not (km-tagp tag))
		  (report-error 'user-error "~a~%   - The tag `~a' must be an atom or a constraint!" `#$(a ,CLASS uniquely-called ,TAG with ,@SLOTSVALS) tag))
		 ((are-slotsvals slotsvals)
		  (let ( (instance (create-instance class (cons `(#$uniquely-called ,(VAL-TO-VALS TAG))
								(convert-comments-to-internal-form slotsvals))
						    :target target)) )
		    (cond ((am-in-prototype-mode) (km-int '#$(evaluate-paths))))	; route through interpreter for tracing + loop detection
		    (list instance))))) )

    ( (#$a ?class #$called ?tag #$with &rest)
      (lambda (_fmode target class tag slotsvals)
	   (declare (ignore  _fmode))
	   (km-setq '*are-some-tags* t)
	   (cond ((not (km-tagp tag))
		  (report-error 'user-error "~a~%   - The tag `~a' must be an atom or a constraint!" `#$(a ,CLASS called ,TAG with ,@SLOTSVALS) tag))
		 ((are-slotsvals slotsvals)
		  (let ( (instance (create-instance class (cons `(#$called ,(VAL-TO-VALS TAG))
								(convert-comments-to-internal-form slotsvals))
						    :target target)) )
		    (cond ((am-in-prototype-mode) (km-int '#$(evaluate-paths))))	; route through interpreter for tracing + loop detection
		    (list instance))))) )

;;; ======================================================================
;;;		PROTOTYPES
;;; ======================================================================

    ( (#$a-prototype ?class)
      (lambda (fmode target class)
	(km-int `#$(a-prototype ,CLASS with) :fail-mode fmode :target target :rewritep t)) )  ; rewrite, errors caught below

    ( (#$a-prototype ?class #$with &rest)
      (lambda (_fmode _target class slotsvals)
	   (declare (ignore  _fmode _target))
	   (cond ((am-in-local-situation)
		  (report-error 'user-error "Can't enter prototype mode when in a Situation!~%"))
	         ((am-in-local-theory)
		  (report-error 'user-error "Can't enter prototype mode when in a Theory!~%"))
		 ((am-in-prototype-mode)
		  (report-error 'user-error
	    "~a~%Attempt to enter prototype mode while already in prototype mode (not allowed)!~%Perhaps you are missing an (end-prototype)?"
	    			`#$(a-prototype ,CLASS with ,@SLOTSVALS)))
	         ((are-slotsvals slotsvals)
		  (new-context)
		  (km-setq '*curr-prototype*
			   (create-instance class
					     `#$((prototype-of (,CLASS))
;						 ,(COND (SLOTSVALS `(prototype-scope ('(a ,CLASS with ,@SLOTSVALS))))
						 ,(COND (SLOTSVALS `(prototype-scope ((the-class ,CLASS with ,@SLOTSVALS))))
							(T `(prototype-scope (,CLASS))))
						 ,@SLOTSVALS)
					     :prefix-string *proto-marker-string*	; ie. "_Proto"
					     :bind-selfp nil))				; bind-selfp = nil - PRESERVE "Self" in prototype-scope
		  (add-val *curr-prototype* '#$prototype-participants *curr-prototype*)		; consistency
		  (km-setq '*are-some-prototypes* t)		; optimization flag
		  (cond ((null slotsvals) (add-to-prototype-definition *curr-prototype* `(#$a-prototoype ,class)))
			(t (add-to-prototype-definition *curr-prototype* `(#$a-prototype ,class #$with ,@slotsvals))))
		  (list *curr-prototype*)))) )

    ( (#$end-prototype)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(km-setq '*curr-prototype* nil)
	(global-situation)
	(new-context)
	'#$(t)) )

    ( (#$clone ?expr)
      (lambda (_fmode _target expr)
	(declare (ignore _fmode _target))
	(let ( (source (km-unique-int expr :fail-mode 'error)) )
	  (cond (source (list (clone source)))))) )

    ( (#$evaluate-paths)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(eval-instances)
	'#$(t)) )

    ( (#$default-fluent-status &rest)
      (lambda (_fmode _target rest)
	(declare (ignore _fmode _target))
	(default-fluent-status (first rest))) )

;;; ----------------------------------------------------------------------
;;; Type constraints don't get evaluated.

    ( (#$must-be-a ?class)
      (lambda (_fmode _target _class) (declare (ignore  _fmode _target _class)) (note-are-constraints) nil))
    ( (#$possible-values ?values)
      (lambda (_fmode _target _values) (declare (ignore  _fmode _target _values)) (note-are-constraints) nil))
    ( (#$excluded-values ?values)
      (lambda (_fmode _target _values) (declare (ignore  _fmode _target _values)) (note-are-constraints) nil))

    ( (#$must-be-a ?class #$with &rest)
      (lambda (_fmode _target _class slotsvals)
	   (declare (ignore  _fmode _target _class))
	   (are-slotsvals slotsvals)				; Syntax check
	   (note-are-constraints)
	   nil))

    ( (#$mustnt-be-a ?class)
      (lambda (_fmode _target _class)
	(declare (ignore  _fmode _target _class))
	(note-are-constraints) nil) )

    ( (#$mustnt-be-a ?class #$with &rest)
      (lambda (_fmode _target _class slotsvals)
	   (declare (ignore  _fmode _target _class))
	   (are-slotsvals slotsvals)				; Syntax check
	   (note-are-constraints)
	   nil))

;;; New 1.4.0-beta10:
    ( (<> ?val) ; ie. means isn't val
      (lambda (_fmode _target _val) (declare (ignore  _fmode _target _val)) (note-are-constraints) nil))

    ( (#$no-inheritance) (lambda (_fmode _target) (declare (ignore _fmode _target))) nil )

    ( (#$constraint ?expr)			; constraints tested elsewhere
      (lambda (_fmode _target _expr)
	(declare (ignore _fmode _target _expr))
	(note-are-constraints) nil) )

    ( (#$set-constraint ?expr)			; constraints tested elsewhere
      (lambda (_fmode _target _expr)
	(declare (ignore _fmode _target _expr))
	(note-are-constraints) nil) )

    ( (#$set-filter ?expr)			; constraints tested elsewhere
      (lambda (_fmode _target _expr)
	(declare (ignore _fmode _target _expr))
	(note-are-constraints) nil) )

    ( (#$at-least ?n ?class)
      (lambda (_fmode _target _n _class)
	(declare (ignore _fmode _target _n _class))
	(note-are-constraints) nil) )

    ( (#$at-most ?n ?class)
      (lambda (_fmode _target _n _class)
	(declare (ignore _fmode _target _n _class))
	(note-are-constraints) nil) )

    ( (#$exactly ?n ?class)
      (lambda (_fmode _target _n _class)
	(declare (ignore _fmode _target _n _class))
	(note-are-constraints) nil) )

    ( (#$sanity-check ?expr)			; toggleable wrapper around constraints
      (lambda (fmode target expr)
	(cond (*sanity-checks* (km-int expr :fail-mode fmode :target target))
	 (t '#$(t)))) )

    ((#$retain-expr ?expr)
     (lambda (fmode target expr)
       (let ((instance (fourth target))
	     (slot (second target)))
	 (cond ((or (null target)
		    (notany #'(lambda (isv-explanation)
				(let ((explanation (explanation-in isv-explanation)))
				  (equal explanation `(#$retain-expr ,expr))))
			    (get-all-explanations instance slot)))
		(km-int expr :fail-mode fmode :target target))))) )

    ; ----------------------------------------

    ; ============================
    ; AUGMENTING MEMBER PROPERTIES
    ; ============================

    ( (#$every ?cexpr #$has &rest)
      (lambda (_fmode _target cexpr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (class (km-unique-int cexpr :fail-mode 'error)) )
	     (cond ((not (kb-objectp class))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a class name.~%"
				  `(#$every ,cexpr #$has ,@slotsvals) cexpr))
		   ((are-slotsvals slotsvals)		; check
		    (let* ( (slotsvals00 (cond (*record-sources* (annotate-slotsvals slotsvals (make-source class)))
					       (t slotsvals)))
			    (slotsvals0 (convert-comments-to-internal-form slotsvals00)) )
		      (add-slotsvals class slotsvals0 :facet 'member-properties))
		    (cond ((and (assoc '#$assertions slotsvals)
				(not (member class *classes-using-assertions-slot*)))
			   (km-setq '*classes-using-assertions-slot* (cons class *classes-using-assertions-slot*))))
		    (mapc #'un-done (all-instances class))
		    (list class))))))

    ( (#$every ?cexpr #$also-has &rest)
      (lambda (_fmode _target cexpr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (class (km-unique-int cexpr :fail-mode 'error)) )
	     (cond ((not (kb-objectp class))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a class name.~%"
				  `(#$every ,cexpr #$also-has ,@slotsvals) cexpr))
		   ((are-slotsvals slotsvals)		; check
		    (let* ( (slotsvals00 (cond (*record-sources* (annotate-slotsvals slotsvals (make-source class)))
					       (t slotsvals)))
			    (slotsvals0 (convert-comments-to-internal-form slotsvals00)) )
		      (add-slotsvals class slotsvals0 :facet 'member-properties :combine-values-by 'appending))
		    (cond ((and (assoc '#$assertions slotsvals)
				(not (member class *classes-using-assertions-slot*)))
;			   (setq *classes-using-assertions-slot* (cons class *classes-using-assertions-slot*))))
;			   (make-transaction `(setq *classes-using-assertions-slot* ,(cons class *classes-using-assertions-slot*)))))
			   (km-setq '*classes-using-assertions-slot* (cons class *classes-using-assertions-slot*))))
		    (mapc #'un-done (all-instances class))
		    (list class))))))

    ( (#$every ?cexpr #$now-has &rest)
      (lambda (_fmode _target cexpr slotsvals)
	   (declare (ignore _fmode _target))
	   (let ( (class (km-unique-int cexpr :fail-mode 'error)) )
	     (cond ((not (kb-objectp class))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a class name.~%"
				  `(#$every ,cexpr #$now-has ,@slotsvals) cexpr))
		   ((are-slotsvals slotsvals)		; check
		    (let* ( (slotsvals00 (cond (*record-sources* (annotate-slotsvals slotsvals (make-source class)))
					       (t slotsvals)))
			    (slotsvals0 (convert-comments-to-internal-form slotsvals00)) )
		      (add-slotsvals class slotsvals0 :facet 'member-properties :combine-values-by 'overwriting))
		    (cond ((and (assoc '#$assertions slotsvals)
				(not (member class *classes-using-assertions-slot*)))
;			   (setq *classes-using-assertions-slot* (cons class *classes-using-assertions-slot*))))
;			   (make-transaction `(setq *classes-using-assertions-slot* ,(cons class *classes-using-assertions-slot*)))))
			   (km-setq '*classes-using-assertions-slot* (cons class *classes-using-assertions-slot*))))
		    (mapc #'un-done (all-instances class))
		    (list class))))) )

    ; =========================
    ; AUGMENTING OWN PROPERTIES
    ; =========================

    ( (?instance-expr #$has &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(,instance-expr #$has ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals)	; check
		    (add-slotsvals instance (convert-comments-to-internal-form slotsvals))
		    (make-assertions instance slotsvals)
		    (un-done instance)		; In case redefinition	  - now in put-slotsvals; Later: No!!
		    (classify instance :slots-that-changed (mapcar #'slot-in slotsvals))		; Because it's an instance
		    (cond ((am-in-prototype-mode) (km-int '#$(evaluate-paths))))	; route through interpreter for tracing + loop detection
		    (list instance))))) )
    )) ;; end part 1 of list init

(setf
 *km-handler-alist2* ;; part 2 of the list
 '(
    ( (?instance-expr #$also-has &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(,instance-expr #$also-has ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals)	; check
		    (add-slotsvals instance (convert-comments-to-internal-form slotsvals) :combine-values-by 'appending)
		    (un-done instance)		; In case redefinition	  - now in put-slotsvals; Later: No!!
		    (classify instance :slots-that-changed (mapcar #'slot-in slotsvals))		; Because it's an instance
		    (cond ((am-in-prototype-mode) (km-int '#$(evaluate-paths))))	; route through interpreter for tracing + loop detection
		    (list instance))))) )

    ((#$every ?instance-expr #$also-hasnt &rest)
     (lambda (_fmode _target instance-expr slotsvals)
       (declare (ignore  _fmode _target))
       (report-error 'user-error "~a:~%Can't use also-hasnt with an \"every\" expression (can only use it with instances, not classes)~%" `(#$every ,instance-expr #$also-hasnt ,@slotsvals))))

    ;;; USE WITH EXTREME CAUTION
    ( (?instance-expr #$also-hasnt &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(,instance-expr #$also-has ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals) ; check
		    (mapc #'(lambda (slotvals)
			      (let ((slot (slot-in slotvals))
				    (vals (vals-in slotvals)))
				(mapc #'(lambda (val)
					  (delete-val instance slot val))
				      vals)))
			  slotsvals)
		    (un-done instance)	; In case redefinition	  - now in put-slotsvals; Later: No!!
		    (list instance))))) )

;;; New, explicitly for Shaken. The new slotsvals OVERWRITE the old slotsvals, so must be used with extreme caution!
;;; Old inverses will also uninstalled providing they are fully-evaluated KB objects.
    ( (?instance-expr #$now-has &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(,instance-expr #$now-has ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals)	; check
		    (add-slotsvals instance (convert-comments-to-internal-form slotsvals) :combine-values-by 'overwriting)
; Neah, let's assume these things better not change!!
		    (un-done instance)		; In case redefinition	  - now in put-slotsvals; Later: No!!
		    (classify instance)		; Because it's an instance
;#|new|#	    (cond ((am-in-prototype-mode)
;			   ; (eval-instances)
;			   (km-int '#$(evaluate-paths) :fail-mode 'error)))	; new: route through query interpreter for tracing and also loop detection
		    (list instance))))) )

    ;;; ----------------------------------------------------------------------
    ;;;	 UNIFICIATION - now off-load to special procedure in lazy-unify.lisp
    ;;; ----------------------------------------------------------------------

    ( (?xs && &rest)
      (lambda (fmode target xs rest)
	(declare (ignore fmode))
;	(km-format t "xs = ~a~%rest = ~a~%" xs rest)
	(lazy-unify-&-expr `(,xs && ,@rest) :fail-mode 'error :joiner '&& :target target)) )

    ( (?x & &rest)
      (lambda (fmode target x rest)
	(declare (ignore fmode))
	(lazy-unify-&-expr `(,x & ,@rest) :fail-mode 'error :joiner '& :target target)) )

    ( (?xs === &rest)
      (lambda (fmode target xs rest)
	(declare (ignore fmode))
	(lazy-unify-&-expr `(,xs === ,@rest) :fail-mode 'error :joiner '=== :target target)) )

    ( (?x == ?y)
      (lambda (fmode target x y)
	(declare (ignore fmode))
	(lazy-unify-&-expr `(,x == ,y) :fail-mode 'error :joiner '== :target target)) )

    ( (?x /== ?y)
      (lambda (fmode target x y)
	(declare (ignore fmode target))
	(let ( (xv (km-unique-int x :fail-mode 'error))
	       (yv (km-unique-int y :fail-mode 'error)) )
	  (cond ((equal xv yv)
		 (report-error 'user-error "(~a /== ~a): ~a and ~a are the same object!~%"
			       x y x y))
		((kb-objectp xv) (km-int `#$(,XV has (/== (,YV))) :fail-mode 'error))
		((kb-objectp yv) (km-int `#$(,YV has (/== (,XV))) :fail-mode 'error))
		('#$(t))))) )		; two distinct, non-KB objects eg. ("cat" /== "dog")

;;; These variants do eager unification
    ( (?xs &&! &rest)
      (lambda (fmode target xs rest)
	(declare (ignore fmode))
	(lazy-unify-&-expr `(,xs &&! ,@rest) :fail-mode 'error :joiner '&&! :target target)) )

    ( (?x &! &rest)
      (lambda (fmode target x rest)
	(declare (ignore fmode))
	(lazy-unify-&-expr `(,x &! ,@rest) :fail-mode 'error :joiner '&! :target target)) )

;;; NEW VERSION: Avoids creating then deleting the temporary frame
    ( (?x &? ?y)			; *tests* unification. No side effects. Returns a better unification expression if successful.
      (lambda (_fmode target x y)
	(declare (ignore _fmode target))
	(cond ((null x) '#$(t))
	      ((null y) '#$(t))
	      ((existential-exprp y) (let ( (xf (km-unique-int x)) )
					(cond ((null xf) '#$(t))
					      ((unifiable-with-existential-expr xf y) '#$(t)))))
	      ((existential-exprp x) (let ( (yf (km-unique-int y)) )
					(cond ((null yf) '#$(t))
					      ((unifiable-with-existential-expr yf x) '#$(t)))))
	      (t (let ( (xv (km-unique-int x)) )
		   (cond ((null xv) '#$(t))
			 (t (let ( (yv (km-unique-int y)) )
			      (cond ((null yv) '#$(t))
				    ((try-lazy-unify xv yv) '#$(t)))))))))))		; return "t" if successful

;;; SAME, but insist on classes-subsume constraint turned ON...

    ( (?x &+? ?y)			; *tests* unification. No side effects. Returns a better unification expression if successful.
      (lambda (_fmode target x y)
	(declare (ignore _fmode target))
	(cond ((existential-exprp y) (let ( (xf (km-unique-int x)) )
					(cond ((null xf) '#$(t))
					      ((unifiable-with-existential-expr xf y :classes-subsumep t) '#$(t)))))
	      ((existential-exprp x) (let ( (yf (km-unique-int y)) )
					(cond ((null yf) '#$(t))
					      ((unifiable-with-existential-expr yf x :classes-subsumep t) '#$(t)))))
	      (t (let ( (xv (km-unique-int x)) )
		   (cond ((null xv) '#$(t))
			 (t (let ( (yv (km-unique-int y)) )
			      (cond ((null yv) '#$(t))
				    ((try-lazy-unify xv yv :classes-subsumep t) '#$(t)))))))))))		; return "t" if successful

;;; ---------- Unification, but with classes-subsumep constraint turned ON

;;;; Unification, but with classes-subsumep constraint turned ON
;;; If unification fails, it returns NIL but no error is printed out.
;;; &+ is more restricted than & (at least for now), it won't nicely break up nested
;;; expressions.
    ( (?x &+ ?y)
      (lambda (fmode target x y)
	(let ( (unification (lazy-unify-exprs x y :classes-subsumep t :fail-mode fmode :target target)) )
	  (cond (unification (list unification))
		((eq fmode 'error)
		 (report-error 'user-error "Unification (~a &+ ~a) failed!~%" x y))))) )

; No, test first before doing it, else you might leave side effects.
; **NOTE** Unlike &!, &+! *is* allowed to quietly fail
    ((?x &+! ?y)
     (lambda (fmode target x y)
       (cond ((km-int `(,x &+? ,y) :target target :fail-mode fmode) ; must test before doing it,
	      (km-int `(,x &! ,y) :target target :fail-mode 'error)) ; If &+? succeeds, route through query interpreter so pending-equality is seen. &! *must* succeed if &+? succeeds
	     ((eq fmode 'error)
	      (report-error 'user-error "Unification (~a &+! ~a) failed!~%" x y)))))

; Attempt 2
;    ((?x &+! ?y)
;     (lambda (fmode target x y)
;       (cond ((km-int `(,x &+? ,y) :target target :fail-mode fmode) ; must test before doing it,
;	      (let ((unification (lazy-unify-exprs x y :classes-subsumep t :eagerlyp t :fail-mode fmode :target target)) )
;		(cond (unification (list unification))
;		      ((eq fmode 'error)
;		       (report-error 'user-error "Unification (~a &+! ~a) failed!~%" x y))))))))

; Attempt 1
;    ((?x &+! ?y)
;     (lambda (fmode target x y)
;	(let ( (unification (lazy-unify-exprs x y :classes-subsumep t :eagerlyp t :fail-mode fmode :target target)) )
;	  (cond (unification (list unification))
;		((eq fmode 'error)
;		 (report-error 'user-error "Unification (~a &+! ~a) failed!~%" x y))))) )

;;; ----------------------------------------

;;; This is a special case where we do allow delistification.
;;;	"(the x of y) = z" is okay [strictly should be (the x of y) = (:set z)]
;;; [1] In computing yv, the binding of xv may have changed!
    ( (?x = ?y) (lambda (fmode target x y)
		     (declare (ignore target))
		     (let ( (xv (km-int x :fail-mode fmode))
			    (yv (km-int y :fail-mode fmode)) )
		       (cond ((km-set-equal (dereference xv) yv) '(#$t))))) )	; [1]

    ( (?x /= ?y) (lambda (fmode target x y)
		     (declare (ignore target))
		     (let ( (xv (km-int x :fail-mode fmode))
			    (yv (km-int y :fail-mode fmode)) )
		       (cond ((not (km-set-equal (dereference xv) yv)) '(#$t))))) )	; [1]

    ( (#$the ?class ?slot #$of ?frameadd)
      (lambda (fmode0 target class slot frameadd)
;	(cond ((neq slot '#$instances) (check-situations-mode))) ; allow query for instances to slip through, for internal (all-instances) queries
	   (cond ((structured-slotp slot)
		  (follow-multidepth-path (km-int frameadd :fail-mode fmode0 :target target :rewritep t)   ; start-values
				      slot class :fail-mode fmode0))
		 ((pathp slot)
		  (let ( (eval-slot (km-unique-int slot :fail-mode 'error)) )
		    (km-int `#$(the ,CLASS ,EVAL-SLOT of ,FRAMEADD) :fail-mode fmode0 :target target :rewritep t)))
		 (t (let* ( (fmode (cond ((built-in-aggregation-slot slot) 'fail)
					 (t fmode0))) )
		      (vals-in-class (km-int `#$(the ,SLOT of ,FRAMEADD) :fail-mode fmode :target target :rewritep t)
				     class))))) )

;;; ======================================================================
;;;		THEORIES - NEW
;;; ======================================================================

    ( (#$in-theory ?theory-expr)
      (lambda (_fmode _target theory-expr)
	   (declare (ignore _fmode _target))
	   (in-theory theory-expr)) )

    ( (#$in-theory ?theory-expr ?km-expr)
      (lambda (_fmode _target theory-expr km-expr)
	   (declare (ignore _fmode _target))
	   (in-theory theory-expr km-expr)) )

    ( (#$hide-theory ?theory-expr)
      (lambda (_fmode _target theory-expr)
	(declare (ignore _fmode _target))
	(mapc #'hide-theory (km-int theory-expr))
	(cond ((visible-theories))
	      (t '#$(t)))))

    ( (#$see-theory ?theory-expr)
      (lambda (_fmode _target theory-expr)
	(declare (ignore _fmode _target))
	(mapc #'see-theory (km-int theory-expr))
	(visible-theories)) )

    ( (#$end-theory)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(in-situation *global-situation*)) )

    ( (#$visible-theories)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(visible-theories)) )

;;; ======================================================================
;;;		SITUATIONS: Pass these KM commands straight to Lisp
;;; Note if these are issued directly from Lisp, then the KM exprs have to be quoted.
;;; ======================================================================

    ( (#$in-situation ?situation-expr)
      (lambda (_fmode _target situation-expr)
	   (declare (ignore _fmode _target))
	   (in-situation situation-expr)) )

    ( (#$in-situation ?situation (#$the ?slot #$of ?frame))	; special fast handling of this: If
      (lambda (_fmode _target situation slot frame)		; the slot-vals are already computed ([1])
	   (declare (ignore _fmode _target))			; then just do a lookup ([2])
	   (cond ((and (kb-objectp situation)
		       (isa situation '#$Situation)
; APR30		       (already-done frame slot situation))			; [1]
		       (already-done frame slot))			; [1]
#|OLD|#		  (remove-constraints (get-vals frame slot :situation (target-situation situation frame slot))))	; [2]
;#|NEW|#	  (get-vals-in-cache frame slot :situation situation))
		 (t (in-situation situation `#$(the ,SLOT of ,FRAME))))) )

    ( (#$in-situation ?situation-expr ?km-expr)
      (lambda (_fmode _target situation-expr km-expr)
	   (declare (ignore _fmode _target))
	   (in-situation situation-expr km-expr)) )

    ( (#$end-situation)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(in-situation *global-situation*)) )

    ( (#$global-situation)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(in-situation *global-situation*)) )

    ( (#$new-situation)
      (lambda (_fmode _target)
	(declare (ignore _fmode _target))
	(new-situation)) )			; NB returns a singleton list containing the new situation

;;; ----------------------------------------

    ( (#$do ?action-expr)
      (lambda (_fmode _target action-expr)
	   (declare (ignore _fmode _target))
	   (list (do-action action-expr))) )			; NB do-action returns a SINGLE value (a situation), not a list.

    ( (#$do ?action-expr ?next-situation)
      (lambda (_fmode _target action-expr next-situation)
	(declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (list (do-action action-expr :next-situation next-situation))))) )

    ( (#$do-and-next ?action-expr)
      (lambda (_fmode _target action-expr)
	   (declare (ignore _fmode _target))
	   (list (do-action action-expr :change-to-next-situation t))) )

    ( (#$do-and-next ?action-expr ?next-situation)
      (lambda (_fmode _target action-expr next-situation)
	   (declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (list (do-action action-expr :next-situation next-situation :change-to-next-situation t))))) )

;;; New
    ( (#$try-do ?action-expr)
      (lambda (_fmode _target action-expr)
	   (declare (ignore _fmode _target))
	   (list (do-action action-expr :test-or-assert-pcs 'test))) )		; NB do-action returns a SINGLE value (a situation), not a list.

    ( (#$try-do ?action-expr ?next-situation)
      (lambda (_fmode _target action-expr next-situation)
	(declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (list (do-action action-expr :next-situation next-situation :test-or-assert-pcs 'test))))) )

    ( (#$try-do-and-next ?action-expr)
      (lambda (_fmode _target action-expr)
	   (declare (ignore _fmode _target))
	   (list (do-action action-expr :change-to-next-situation t :test-or-assert-pcs 'test))) )

    ( (#$try-do-and-next ?action-expr ?next-situation)
      (lambda (_fmode _target action-expr next-situation)
	(declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (list (do-action action-expr :next-situation next-situation :change-to-next-situation t :test-or-assert-pcs 'test))))) )

    ( (#$do-concurrently ?action-expr)
     (lambda (_fmode _target action-expr)
       (declare (ignore _fmode _target))
       (let* ((actions (km-int action-expr))
	      (next-situation (km-unique-int `#$(do ,(FIRST ACTIONS)))))
	 (mapc #'(lambda (action) (km-int `#$(do ,ACTION ,NEXT-SITUATION))) (rest actions))
	 (list next-situation))) )

    ( (#$do-concurrently ?action-expr ?next-situation)
     (lambda (_fmode _target action-expr next-situation)
       (declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (let ((actions (km-int action-expr)))
		   (mapc #'(lambda (action) (km-int `#$(do ,ACTION ,NEXT-SITUATION))) actions)
		   (list next-situation))))) )

    ( (#$do-concurrently-and-next ?action-expr)
     (lambda (_fmode _target action-expr)
       (declare (ignore _fmode _target))
       (let* ((actions (km-int action-expr))
	      (next-situation (km-unique-int `#$(do ,(FIRST ACTIONS)))))
	 (mapc #'(lambda (action) (km-int `#$(do ,ACTION ,NEXT-SITUATION))) (rest actions))
	 (in-situation next-situation)
	 (list next-situation))) )

    ( (#$do-concurrently-and-next ?action-expr ?next-situation)
     (lambda (_fmode _target action-expr next-situation)
       (declare (ignore _fmode _target))
	(cond ((not (instance-of next-situation '#$Situation))
	       (report-error 'user-error "(do ~a ~a): ~a should be an instance of Situation, but isn't!~%"
			     action-expr next-situation next-situation))
	      (t (let ((actions (km-int action-expr)))
		   (mapc #'(lambda (action) (km-int `#$(do ,ACTION ,NEXT-SITUATION))) actions)
		   (in-situation next-situation)
		   (list next-situation))))) )

;;; Now returns the list of successful actions
    ( (#$do-script ?script)
      (lambda (fmode target script)
	   (km-int `#$(forall (the actions of ,SCRIPT) (do-and-next It))
	       :fail-mode fmode :target target :rewritep t)) )

    ( (#$do-plan ?plan-instance-expr)
      (lambda (_fmode _target plan-instance-expr)
	(declare (ignore _fmode _target))
	(let ( (plan-instance (km-unique plan-instance-expr)) )
	  (do-plan plan-instance))) )			; defined in sadl.lisp

;;; ----------------------------------------

;;; Should even work for constraints
   ( (#$assert ?triple-expr)
      (lambda (_fmode _target triple-expr)
	(declare (ignore _fmode _target))
	(let ( (triple (km-unique-int triple-expr)) )
	  (cond ((not (km-triplep triple))
		 (report-error 'user-error "(assert ~a): ~a should evaluate to a triple! (evaluated to ~a instead)!~%"
			       triple-expr triple))
		(t (km-int `#$(,(ARG1OF TRIPLE) has (,(ARG2OF TRIPLE) ,(VAL-TO-VALS (ARG3OF TRIPLE)))) :fail-mode 'error))))) )

    ( (#$is-true ?triple-expr)
      (lambda (_fmode _target triple-expr)
	(declare (ignore _fmode _target))
	(let* ( (triple (km-unique-int triple-expr)) )
	  (cond
	   ((not (km-triplep triple))
	    (report-error 'user-error "(is-true ~a): ~a should evaluate to a triple! (evaluated to ~a instead)!~%"
			  triple-expr triple))
	   ((comparison-operator (arg2of triple))
	    (km-int `#$(,(SECOND TRIPLE) ,(THIRD TRIPLE) ,(FOURTH TRIPLE))))
	   (t (let ( (frame (km-unique-int (second triple) :fail-mode 'error))
		     (slot  (km-unique-int (third triple) :fail-mode 'error))
		     (value (fourth triple)) )			; don't evaluate this!
		(cond
		 ((null value) '#$(t))
		 ((km-int `#$(,FRAME is '(a Thing with (,SLOT (,VALUE)))))))))))) )

;		 ((constraint-exprp value)
;		  (km-int `#$(,FRAME &? (a Thing with (,SLOT (,VALUE))))))
;		 (t (km-int `#$((the ,SLOT of ,FRAME) includes ,VALUE))))))))) )

    ( (#$all-true ?triples-expr)
      (lambda (_fmode _target triples-expr)
	(declare (ignore _fmode _target))
	(let ( (triples (km-int triples-expr)) )
	  (cond ((every #'(lambda (triple)
			    (km-int `#$(is-true ,TRIPLE)))
			triples)
		 '#$(t))))))

    ( (#$some-true ?triples-expr)
      (lambda (_fmode _target triples-expr)
	(declare (ignore _fmode _target))
	(let ( (triples (km-int triples-expr)) )
	  (cond ((some #'(lambda (triple)
			   (km-int `#$(is-true ,TRIPLE)))
		       triples)
		 '#$(t))))))

;;; ----------------------------------------

    ( #$(next-situation)
	(lambda (_fmode _target)
	     (declare (ignore _fmode _target))
	     (cond ((am-in-local-situation) (list (do-action nil :change-to-next-situation t)))
		   (t (report-error 'user-error "Can only do (next-situation) from within a situation!~%")))))

    ( #$(curr-situation)
	(lambda (_fmode _target)
	     (declare (ignore _fmode _target))
	     (list (curr-situation))) )

    ( (#$ignore-result ?expr)		; return t always
      (lambda (fmode target expr)
	(declare (ignore fmode target))
	(km-int expr) nil))

    ( (#$ignore ?expr)		; return t always
      (lambda (fmode target expr)
	(declare (ignore fmode target expr))
	nil))

    ; Important v1.3.8 addition!
    ; expr should be an assertional expression
    ( (#$in-every-situation ?situation-class ?expr)
      (lambda (fmode target situation-class km-expr)
	   (cond ((not (is-subclass-of situation-class '#$Situation))
		  (report-error 'user-error "~a:~%   Can't do this! (~a is not a subclass of Situation!)~%"
				`#$(in-every-situation ,SITUATION-CLASS ,KM-EXPR) situation-class))
		 (t (let ( (modified-expr (sublis '#$((TheSituation . #,Self) (Self . SubSelf)) km-expr)) )
		      (km-int `#$(in-situation ,*GLOBAL-SITUATION*
				(every ,SITUATION-CLASS has (assertions (',MODIFIED-EXPR)))) :fail-mode fmode
						:target target :rewritep t))))) )

;;; ======================================================================
;;;		CONTEXTS - Very experimental!!
;;; These are distinct from situations. A situation is a version of the KB.
;;; A context is where just the participant instances are visible.
;;; ======================================================================

    ( #$(new-context)
	(lambda (_fmode _target)
	     (declare (ignore _fmode _target))
	     (clear-obj-stack)			; NEW. Let obj-stack be the context
	     '#$(t)) )

;;; ======================================================================
;;;	the ordering of the remaining handers is arbitrary
;;; ======================================================================

;;; ========================================
;;;	QUICK SEARCH OF THE STACK (previously was "the" rather than "that")
;;; ========================================

;;; Now merged into the single framework of subsumption checking.
    ( (#$thelast ?frame)
      (lambda (_fmode _target frame) (declare (ignore  _fmode _target))
	   (let ( (last-instance (search-stack frame)) )
	     (cond (last-instance (list last-instance))))) )

;;; ========================================
;;;  FIND OBJECTS BY SUBSUMPTION CHECKING
;;; ========================================

    ( (#$every ?frame)
      (lambda (fmode target frame) (km-int `(#$every ,frame #$with) :fail-mode fmode :target target :rewritep t)) )

    ( (#$every ?frame #$with &rest)
      (lambda (_fmode _target frame slotsvals)
	   (declare (ignore  _fmode _target))
	   (cond
	    ((are-slotsvals slotsvals)
	     (let ( (existential-expr
		          (cond ((and (null slotsvals) (pathp frame)) 	  ; eg. (the (porter owns car))
				 (path-to-existential-expr frame))
				(t `(#$a ,frame #$with ,@slotsvals)))) )
	       (find-subsumees-on-object-stack existential-expr))))) )

;;; (the ...)  -- expects a unique answer

;;; REDEFINITIONS:
;;;	(the ...) -> (find-the ...)
;;;	(forc (the ...)) -> (the ...)

;;; 2.29.00 - the below is more verbose,  to give better error messages during debugging.
;;; (The earlier version just send (the X) -> (the X with ...) -> (km-unique-int (every X with ...)), but then error messages were unintuitive)

    ( (#$the ?frame)
      (lambda (fmode target frame)
	(declare (ignore fmode target))
	(let ( (answer (km-int `(#$every ,frame))) )
	  (cond ((null answer)
		 (report-error 'user-error "No values found for expression ~a!~%" `#$(the ,FRAME)))
		((not (singletonp answer))
		 (report-error 'user-error "Expected a single value for expression ~a, but found multiple values ~a!~%" `#$(the ,FRAME) answer))
		(t answer)))))

    ( (#$the ?frame #$with &rest)
      (lambda (fmode target frame slotsvals)
	(declare (ignore fmode target))
	   (let ( (answer (km-int `(#$every ,frame #$with ,@slotsvals))) )
	     (cond ((null answer)
		    (report-error 'user-error "No values found for expression ~a!~%" `#$(the ,FRAME with ,@SLOTSVALS)))
		   ((not (singletonp answer))
		    (report-error 'user-error "Expected a single value for expression ~a, but found multiple values ~a!~%"
				  `#$(the ,FRAME with ,@SLOTSVALS) answer))
		   (t answer)))))

;;; Find-or-create Three forms for forc:
;;; (forc (the (porter owns car)))		; (forc (the ...)) and (forc (a ...)) are synonymous
;;; (forc (the car with (owns-by (porter))))
;;; (forc (porter owns car)

;;; Rewrites, to allow path notation to be used...
    ( (#$the+ ?slot #$of ?frameadd)
      (lambda (_fmode target slot frameadd)
	(declare (ignore _fmode))
	(km-int `#$(the+ Thing with (,(INVERT-SLOT SLOT) (,FRAMEADD))) :fail-mode 'error :target target :rewritep t)))

    ( (#$the+ ?class ?slot #$of ?frameadd)
      (lambda (_fmode target class slot frameadd)
	(declare (ignore _fmode))
	(km-int `#$(the+ ,CLASS with (,(INVERT-SLOT SLOT) (,FRAMEADD))) :fail-mode 'error :target target :rewritep t)))

   ( (#$the+ ?frame)
     (lambda (fmode target frame) (km-int `(#$the+ ,frame #$with) :fail-mode fmode :target target :rewritep t)) )

    ( (#$the+ ?frame #$with &rest)
      (lambda (_fmode _target frame slotsvals)
	    (declare (ignore  _fmode _target))
;	    (cond
;	     ((km-int `(#$the ,frame #$with ,@slotsvals)))	  ; OLD: (the ... with ...) *always* generates error on failure, so bypass this.
	    (let ( (val (km-unique-int `(#$every ,frame #$with ,@slotsvals))) )	; NEW		; PS don't surpress error for (the ...)!
	      (cond
	       (val (list val))
	       ((are-slotsvals slotsvals)
		(let ( (existential-expr
			(cond ((and (null slotsvals) (pathp frame)) 	  ; eg. (a (porter owns car))
			       (path-to-existential-expr frame))
			      (t `(#$a ,frame #$with ,@slotsvals)))) )
		  (mapcar #'eval-instance (km-int existential-expr :fail-mode 'error))))))) )	; [1]

   ( (#$a+ &rest)							; a+ is synonym for the+
     (lambda (fmode target rest) (km-int `(#$the+ ,@rest) :fail-mode fmode :target target :rewritep t)) )

;;; [1] above: Do an eval-instance forces inverses in! For example, doing
;;;    (the+ Leg with (part-of ((the Dog with (owned-by (Bruce))))))
;;; should not just return _Leg2, but also add (Bruce owns _Dog3), and (_Dog3 parts _Leg2)

    ; ----------------------------------------

    ; ==========================
    ; DEFINING MEMBER PROPERTIES
    ; ==========================

    ( (#$every ?cexpr #$has-definition &rest)
      (lambda (_fmode _target cexpr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (class (km-unique-int cexpr :fail-mode 'error)) )
	     (cond ((not (kb-objectp class))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a class name.~%"
				  `(#$every ,cexpr #$has-definition ,@slotsvals) cexpr))
		   ((are-slotsvals slotsvals)
		    (let* ((slotsvals00 (cond (*record-sources* (annotate-slotsvals slotsvals (make-source class)))
					       (t slotsvals)))
			   (slotsvals0 (convert-comments-to-internal-form slotsvals00))
			   (parents-of-defined-concept
			    (desource+decomment (vals-in (assoc '#$instance-of slotsvals0)) :delistifyp nil)) )
		      (cond ((not (every #'kb-objectp parents-of-defined-concept))
			     (report-error 'user-error "~a~%The `instance-of' slot-filler(s) in a has-definition must be atomic class name(s) only.~%"
					   `(#$every ,cexpr #$has-definition ,@slotsvals0)))
			    ((null parents-of-defined-concept)
			     (report-error 'user-error
					   "~a~%You must specify an `instance-of' slot value for a has-definition, pointing to the parent class(es)!~%"
					   `(#$every ,cexpr #$has-definition ,@slotsvals0)))
			    (t (add-slotsvals class slotsvals0 :facet 'member-definition)
			       (point-parents-to-defined-concept class parents-of-defined-concept 'member-definition)
			       (km-setq '*are-some-definitions* t)
			       (mapc #'un-done (all-instances class))
			       (list class)))))))) )

;;; Note: Unlike now-has, we clobber *all* the slots, not just the ones mentioned in the definition
   ( (#$every ?cexpr #$now-has-definition &rest)
      (lambda (_fmode _target cexpr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (class (km-unique-int cexpr :fail-mode 'error)) )
	     (cond ((not (kb-objectp class))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a class name.~%"
				  `(#$every ,cexpr #$now-has-definition ,@slotsvals) cexpr))
		   ((are-slotsvals slotsvals)
		    (let* ((slotsvals00 (cond (*record-sources* (annotate-slotsvals slotsvals (make-source class)))
					       (t slotsvals)))
			   (slotsvals0 (convert-comments-to-internal-form slotsvals00))
			   (parents-of-defined-concept
			    (desource+decomment (vals-in (assoc '#$instance-of slotsvals0)) :delistifyp nil)) )
		      (cond ((not (every #'kb-objectp parents-of-defined-concept))
			     (report-error 'user-error "~a~%The `instance-of' slot-filler(s) in a now-has-definition must be atomic class name(s) only.~%"
					   `(#$every ,cexpr #$now-has-definition ,@slotsvals0)))
			    ((and (null parents-of-defined-concept)
				  slotsvals0) ; But (every X now-has-definition) is ok as a way to REMOVE a definition
			     (report-error 'user-error
					   "~a~%You must specify an `instance-of' slot value for a now-has-definition, pointing to the parent class(es)!~%"
					   `(#$every ,cexpr #$now-has-definition ,@slotsvals0)))

			    (t ; [1] Delete old definition:
			       (let ((member-definition-parents (get-vals class '#$instance-of :facet 'member-definition)))
				 (cond (member-definition-parents
					(unpoint-parents-to-defined-concept class member-definition-parents 'member-definition))))
			       (mapc #'(lambda (situation)
					 (mapc #'(lambda (slotvals)
						   (let ((slot (slot-in slotvals)))
						     (put-vals class slot nil :facet 'member-definition :situation situation)))
					       (get-slotsvals class :situation situation :facet 'member-definition)))
				     (all-situations-and-theories))

			       ; [2] Assert new definition. NB if parents-of-defined-concept is NIL, then there is no new definition.
			       (cond (parents-of-defined-concept ; might be NIL if you are DELETING a definition
				      (add-slotsvals class slotsvals0 :facet 'member-definition)
				      (point-parents-to-defined-concept class parents-of-defined-concept 'member-definition)
				      (km-setq '*are-some-definitions* t)
				      (mapc #'un-done (all-instances class))))
			       (list class)))))))) )

    ; =======================
    ; DEFINING OWN PROPERTIES
    ; =======================

    ( (?instance-expr #$has-definition &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(#$every ,instance-expr #$has-definition ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals)	; check
		    (let* ((slotsvals0 (desource+decomment slotsvals)) ; Can't handle comments on instances yet, so strip
			   				 ; them off and throw them out, unlike for (every ... has-def...)
			   (parents-of-defined-concept (vals-in (assoc '#$instance-of slotsvals0))))
		      (cond ((not (every #'kb-objectp parents-of-defined-concept))
			     (report-error 'user-error "~a~%The `instance-of' slot-filler(s) in a has-definition must be atomic class name(s) only.~%"
					   `(,instance-expr #$has-definition ,@slotsvals0)))
			    ((null parents-of-defined-concept)
			     (report-error 'user-error
					   "~a~%You must specify an `instance-of' slot value for a has-definition, pointing to the parent class(es)!~%"
					   `(,instance-expr #$has-definition ,@slotsvals0)))
			    (t (add-slotsvals instance slotsvals0 :facet 'own-definition)
			       (point-parents-to-defined-concept instance parents-of-defined-concept 'own-definition)
			       (km-setq '*are-some-definitions* t)
			       (un-done instance)		; In case redefinition	- now in put-slotsvals; Later: no!!!
			       (classify instance :slots-that-changed (mapcar #'slot-in slotsvals))		; Because it's an instance
			       (list instance)))))))) )

    ( (?instance-expr #$now-has-definition &rest)
      (lambda (_fmode _target instance-expr slotsvals)
	   (declare (ignore  _fmode _target))
	   (let ( (instance (km-unique-int instance-expr :fail-mode 'error)) )
	     (cond ((not (kb-objectp instance))
		    (report-error 'user-error "~a~%~a isn't/doesn't evaluate to a KB object name.~%"
				  `(#$every ,instance-expr #$now-has-definition ,@slotsvals) instance-expr))
		   ((are-slotsvals slotsvals)	; check
		    (let* ((slotsvals0 (desource+decomment slotsvals)) ; Can't handle comments on instances yet, so strip
			   				 ; them off and throw them out, unlike for (every ... now-has-def...)
			   (parents-of-defined-concept (vals-in (assoc '#$instance-of slotsvals0))))
		      (cond ((not (every #'kb-objectp parents-of-defined-concept))
			     (report-error 'user-error "~a~%The `instance-of' slot-filler(s) in a now-has-definition must be atomic class name(s) only.~%"
					   `(,instance-expr #$now-has-definition ,@slotsvals0)))
			    ((and (null parents-of-defined-concept)
				  slotsvals0)
			     (report-error 'user-error
					   "~a~%You must specify an `instance-of' slot value for a now-has-definition, pointing to the parent class(es)!~%"
					   `(,instance-expr #$now-has-definition ,@slotsvals0)))

			    (t ; [1] Delete old definition:
			       (let ((own-definition-parents (get-vals instance '#$instance-of :facet 'own-definition)))
				 (cond (own-definition-parents
					(unpoint-parents-to-defined-concept instance own-definition-parents 'own-definition))))
			       (mapc #'(lambda (situation)
					 (mapc #'(lambda (slotvals)
						   (let ((slot (slot-in slotvals))
							 (vals (vals-in slotvals)))
						     (uninstall-inverses instance slot vals situation)
						     (put-vals instance slot nil :facet 'own-definition :situation situation)))
					       (get-slotsvals instance :situation situation :facet 'own-definition)))
				     (all-situations-and-theories))

			       ; [2] Assert new definition. NB if parents-of-defined-concept is NIL, then there is no new definition.
			       (cond (parents-of-defined-concept ; might be NIL if you are DELETING a definition
				      (add-slotsvals instance slotsvals0 :facet 'own-definition)
				      (point-parents-to-defined-concept instance parents-of-defined-concept 'own-definition)
				      (km-setq '*are-some-definitions* t)
				      (un-done instance) ; In case redefinition	- now in put-slotsvals; Later: no!!!
				      (classify instance :slots-that-changed (mapcar #'slot-in slotsvals)))) ; Because it's an instance
			       (list instance)))))))) )

   ; ----------------------------------------

    ( (#$if ?condition #$then ?action)
      (lambda (fmode target condition action)
	   (km-int `(#$if ,condition #$then ,action #$else nil) :fail-mode fmode :target target :rewritep t)) )

    ( (#$if ?condition #$then ?action #$else ?altaction)
      (lambda (fmode target condition action altaction)
	(declare (ignore target))
	   (let ( (test-result (km-int condition)) )
	     (cond ((not (member test-result '#$(NIL f F))) (km-int action :fail-mode fmode))
		   (t (km-int altaction :fail-mode fmode))))))

    ( (?x > ?y) (lambda (_fmode _target x y)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval))
			      (cond ((> xval yval) '#$(t))))))))

    ( (?x < ?y) (lambda (_fmode _target x y)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval))
			      (cond ((< xval yval) '#$(t))))))))

    ( (?x >= ?y) (lambda (_fmode _target x y)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval))
			      (cond ((>= xval yval) '#$(t))))))))

    ( (?x <= ?y) (lambda (_fmode _target x y)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval))
			      (cond ((<= xval yval) '#$(t))))))))

    ( (?x = ?y +/- ?z) (lambda (_fmode _target x y z)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error))
			    (zval (km-unique-int z :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval) (numberp zval))
			      (cond ((<= (abs (- xval yval)) (abs zval)) '#$(t))))))) )

    ( (?x = ?y +/- ?z %) (lambda (_fmode _target x y z)
		     (declare (ignore  _fmode _target))
		     (let ( (xval (km-unique-int x :fail-mode 'error))
			    (yval (km-unique-int y :fail-mode 'error))
			    (zval (km-unique-int z :fail-mode 'error)) )
		       (cond ((and (numberp xval) (numberp yval) (numberp zval))
			      (cond ((<= (abs (- xval yval)) (* (max (abs xval) (abs yval)) (abs zval) 0.01)) '#$(t))))))) )

    ; ----------------------------------------

    ( (?x #$and &rest)
      (lambda (_fmode _target x rest)
	(declare (ignore  _fmode _target))
	(cond ((and (listp x)
		    (= (length x) 3)
		    (eq (second x) '==))		; special handling for ((?x == <expr>) and ...)
	       (let* ( (xx (first x))
		       (yy (third x)) )
		 (cond ((and (km-varp xx)
			     (km-varp yy))
			(km-int (subst xx yy rest)))		; or perhaps should be an error
		       ((km-varp xx) (km-int (subst (vals-to-val (km-int yy)) xx rest)))
		       ((km-varp yy) (km-int (subst (vals-to-val (km-int xx)) yy rest)))
		       ((and (lazy-unify-&-expr `(,xx == yy) :fail-mode 'error :joiner '==)
			     (km-int rest))))))
	      (t (and (km-int x)
		      (km-int rest))))) )

    ( (?x #$or &rest) (lambda (_fmode _target x y)
			 (declare (ignore  _fmode _target))
			 (or (and (not (on-goal-stackp x))
				  (km-int x))
			     (km-int y))) )

    ( (#$not ?x) (lambda (_fmode _target x)
		      (declare (ignore  _fmode _target))
		      (cond ((not (km-int x)) '#$(t)))) )

    ( (#$numberp ?x) (lambda (_fmode _target x)
			  (declare (ignore  _fmode _target))
			  (cond ((numberp (km-unique-int x)) '#$(t)))) )

;;; ======================================================================
;;;		SUBSUMPTION TESTING
;;; ======================================================================

    ( (?x #$is-subsumed-by ?y)
      (lambda (fmode target x y)
	(km-int `(,y #$subsumes ,x) :fail-mode fmode :target target :rewritep t)) )

    ( (?x #$subsumes ?y)
      (lambda (_fmode _target x y)
	   (declare (ignore  _fmode _target))
	   (let ( (yv (km-int y)) )
	     (cond ((null yv) '#$(t))
		   (t (let ( (xv (km-int x)) )
			(cond ((and (not (null xv))
				    (subsumes xv yv))
			       '#$(t)))))))))

    ( (?x #$is-covered-by ?y)
      (lambda (fmode target x y)
	(km-int `(,y #$covers ,x) :fail-mode fmode :target target :rewritep t)) )

; replace with generalized isa
;    ( (?x #$covers ?y)
;      (lambda (_fmode x y)
;	   (declare (ignore  _fmode))
;	   (let ( (yv (km-unique-int y)) )
;	     (cond ((null yv) '#$(t))
;		   (t (let ( (xv (km-int x)) )
;			(cond ((and (not (null xv))
;				    (covers xv yv))
;			       '#$(t)))))))))

;;; Obsolete, but keep for backward compatibility
    ( (?x #$covers ?y)
      (lambda (fmode target x y)
	(km-int `(,y #$isa ,x) :fail-mode fmode :target target :rewritep t)) )

    ( (?y #$isa ?x)
      (lambda (_fmode _target y x)
	   (declare (ignore  _fmode _target))
	   (let* ( (yvals (km-int y))
		   (yv (first yvals)) )
	     (cond ((null yvals)
		    (report-error 'user-error "Doing ~a:~% ~a evaluates to nil (should evaluate to an instance!)~%" `(,y #$isa ,x) y))
		   ((not (singletonp yvals))
		    (report-error 'user-error "Doing ~a:~% ~a evaluates to multiple values ~a (should evaluate to a single instance!)~%"
				  `(,y #$isa ,x) y yvals))
		   (t (let* ((xvals (km-int x))
			     (xv (first xvals)))
			(cond ((null xvals)
			       (report-error 'user-error "Doing ~a:~% ~a evaluates to nil (should evaluate to something!)~%" `(,y #$isa ,x) x))
			      ((not (singletonp xvals))
			       (report-error 'user-error "Doing ~a:~% ~a evaluates to multiple values ~a (should evaluate to a single object!)~%"
					     `(,y #$isa ,x) x xvals))
			      ((kb-objectp xv)
			       (cond ((isa yv xv) '#$(t)))) ; quick test
			      ((covers (list xv) yv) '#$(t)))))))) ) ; more complex test for expressions

    ( (?x #$is ?y)
      (lambda (_fmode _target x y)
	   (declare (ignore  _fmode _target))
	   (let ( (xv (km-unique-int x)) )
	     (cond ((null xv) nil)
		   (t (let ( (yv (km-unique-int y)) )
			(cond ((and (not (null yv))
				    (is xv yv)) '#$(t)))))))))

;;; ======================================================================

    ( (?xs #$includes ?y)
      (lambda (_fmode _target xs y)
	   (declare (ignore  _fmode _target))
	   (let ((xs-vals (km-int xs))
;		 (y-val (km-unique-int y :fail-mode 'error)) ; no, I think it's ok for this to return NIL
		 (y-val (km-unique-int y)))
	     (cond ((member y-val (dereference xs-vals) :test #'equal) '#$(t))))))

    ( (?xs #$is-superset-of ?ys)
      (lambda (_fmode _target xs ys)
	   (declare (ignore  _fmode _target))
	   (let ( (xs-vals (km-int xs))
		  (ys-vals (km-int ys)) )
	     (cond ((subsetp ys-vals (dereference xs-vals) :test #'equal) '#$(t))))) )

;;; ======================================================================
;;;		SEQUENCE MANIPULATION
;;; ======================================================================

    ( (?seq-expr1 #$append ?seq-expr2)
      (lambda (_fmode _target seq-expr1 seq-expr2)
	(declare (ignore  _fmode _target))
	(let* ( (seq1 (km-unique-int seq-expr1))
		(seq2 (km-unique-int seq-expr2))
		(elts1 (cond ((or (km-seqp seq1)
				  (km-bagp seq1)) (seq-to-list seq1))
			     ((null seq1) nil)
			     ((is-km-term seq1) (list seq1))
			     (t (report-error 'user-error "(~a append ~a): ~a doesn't evaluate to an instance, sequence, or bag!"
					      seq-expr1 seq-expr2 seq-expr1))))
		(elts2 (cond ((or (km-seqp seq2)
				  (km-bagp seq2)) (seq-to-list seq2))
			     ((null seq2) nil)
			     ((is-km-term seq2) (list seq2))
			     (t (report-error 'user-error "(~a append ~a): ~a doesn't evaluate to an instance, sequence, or bag!"
					      seq-expr1 seq-expr2 seq-expr2))))
		(result-type (cond ((or (and (km-seqp seq1) (km-bagp seq2))
					(and (km-seqp seq2) (km-bagp seq1)))
				    (report-error 'user-error "(~a append ~a): Elements should be both sequences or both bags!"
						  seq-expr1 seq-expr2)
				    '#$:seq)						; result on failure
				   ((or (km-bagp seq1) (km-bagp seq2)) '#$:bag)
				   (t '#$:seq))) )					; default
	  `((,result-type ,@(append elts1 elts2))))) )

;;; ======================================================================
;;;		ALLOF/ONEOF etc.
;;; ======================================================================

;;; New. NOTE: fails quietly if it can't find any values. That's fine.
    ( (?expr #$called ?tag)
      (lambda (fmode _target expr tag)
	(declare (ignore _target))
	(let* ( (vals (km-int expr)) )
	  (cond (vals (km-trace 'comment "Now find just those value(s) whose tag = ~a..." tag)))
	  (let* ( (tags (val-to-vals tag))
		  (target-vals (remove-if #'(lambda (val)
					      (set-difference tags (append (km-int `#$(the called of ,VAL))
									   (km-int `#$(the uniquely-called of ,VAL)))
							      :test #'equal))
					  vals)) )
	    (cond ((null target-vals)
		   (cond ((eq fmode 'error)
			  (report-error 'user-error "(~a called/uniquely-called ~a): No values of ~a (evaluates to ~a) is called/uniquely-called ~a!"
					expr tag expr vals (val-to-vals tag)))
;			 (t (make-comment "Warning: Can't find any (~a called/uniquely-called ~a)" expr tag))
			 ))
		  (t target-vals))))) )

; synonym
    ( (?expr #$uniquely-called ?tag)
      (lambda (fmode target expr tag)
	(km-int `(,expr #$called ,tag) :fail-mode fmode :target target :rewritep t)) )

;;; > (a man with (parts ((a arm) (a leg) (a arm))))
;;; _man1187
;;; > (allof ((_man1187 parts)) where (it isa arm))
;;; (_arm1188 _arm1190)
    ( (#$allof ?set #$where ?test)
      (lambda (fmode target set test)
	   (km-int `(#$forall ,set #$where ,test #$It) :fail-mode fmode :target target :rewritep t)))  ; equivalent

;;; New for KM1.4.0 beta-12
    ( (#$allof ?set #$must ?test)
      (lambda (fmode target set test)
	(declare (ignore fmode target))
	(cond ((every #'(lambda (instance)
			  (km-int (subst Instance '#$It test)))
		      (km-int set))
	       '#$(t)))))

;;; New for KM1.4.0 beta-18
    ( (#$allof ?set #$where ?test2 #$must ?test)
      (lambda (fmode target set test2 test)
	(declare (ignore fmode target))
	(cond ((every #'(lambda (instance)
			  (km-int (subst Instance '#$It test)))
		      (km-int `#$(allof ,SET where ,TEST2)))
	       '#$(t)))))

    ( (#$oneof ?set #$where ?test)
      (lambda (fmode target set test)
	(declare (ignore fmode target))
	(let ( (answer (find-if #'(lambda (member)
				    (km-int (subst member '#$It test)))
				(km-int set))) )
	  (cond (answer (list answer))))) )

;;; New  1.4 - check to ensure there's a single value
    ( (#$theoneof ?set #$where ?test)
      (lambda (fmode target set test)
	   (let ( (val (km-unique-int `(#$forall ,set #$where ,test #$It) :fail-mode fmode :target target :rewritep t)) )  ; equivalent
	     (cond (val (list val))))) )

    ( (#$forall ?set ?value)
      (lambda (fmode target set value)
	   (km-int `(#$forall ,set #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

;;; This iterates through a SINGLE SEQUENCE, returning a SEQUENCE of results.
    ( (#$forall-seq ?seq ?value)
      (lambda (fmode target seq value)
	   (km-int `(#$forall-seq ,seq #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

    ( (#$forall-bag ?bag ?value)
      (lambda (fmode target bag value)
	   (km-int `(#$forall-bag ,bag #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

    ( (#$forall ?set #$where ?constraint ?value)
      (lambda (_fmode _target set constraint value)
	   (declare (ignore  _fmode _target))
	   (remove nil
	    (my-mapcan #'(lambda (member)
			   (cond ((km-int (subst member '#$It constraint))
				  (km-int (subst member '#$It value)))))
		       (km-int set)))) )

;;; ----------

;;; This iterates through a SINGLE SEQUENCE, returning a SEQUENCE of results.
    ( (#$forall-seq ?seq #$where ?constraint ?value)
      (lambda (_fmode _target seq constraint value)
	   (declare (ignore  _fmode _target))
	   (let ( (sequences (km-int seq)) )
	     (cond ((null sequences) nil)
	           ((or (not (singletonp sequences))
			(not (km-seqp (first sequences))))
		    (report-error 'user-error "~a: ~a should evaluate to a single sequence (:seq ... ...)!~%"
				  `#$(forall-seq ,SEQ where ,CONSTRAINT ,VALUE) seq))
		   (t (list
		       (cons '#$:seq
			    (remove 'to-remove
			     (mapcar #'(lambda (member)
					 (cond ((km-int (subst member '#$It constraint))
						(vals-to-val (km-int (subst member '#$It value))))
					       (t 'to-remove)))
				     (rest (first sequences)))))))))) )	; ((:seq a b)) -> map over (a b)

    ( (#$forall-seq2 ?seq #$where ?constraint ?value)
      (lambda (_fmode _target seq constraint value)
	   (declare (ignore  _fmode _target))
	   (let ( (sequences (km-int seq)) )
	     (cond ((null sequences) nil)
		   ((or (not (singletonp sequences))
			(not (km-seqp (first sequences))))
		    (report-error 'user-error "~a: ~a should evaluate to a single sequence (:seq ... ...)!~%"
				  `#$(forall-seq2 ,SEQ where ,CONSTRAINT ,VALUE) seq))
		   (t (list
		       (cons '#$:seq
			    (remove 'to-remove
			     (mapcar #'(lambda (member)
					 (cond ((km-int (subst member '#$It2 constraint))
						(vals-to-val (km-int (subst member '#$It2 value))))
					       (t 'to-remove)))
				     (rest (first sequences)))))))))) )	; ((:seq a b)) -> map over (a b)

;;; ----------

;;; This iterates through a SINGLE SEQUENCE, returning a SEQUENCE of results.
    ( (#$forall-bag ?bag #$where ?constraint ?value)
      (lambda (_fmode _target bag constraint value)
	   (declare (ignore  _fmode _target))
	   (let ( (bags (km-int bag)) )
	     (cond ((null bags) nil)
		   ((or (not (singletonp bags))
			(not (km-bagp (first bags))))
		    (report-error 'user-error "~a: ~a should evaluate to a single bag (:bag ... ...)!~%"
				  `#$(forall-bag ,BAG where ,CONSTRAINT ,VALUE) bag))
		   (t (list
		       (cons '#$:bag
			     (remove nil
				     (mapcar #'(lambda (member)
						 (cond ((km-int (subst member '#$It constraint))
							(vals-to-val (km-int (subst member '#$It value))))))
					     (rest (first bags)))))))))) )	; ((:bag a b)) -> map over (a b)

    ( (#$forall-bag2 ?bag #$where ?constraint ?value)
      (lambda (_fmode _target bag constraint value)
	   (declare (ignore  _fmode _target))
	   (let ( (bags (km-int bag)) )
	     (cond ((null bags) nil)
		   ((or (not (singletonp bags))
			(not (km-bagp (first bags))))
		    (report-error 'user-error "~a: ~a should evaluate to a single bag (:bag ... ...)!~%"
				  `#$(forall-bag2 ,BAG where ,CONSTRAINT ,VALUE) bag))
		   (t (list
		       (cons '#$:bag
			     (remove nil
				     (mapcar #'(lambda (member)
						 (cond ((km-int (subst member '#$It2 constraint))
							(vals-to-val (km-int (subst member '#$It2 value))))))
					     (rest (first bags)))))))))) )	; ((:bag a b)) -> map over (a b)

;;; ----------

;;; To allow nesting, we also have forall2, whose referents are "it2"
    ( (#$allof2 ?set #$where ?test)
      (lambda (fmode target set test)
	   (km-int `(#$forall2 ,set #$where ,test #$It2) :fail-mode fmode :target target :rewritep t)))  ; equivalent

;;; New for KM1.4.0 beta-12
    ( (#$allof2 ?set #$must ?test)
      (lambda (fmode target set test)
	(declare (ignore fmode target))
	(cond ((every #'(lambda (instance)
			  (km-int (subst Instance '#$It2 test)))
		      (km-int set))
	       '#$(t)))))

;;; New for KM1.4.0 beta-18
    ( (#$allof2 ?set #$where ?test2 #$must ?test)
      (lambda (fmode target set test2 test)
	(declare (ignore fmode target))
	(cond ((every #'(lambda (instance)
			  (km-int (subst Instance '#$It2 test)))
		      (km-int `#$(allof2 ,SET where ,TEST2)))
	       '#$(t)))))

    ( (#$oneof2 ?set #$where ?test)
      (lambda (fmode target set test)
	(declare (ignore fmode target))
	(let ( (answer (find-if #'(lambda (member)
				    (km-int (subst member '#$It2 test)))
				(km-int set))) )
	  (cond (answer (list answer))))) )

    ( (#$forall2 ?set ?value)
      (lambda (fmode target set value)
	   (km-int `(#$forall2 ,set #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

    ( (#$forall-seq2 ?seq ?value)
      (lambda (fmode target seq value)
	   (km-int `(#$forall-seq2 ,seq #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

    ( (#$forall-bag2 ?bag ?value)
      (lambda (fmode target bag value)
	   (km-int `(#$forall-bag2 ,bag #$where t ,value) :fail-mode fmode :target target :rewritep t)))  ; equivalent

    ( (#$theoneof2 ?set #$where ?test)
      (lambda (fmode target set test)
	   (let ( (val (km-unique-int `(#$forall2 ,set #$where ,test #$It2) :fail-mode fmode :target target :rewritep t)) )  ; equivalent
	     (cond (val (list val))))) )

    ( (#$forall2 ?set #$where ?constraint ?value)
      (lambda (_fmode _target set constraint value)
	   (declare (ignore  _fmode _target))
	   (remove 'nil
	    (my-mapcan #'(lambda (member)
			   (cond ((km-int (subst member '#$It2 constraint))
				  (km-int (subst member '#$It2 value)))))
		       (km-int set)))) )

;;; ======================================================================
;;;			NEW: VARIABLES!!!
;;; ======================================================================

    ( (#$allof ?var #$in  ?set #$where ?test)
      (lambda (fmode target var set test)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$allof ,var #$in ,set #$where ,test)))
	      (t (km-int `(#$forall ,var #$in ,set #$where ,test ,var) :fail-mode fmode :target target :rewritep t)))) )  ; equivalent

    ( (#$allof ?var #$in ?set #$must ?test)
      (lambda (fmode target var set test)
	(declare (ignore fmode target))
	(allof-must var set test)) )

    ( (#$allof ?var #$in ?set #$where ?test2 #$must ?test)
      (lambda (fmode target var set test2 test)
	(declare (ignore fmode target))
	(allof-where-must var set test2 test)) )

    ( (#$oneof ?var #$in ?set #$where ?test)
      (lambda (fmode target var set test)
	(declare (ignore fmode target))
	(oneof-where var set test)) )

    ( (#$theoneof ?var #$in ?set #$where ?test)
      (lambda (fmode target var set test)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$theoneof ,var #$in ,set #$where ,test)))
	      (t (let ( (val (km-unique-int `(#$forall ,var #$in ,set #$where ,test ,var) :fail-mode fmode :target target :rewritep t)) )  ; equivalent
		   (cond (val (list val))))))) )

    ( (#$forall ?var #$in ?set ?value)
      (lambda (fmode target var set value)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$forall ,var #$in ,set ,value)))
	      (t (km-int `(#$forall ,var #$in ,set #$where t ,value) :fail-mode fmode :target target :rewritep t)))) )  ; equivalent

    ( (#$forall-seq ?var #$in ?seq ?value)
      (lambda (fmode target var seq value)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$forall-seq ,var #$in ,seq ,value)))
	      (t (km-int `(#$forall-seq ,var #$in ,seq #$where t ,value) :fail-mode fmode :target target :rewritep t)))) )  ; equivalent

    ( (#$forall-bag ?var #$in ?bag ?value)
      (lambda (fmode target var bag value)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$forall-bag ,var #$in ,bag ,value)))
	      (t (km-int `(#$forall-bag ,var #$in ,bag #$where t ,value) :fail-mode fmode :target target :rewritep t)))) )  ; equivalent

    ( (#$forall ?var #$in ?set #$where ?constraint ?value)
      (lambda (_fmode _target var set constraint value)
	   (declare (ignore  _fmode _target))
	   (cond ((not (km-varp var))
		  (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$forall ,var #$in ,set #$where ,constraint ,value)))
		 (t (remove nil
			    (my-mapcan #'(lambda (member)
					   (cond ((km-int (subst member var constraint))
						  (km-int (subst member var value)))))
				       (km-int set)))))) )

    ( (#$forall-bag ?var #$in ?bag #$where ?constraint ?value)
      (lambda (_fmode _target var bag constraint value)
	   (declare (ignore  _fmode _target))
	   (cond ((not (km-varp var))
		  (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%"
				`(#$forall-bag ,var #$in ,bag #$where ,constraint ,value)))
		 (t (let ( (bags (km-int bag)) )
		      (cond ((or (not (singletonp bags))
				 (not (km-bagp (first bags))))
			     (report-error 'user-error "~a: ~a should evaluate to a single bag (:bag ... ...)!~%"
					   `#$(forall-bag ,VAR in ,BAG where ,CONSTRAINT ,VALUE) bag))
			    (t (list
				(cons '#$:bag
				      (remove nil
					      (mapcar #'(lambda (member)
							  (cond ((km-int (subst member var constraint))
								 (vals-to-val (km-int (subst member var value))))))
						      (rest (first bags)))))))))))) )	; ((:bag a b)) -> map over (a b)

    ( (#$forall-seq ?var #$in ?seq #$where ?constraint ?value)
      (lambda (_fmode _target var seq constraint value)
	   (declare (ignore  _fmode _target))
	   (cond ((not (km-varp var))
		  (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%"
				`(#$forall-seq ,var #$in ,seq #$where ,constraint ,value)))
		 (t (let ( (sequences (km-int seq)) )
		      (cond ((or (not (singletonp sequences))
				 (not (km-seqp (first sequences))))
			     (report-error 'user-error "~a: ~a should evaluate to a single sequence (:seq ... ...)!~%"
					   `#$(forall-seq ,VAR in ,SEQ where ,CONSTRAINT ,VALUE) seq))
			    (t (list
				(cons '#$:seq
				      (remove 'to-remove
					      (mapcar #'(lambda (member)
							  (cond ((km-int (subst member var constraint))
								 (vals-to-val (km-int (subst member var value))))
								(t 'to-remove)))
						      (rest (first sequences)))))))))))) )	; ((:seq a b)) -> map over (a b)

;;; ----------

;;; Given a function with zero arguments, KM will automatically evalute it.
    ( (function ?lispcode)		;;; NB NOT #$function, as we mean Lisp FUNCTION (#')
      (lambda (_fmode _target lispcode)
	(declare (ignore  _fmode _target))
;	(km-format t "CALLING FUNCTION~%")
	   (let* ( (answer0 (funcall (eval (list 'function lispcode)))) ; lispcode can return a val, or list of vals
		   (answer (listify answer0)) )
	     (cond ((every #'fully-evaluatedp answer) answer)
		   (t (report-error 'user-error
"In call to external Lisp procedure
  ~a
Lisp procedure should return a list of fully evaluated KM objects (e.g.,
instances, or :seq/:bag/:pair of instances), but instead returned:
   ~a~%" lispcode answer0))))) )

;;; ======================================================================
;;;		MULTIARGUMENT PREDICATES
;;; ======================================================================

;;; Shorthands
    ( (#$the1 ?slot #$of ?frameadd)
      (lambda (fmode target slot frameadd)
	(km-int `#$(the1 of (the ,SLOT of ,FRAMEADD)) :fail-mode fmode :target target :rewritep t)) )

    ( (#$the2 ?slot #$of ?frameadd)
      (lambda (fmode target slot frameadd)
	(km-int `#$(the2 of (the ,SLOT of ,FRAMEADD)) :fail-mode fmode :target target :rewritep t)) )

    ( (#$the3 ?slot #$of ?frameadd)
      (lambda (fmode target slot frameadd)
	(km-int `#$(the3 of (the ,SLOT of ,FRAMEADD)) :fail-mode fmode :target target :rewritep t)) )

;;; ----------

;;; [1] New: tolerate (the1 of x), where x isn't structured
    ( (#$the1 #$of ?frameadd)
      (lambda (fmode target frameadd)
	(let ( (multiargs (km-int frameadd :fail-mode fmode :target target :rewritep t)) )
	  (km-int (vals-to-val
		(mapcar #'(lambda (multiarg)
			    (cond ((km-structured-list-valp multiarg) (arg1of multiarg))
				  (t multiarg)))							; [1]
			multiargs))))) )
;	  (cond ((every #'km-structured-list-valp multiargs) (mapcar #'arg1of multiargs))
;		(t (report-error 'user-error "~a! the1 expects multi-argument values for ~a, but got ~a instead!~%"
;				 `#$(the1 of ,FRAMEADD)  frameadd multiargs))))) )

    ( (#$the2 #$of ?frameadd)
      (lambda (fmode target frameadd)
	(let ( (multiargs (km-int frameadd :fail-mode fmode :target target :rewritep t)) )
	 (km-int (vals-to-val
	  (mapcar #'(lambda (multiarg)
		      (cond ((km-structured-list-valp multiarg) (arg2of multiarg))))		; nil otherwise
		  multiargs))))) )
;	  (cond ((every #'km-structured-list-valp multiargs) (mapcar #'arg2of multiargs))
;		(t (report-error 'user-error "~a! the2 expects multi-argument values for ~a, but got ~a instead!~%"
;				 `#$(the2 of ,FRAMEADD)  frameadd multiargs))))) )

    ( (#$the3 #$of ?frameadd)
      (lambda (fmode target frameadd)
	(let ( (multiargs (km-int frameadd :fail-mode fmode :target target :rewritep t)) )
	  (km-int (vals-to-val
		(mapcar #'(lambda (multiarg)
		      (cond ((km-structured-list-valp multiarg) (arg3of multiarg))))	; nil otherwise
		  multiargs))))) )

;	  (cond ((every #'km-structured-list-valp multiargs) (mapcar #'arg3of multiargs))
;		(t (report-error 'user-error "~a! the3 expects multi-argument values for ~a, but got ~a instead!~%"
;				 `#$(the3 of ,FRAMEADD)  frameadd multiargs))))) )

    ( (#$theN ?nexpr #$of ?frameadd)
      (lambda (fmode target nexpr frameadd)
	(let ( (n (km-unique-int nexpr :fail-mode 'error))
	       (multiargs (km-int frameadd :fail-mode fmode :target target :rewritep t)) )
	  (cond ((or (not (integerp n))
		     (< n 1))
		 (report-error 'user-error "Doing ~a. ~a should evaluate to a non-negative integer!~%" `#$(the ,NEXPR of ,FRAMEADD) nexpr))
		(t (km-int (vals-to-val
		    (mapcar #'(lambda (multiarg)
			       (cond ((and (km-structured-list-valp multiarg)
					   (< n (length multiarg)))		; elt returns error if n out of range under Mac CommonLisp
				      (elt multiarg n))
				     ((= n 1) multiarg)))					; nil otherwise
			   multiargs))))))) )

;;; This is slightly bad naming but oh well. theN is used for a SINGLE structured value. theNth is used for multiple values (sets).
    ( (#$theNth ?nexpr #$of ?frameadd)
      (lambda (fmode target nexpr frameadd)
	(let ( (n (km-unique-int nexpr :fail-mode 'error))
	       (vals (km-int frameadd :fail-mode fmode :target target :rewritep t)) )
	  (cond ((or (not (integerp n))
		     (< n 1))
		 (report-error 'user-error "Doing ~a. ~a should evaluate to a non-negative integer!~%" `#$(the ,NEXPR of ,FRAMEADD) nexpr))
		((and (<= n (length vals))			; elt returns error if n out of range under Mac CommonLisp
		      (elt vals (1- n)))
		 (list (elt vals (1- n))))))) )

;	        ((every #'km-structured-list-valp multiargs)
;		 (mapcar #'(lambda (seq) (and (< n (length seq)) 		; NB (:seq 1 2 3) has 3 (not 4) elements
;					      (elt seq n))) multiargs))
;		(t (report-error 'user-error "~a! theN expects multi-argument values for ~a, but got ~a instead!~%"
;			      `#$(the3 of ,FRAMEADD)  frameadd multiargs))))) )

;;; ======================================================================
;;;		ARITHMETIC
;;; ======================================================================

;;; Change default right-association precidence to left-association precedence, for
;;; cases where it makes a difference and appropriate:
   ( (?x ^ ?y ^ &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x ^ ,y) ^ ,@rest) :fail-mode fm)) )
   ( (?x ^ ?y + &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x ^ ,y) + ,@rest) :fail-mode fm)) )
   ( (?x ^ ?y - &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x ^ ,y) - ,@rest) :fail-mode fm)) )
   ( (?x ^ ?y / &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x ^ ,y) / ,@rest) :fail-mode fm)) )
   ( (?x ^ ?y * &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x ^ ,y) * ,@rest) :fail-mode fm)) )

   ( (?x / ?y + &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x / ,y) + ,@rest) :fail-mode fm)) )
   ( (?x / ?y - &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x / ,y) - ,@rest) :fail-mode fm)) )
   ( (?x / ?y / &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x / ,y) / ,@rest) :fail-mode fm)) )
   ( (?x / ?y * &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x / ,y) * ,@rest) :fail-mode fm)) )

   ( (?x * ?y + &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x * ,y) + ,@rest) :fail-mode fm)) )
   ( (?x * ?y - &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x * ,y) - ,@rest) :fail-mode fm)) )
   ( (?x * ?y / &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x * ,y) / ,@rest) :fail-mode fm)) )

   ( (?x - ?y - &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x - ,y) - ,@rest) :fail-mode fm)) )
   ( (?x - ?y + &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x - ,y) + ,@rest) :fail-mode fm)) )

   ( (?x + ?y - &rest) (lambda (fm tg x y rest) (declare (ignore tg)) (km-int `((,x + ,y) - ,@rest) :fail-mode fm)) )

;;; ----------------------------------------

   ( (?expr + &rest) (lambda (fmode target expr rest)
			  (let ( (x (km-unique-int expr :fail-mode fmode :target target :rewritep t))
				 (y (km-unique-int rest :fail-mode fmode :target target :rewritep t)) )
			    (cond ((and (numberp x) (numberp y)) (list (+ x y)))))))
   ( (?expr - &rest) (lambda (fmode target expr rest)
			  (let ( (x (km-unique-int expr :fail-mode fmode :target target :rewritep t))
				 (y (km-unique-int rest :fail-mode fmode :target target :rewritep t)) )
			    (cond ((and (numberp x) (numberp y)) (list (- x y)))))))
   ( (?expr * &rest) (lambda (fmode target expr rest)
			  (let ( (x (km-unique-int expr :fail-mode fmode :target target :rewritep t))
				 (y (km-unique-int rest :fail-mode fmode :target target :rewritep t)) )
			    (cond ((and (numberp x) (numberp y)) (list (* x y)))))))
   ( (?expr / &rest) (lambda (fmode target expr rest)
			  (let ( (x (km-unique-int expr :fail-mode fmode :target target :rewritep t))
				 (y (km-unique-int rest :fail-mode fmode :target target :rewritep t)) )
			    (cond
			     ((and (numberp x) (numberp y))
#|new|#			      (cond ((and (zerop x)
					  (zerop y) (list 1)))
#|new|#                             ((zerop x) (list 0))
#|new|#                             ((zerop y) (list *infinity*))
                                    ((and (numberp x) (numberp y)) (list (/ x y)))))))) )

   ( (?expr1 ^ ?expr2) (lambda (fmode target expr1 expr2)
			  (let ( (x (km-unique-int expr1 :fail-mode fmode :target target :rewritep t))
				 (y (km-unique-int expr2 :fail-mode fmode :target target :rewritep t)) )
			    (cond ((and (numberp x) (numberp y)) (list (expt x y)))))))

; shouldn't be needed now
;    ( #$:set
;      (lambda (_fmode) (declare (ignore _fmode)) nil) )

;;; also handled in faster mechanism directly in km1. Leave it here for completeness
    ( #$nil
      (lambda (_fmode _target) (declare (ignore _fmode _target)) nil) )

    ( nil		; ie. NIL
      (lambda (_fmode _target) (declare (ignore _fmode _target)) nil) )

    ( (#$:set &rest)					; for :set, just remove :set tag to return a list
      (lambda (fmode target exprs) 				; km will do the dereferencing and remove the duplicates later
	   (declare (ignore fmode))
	   (my-mapcan #'(lambda (expr) (km-int expr :target target)) exprs)) )


   ;;; NOTE: These are NOT rewrites, they are breaking up a goal into subgoals
    ( (#$:seq &rest)					; for :seq, build a one-element long structure
      (lambda (fmode target exprs)
	   (declare (ignore target fmode))
	   (let ( (sequence (mapcar #'(lambda (expr)
					(vals-to-val (km-int expr #|:target target :rewritep t|#))) exprs)) )
	     (cond (sequence `#$((:seq ,@SEQUENCE)))))) )

    ( (#$:bag &rest)					; for :bag, build a one-element long structure
      (lambda (fmode target exprs)
	   (declare (ignore target fmode))
	   (let ( (bag (mapcar #'(lambda (expr)
				   (vals-to-val (km-int expr #|:target target :rewritep t|#)))
			       exprs)) )
	     (cond (bag `#$((:bag ,@BAG)))))) )

    ( (#$:function &rest)				; Identical code for functions...
      (lambda (fmode target exprs)
	   (declare (ignore target fmode))
	   (let ( (sequence (mapcar #'(lambda (expr)  (vals-to-val (km-int expr #|:target target :rewritep t|#))) exprs)) )
	     (cond (sequence `#$((:function ,@SEQUENCE)))))) )

    ( (#$:pair &rest)					; for :seq, build a one-element long structure
      (lambda (fmode target exprs)
	   (declare (ignore target fmode))
	   (cond ((not (pairp exprs))
		  (report-error 'user-error "~a: A pair should have exactly two elements!~%" `#$(:pair ,@EXPRS)))
	    (t (let ( (sequence (mapcar #'(lambda (expr)
					    (vals-to-val (km-int expr #|:target target :rewritep t|#))) exprs)) )
		 (cond (sequence `#$((:pair ,@SEQUENCE)))))))) )

;;; Dec 00 - make this reflexive
;;; Apr 01 - Put evaluation back again -- but not quite! Argh, can't quite put this back to normal,
;;; 	     because I want to account for subsumption with triples like
;;; 		(:triple *Pete owns (a House)) and (:triple *Pete owns (mustnt-be-a House))
    ( (#$:triple ?frame-expr ?slot-expr ?val-expr)					; for :seq, build a one-element long structure
      (lambda (_fmode _target frame-expr slot-expr val-expr)
	(declare (ignore _fmode _target))
	(let* ((slot (cond ((comparison-operator slot-expr) slot-expr) 	; can't pass >= etc. to km-unique-int (it's a keyword)
			   (t (km-unique-int slot-expr :fail-mode 'error))))
	       (frame (cond ((and (comparison-operator slot)
				  (minimatch frame-expr '#$(the ?x of ?y))) frame-expr)		; very special case - retain structure
			    (t (km-unique-int frame-expr :fail-mode 'error))))
	       (val-expr0 (desource+decomment val-expr))	; There shouldn't be any comments here, but just in case!
	       (val (cond ((or (constraint-exprp val-expr0)  ; NB better decomment or else comment
			       (existential-exprp val-expr0) ;    may cause failure.
			       (comparison-operator slot))
			   val-expr0)	; preserve expressions (a House) or (mustnt-be-a House) or
					;  		(:triple (the age of X) < (the age of Y))
			  (t (vals-to-val (km-int val-expr))))) )
	  `#$((:triple ,FRAME ,SLOT ,VAL)))) )

    ( (#$:args &rest)					; for :seq, build a one-element long structure
      (lambda (fmode target exprs)
	   (declare (ignore fmode target))
	   (let ( (sequence (mapcar #'(lambda (expr)  (vals-to-val (km-int expr))) exprs)) )
	     (cond (sequence `#$((:args ,@SEQUENCE)))))) )
; Neah, not this:
;	   (let ( (sequence (my-mapcan #'(lambda (expr)  (km-int expr)) exprs)) )
;	     (cond (sequence `#$((:args ,@SEQUENCE)))))) )

    ( (#$showme ?km-expr)
      (lambda (_fmode _target km-expr)
	   (declare (ignore _fmode _target))
	   (showme km-expr)) )

    ( (#$showme ?km-expr ?file)
      (lambda (_fmode _target km-expr file)
	   (declare (ignore _fmode _target))
	   (cond ((not (stringp file))
		  (report-error 'user-error "(showme <expr> <filename>): <filename> should be a string!~%"))
		 (t (let ( (stream (tell file)) )
		      (prog1
			  (showme km-expr (all-situations) (visible-theories) stream)
			(cond ((streamp stream) (close stream)))
			(km-format t "(Output sent to file ~a)~%" file)))))) )

    ( (#$showme-all ?km-expr)
      (lambda (_fmode _target km-expr)
	   (declare (ignore _fmode _target))
	   (showme-all km-expr)) )

    ( (#$evaluate-all ?km-expr)
      (lambda (_fmode _target km-expr)
	   (declare (ignore _fmode _target))
	   (evaluate-all km-expr)) )

    ( (#$showme-here ?km-expr)
      (lambda (_fmode _target km-expr)
	   (declare (ignore _fmode _target))
	   (showme km-expr (list (curr-situation)) (visible-theories))) )

;;; ----------

    ( (#$the-class ?class)
      (lambda (fmode target class)
	(declare (ignore fmode target))
;	(km-int class :fail-mode fmode)) )
;	`((#$the-class ,class))) )
#|NEW|#	(process-unquotes `((#$the-class ,class)))) )
;	`('(#$every ,class))) )


    ( (#$the-class ?class #$with &rest)
      (lambda (fmode target class slotsvals)
	(declare (ignore fmode target))
	(cond ((are-slotsvals slotsvals)
;	       `((#$the-class ,class #$with ,@slotsvals))))) )
#|NEW|#		(process-unquotes `((#$the-class ,class #$with ,@slotsvals)))))) )
;	       `('(#$every ,class #$with ,@slotsvals))))) )

;;; ----------

    ( (#$constraints-for (#$the ?slot #$of ?frameadd))
      (lambda (fmode0 target slot frameadd)
	(declare (ignore fmode0 target))
	(let ( (frame (km-unique-int frameadd :fail-mode 'error)) )
	  (mapcar #'quotify (collect-constraints-on-instance frame slot)))) )

    ( (#$rules-for (#$the ?slot #$of ?frameadd))
      (lambda (fmode0 target slot frameadd)
	(declare (ignore fmode0 target))
	(let ( (rules (rules-for slot frameadd)) )
	  (cond ((null rules) nil)
		((km-setp rules)
		 (mapcar #'quotify (set-to-list rules)))
		(t (list (quotify rules)))))) )		; otherwise

    ( (#$why)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(why)) )

    ( (#$why ?triple)
      (lambda (fmode target triple)
	(declare (ignore fmode target))
	(cond ((not (km-triplep triple))
	       (report-error 'user-error "Bad argument to (why ...)! Should be of form (why (:triple <f> <s> <v>))!"))
	      (t (why triple)))) )

    ( (#$justify)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(justify)))

    ( (#$justify ?triple)
      (lambda (fmode target triple)
	(declare (ignore fmode target))
	(justify triple)))

    ( (#$get-justification)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(list (concat-list (insert-delimeter (get-justification :format 'ascii) *newline-str*)))) )
; 8/9/05 Remove "----"s
;	(list
;	 (concat-list
;	  (cons (format nil "--------------------~%")
;		(append (insert-delimeter (get-justification :format 'ascii) *newline-str*)
;			(list (format nil "~%-------------------~%"))))))) )

    ( (#$get-justification ?triple)
      (lambda (fmode target triple)
	(declare (ignore fmode target))
	(list (concat-list (insert-delimeter (get-justification :triple triple :format 'ascii) *newline-str*)))) )
; 8/9/05 Remove "----"s
;	(list
;	 (concat-list
;	  (cons (format nil "--------------------~%")
;		(append (insert-delimeter (get-justification :triple triple :format 'ascii) *newline-str*)
;			(list (format nil "~%-------------------~%"))))))) )

;;; NEW: allow explanations to be re-read in from a .km file. Useful for explanations for prototype pieces.
    ( (#$explanation (#$:triple ?f0 ?s ?v0) ?explanations)
      (lambda (fmode target f0 s v0 explanations)
	(declare (ignore fmode target))
	(let ((f (dereference f0))
	      (v (dereference v0)))
	  (mapc #'(lambda (explanation)
		    (record-explanation-for `#$(the ,S of ,F) v explanation :situation *global-situation*
					    :ignore-clone-cycles t))
		(dereference explanations)))
	'#$(t)) )

    ( (#$explained-by ?instance ?expr)
     (lambda (fmode target instance expr)
       (declare (ignore fmode target))
       (explained-by instance expr)) )

    ( (#$comment ?comment-tag &rest)
      (lambda (fmode target comment-tag data)
	(declare (ignore fmode target))
	(comment comment-tag data)) )

    ( (#$show-comment ?comment-tag)
      (lambda (fmode target comment-tag)
	(declare (ignore fmode target))
	(show-comment comment-tag)) )

    ( (quote ?expr)
       (lambda (fmode target expr)
	(declare (ignore fmode target))
	 (let ( (processed-expr (process-unquotes expr)) )
	   (cond (processed-expr (list (list 'quote processed-expr)))))) )

    ( (unquote ?expr)
       (lambda (fmode target expr)
	(declare (ignore fmode target))
	 (report-error 'user-error "Doing #,~a: You can't unquote something without it first being quoted!~%" expr)) )

;;; For Adam Farquhar - 12/9/98 now it *does* delete inverses
    ( (#$delete ?km-expr)
       (lambda (fmode target km-expr)
	 (mapc #'delete-frame (km-int km-expr :fail-mode fmode :target target :rewritep t))
	 '#$(t)))

    ( (#$evaluate ?expr)		; Can't use eval, as that's a Lisp call!
       (lambda (fmode target expr)
	    (let ( (quoted-exprs (km-int expr :fail-mode fmode :target target :rewritep t)) )
	      (remove nil
	      (my-mapcan #'(lambda (quoted-expr)
			     (cond ((member quoted-expr '#$(f F)) nil)
				   ((and (pairp quoted-expr)
					 (eq (first quoted-expr) 'quote))
				    (km-int (second quoted-expr) :fail-mode fmode))
; Neah, don't do this.
;				   ((km-triplep quoted-expr)					; NEW
;				    (let ( (frame (km-unique-int (second quoted-expr) :fail-mode 'error))
;					   (slot (km-unique-int (third quoted-expr) :fail-mode 'error))
;					   (val (cond ((constraint-exprp (fourth quoted-expr)) (fourth quoted-expr)) ; NEW: constraints *preserved*
;						      (t (vals-to-val (km-int (fourth quoted-expr)))))) ) ; allow val to be NIL, atom, :set
;				      `#$((:triple ,FRAME ,SLOT ,VAL))))
				   (t (report-error 'user-error
						    "(evaluate ~a)~%evaluate should be given a quoted expression to evaluate!~%"
						    quoted-expr))))
			 quoted-exprs)))) )

    ( (#$exists ?frame)
      (lambda (fmode target frame)
	(report-error 'user-warning "(exists ~a): (exists <expr>) has been renamed (has-value <expr>) in KM 1.4.~%       Please update your KB! Continuing...~%" frame)
	(km-int `#$(has-value ,FRAME) :fail-mode fmode :target target :rewritep t)) )

    ( (#$has-value ?frame)
      (lambda (_fmode _target frame) (declare (ignore  _fmode _target)) (cond ((km-int frame) '#$(t)))) )

    ( (#$print ?expr)
      (lambda (_fmode _target expr)
	(declare (ignore _fmode _target))
	(let ( (vals (km-int expr)) )
	  (km-format t "~a~%" vals)
	  vals )))

    ( (#$format ?flag ?string &rest)
      (lambda (_fmode _target flag string arguments)
	(declare (ignore _fmode _target))
	(cond ((eq flag '#$t)
	       (apply #'format `(t ,string ,@(mapcar #'(lambda (arg) (km-int arg)) arguments)))
	      '#$(t))
	      ((member flag '#$(nil NIL))
	       (list (apply #'format `(nil ,string ,@(mapcar #'(lambda (arg) (km-int arg)) arguments)))))
	      (t (report-error 'user-error "~a: Second argument must be `t' or `nil', not `~a'!~%"
			       `(#$format ,flag ,string ,@arguments) flag)))) )

    ( (#$km-format ?flag ?string &rest)
      (lambda (_fmode _target flag string arguments)
	(declare (ignore _fmode _target))
	(cond ((eq flag '#$t)
	       (apply #'km-format `(t ,string ,@(mapcar #'(lambda (arg) (km-int arg)) arguments)))
	      '#$(t))
	      ((member flag '#$(nil NIL))
	       (list (apply #'km-format `(nil ,string ,@(mapcar #'(lambda (arg) (km-int arg)) arguments)))))
	      (t (report-error 'user-error "~a: Second argument must be `t' or `nil', not `~a'!~%"
			       `(#$km-format ,flag ,string ,@arguments) flag)))) )

;;; (_car1) -> (_car1)
;;; (_car1 _car2) -> (_car1 "and" _car2)
;;; (_car1 _car2 _car3) -> (_car1 "," _car2 ", and" _car3)
    ( (#$andify ?expr)
      (lambda (fmode target expr)
	(list (cons '#$:seq (andify (km-int expr :fail-mode fmode :target target :rewritep t))))) ) ; to avoid removing duplicate ", "s

;;; [1] 6.9.00 - allow the subquery to fail quietly. The parent call can handle it as an error, if it so desires.
    ( (#$make-sentence ?expr)
      (lambda (_fmode _target expr)
	   (declare (ignore _fmode _target))
#|[1]|#	   (let ( (text (km-int expr)) )		; should now return zero or more sequences ((:seq "Print" ..) (:seq ...))
	     (make-comment "anglifying ~a" text)	; show the user the original
	     (list (make-sentence text)))) )					; return the concatenation
;	     (mapcar #'make-sentence text))) )	; return the concatenation

    ( (#$make-phrase ?expr)			; This version *doesn't* capitalize
      (lambda (_fmode _target expr)
	   (declare (ignore _fmode _target))
	   (let ( (text (km-int expr)) )	; should now return zero or more sequences ((:seq "Print" ..) (:seq ...))
	     (make-comment "anglifying ~a" text)	; show the user the original
	     (list (make-phrase text)))) )
;	     (mapcar #'(lambda (item)
;			 (make-phrase item))
;		     text))) )			; return the concatenation

    ( (#$pluralize ?expr)
      (lambda (fmode target expr)
	(declare (ignore fmode target))
	(report-error 'user-error
		      "(pluralize ~a): pluralize is no longer defined in KM1.4 - use \"-s\" suffix instead!~%" expr)) )

;;; ======================================================================
;;;		SPYPOINT MECHANISM
;;; ======================================================================

    ( (#$spy ?expr)
      (lambda (fmode target expr)
	(declare (ignore fmode target))
	(spy expr)) )

    ( (#$spy)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(spy)) )

    ( (#$unspy)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(unspy)) )

    ((#$profile ?expr)
     (lambda (fmode target expr)
       (declare (ignore fmode target))
       (let ((*profiling* t))
	 (profile-reset)
	 (let ((answer (km-int expr)))
	   (km-format t "~a~%" answer)
	   (profile-report)
	   answer))) )

    ( (#$profile-report)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(profile-report)
	'#$(t)) )

    ( (#$profile-report ?n)
      (lambda (fmode target n)
	(declare (ignore fmode target))
	(profile-report n)
	'#$(t)) )

;;; ======================================================================
;;;		TAXONOMY
;;; ======================================================================

    ( (#$taxonomy &rest)
      (lambda (fmode target args)
	(declare (ignore fmode target))
	(cond ((null args) (taxonomy))
	      ((singletonp args) (taxonomy (km-unique (first args))))
	      ((pairp args) (taxonomy (km-unique (first args)) (km-unique (second args))))
	      (t (report-error 'user-error
			       "Too many arguments to the taxonomy function! Format is (taxonomy <top-node> <relation-to-descend>)~%")))) )

;;; ======================================================================
;;;		ROLLBACK MECHANISM
;;; ======================================================================

    ( (#$checkpoint)
      (lambda (fmode target)
	(declare (ignore fmode target))
	(set-checkpoint) '#$(t)) )

    ( (#$checkpoint ?checkpoint-id)
      (lambda (fmode target checkpoint-id)
	(declare (ignore fmode target))
	(cond ((null checkpoint-id)
	       (report-error 'user-error "(checkpoint ~a): Argument to checkpoint can't be NIL!~%" checkpoint-id))
	      (t (set-checkpoint checkpoint-id) '#$(t)))))

    ( (#$undo)					; called only from within a program (km ...), NOT from the KM prompt
      (lambda (fmode target)
	(declare (ignore fmode target))
	(cond ((undo) '#$(t)))) )

;;; This is rather an ugly macro...oh well, let's leave it here
    ( (#$an #$instance #$of ?expr)
      (lambda (fmode target expr)
	(km-int `(#$an #$instance #$of ,expr #$with) :fail-mode fmode :target target :rewritep t)) )

    ( (#$an #$instance #$of ?expr #$with &rest)
      (lambda (fmode target expr slotsvals)
	(declare (ignore  fmode target))
	(cond ((are-slotsvals slotsvals)
	       (let* ( ; (classes (km-int expr :fail-mode 'error)) - OLD
		       (classes (km-int expr)) ; NEW - don't abort
		       (class (first classes))
		       (classes-in-slotsvals (vals-in (assoc '#$instance-of slotsvals)))
		       (new-slotsvals (cond ((>= (length classes) 2)
					     (update-assoc-list slotsvals `(#$instance-of ,(remove-duplicates (append (rest classes) classes-in-slotsvals)))))
					    (t slotsvals))) )
		 (cond ((or classes classes-in-slotsvals)	; if expr = NIL, return NIL (rather than error)
			(list (create-instance class new-slotsvals)))))))) )

    ( (#$reverse ?seq-expr)
      (lambda (fmode target seq-expr)
	(let ( (seq (km-unique-int seq-expr :fail-mode fmode :target target :rewritep t)) )
	  (cond ((null seq) nil)
		((km-seqp seq)
		 (list (cons '#$:seq (reverse (rest seq)))))
		(t (report-error 'user-error
				 "Attempting to reverse a non-sequence ~a!~%[Sequences should be of the form (:seq <e1> ... <en>)]~%"
				 seq-expr))))))

    ( (#$:default ?expr)			 ; strip off and ignore :default flag
      (lambda (fmode target expr)
;;;	(km-int expr :fail-mode fmode :target target :rewritep t)) )
	(declare (ignore fmode target expr))		; no - now ignore them
	(km-setq '*are-some-defaults* t)
	nil ))


;;; New and inert...
    ( (#$sometimes ?expr)
      (lambda (fmode target expr)
	(km-int expr :fail-mode fmode :target target :rewritep t)) )

    ( (#$anonymous-instancep ?expr)
      (lambda (fmode target expr)
	(declare (ignore fmode target))
	(cond ((anonymous-instancep (km-unique-int expr :fail-mode 'error)) '#$(t)))) )

;;; [1] below: NEW: Here make another top level call, so
;;;	(i) the trace is easier to follow during debugging
;;;	(ii) the looping checker jumps in at the right moment
;;; [1] e.g., user may want extra parentheses around maths: ((2 + 3) + (4)) should be a valid expression

    ( ?path
      (lambda (fmode0 target path)
	(declare (ignore target))
	   (cond ((atom path) 					; An instance/class evaluates to itself
                  (cond						; (This case is duplicated in km1 for efficiency)
		        ((no-reserved-keywords (list path)) 	; else no-reserved-keywords prints error
			 (list path))))
		 ((not (listp path))
		  (report-error 'program-error "Failed to find km handler for ~a!~%" path))	; should never happen!
		 ((singletonp path) (km-int (first path) :fail-mode fmode0))	; well...we'll let this linear path through, I guess :-( [1]

;; USER FUNCTIONS
		 ((and (triplep path)
		       (assoc (second path) *user-defined-infix-operators*))
		  (let ( (infix-implementation-fn (second (assoc (second path) *user-defined-infix-operators*))) )
		    (cond
		     ((not (functionp infix-implementation-fn))
		      (report-error 'user-error "
The specified implementation of infix operator ~a is not a Lisp function! (missing \"#'\" prefix?)
The specified implementation was: ~a~%" (second path) infix-implementation-fn))
		     (t (let* ( (x (vals-to-val (km-int (first path))))
				(y (vals-to-val (km-int (third path))))
				(answer0 (apply infix-implementation-fn (list x y)))
				(answer (listify answer0)) )
			  (cond ((every #'fully-evaluatedp answer) answer)
				(t (report-error 'user-error
					   "In call to external Lisp procedure
(~a ~a ~a)
Lisp procedure should return one/a list of fully evaluated KM objects (e.g.,
instances, or :seq/:bag/:pair of instances), but instead returned:
   ~a~%" infix-implementation-fn x y answer0))))))))
		 ((not *linear-paths*)
		  (report-error 'user-error "KM Syntax error: ~a is not a valid KM expression~%" path))
		 ((not (no-reserved-keywords path)) nil)	; ie. check that there are no reserved keywords
		     ((oddp (length path))      ; ODDP case: (last-el path) is a class, which filters the values
		      (cond ((structured-slotp (last-el (butlast path)))
			     (follow-multidepth-path 				        ; QUOTED PATH
			      (km-int (butlast (butlast path)) :fail-mode fmode0)    ; start-values
			      (last-el (butlast path))			        ; slot
			      (last-el path)				        ; target-class
			      :fail-mode fmode0))
			    (t (vals-in-class (km-int (butlast path) :fail-mode fmode0) ; REGULAR PATH
					      (last-el path)))))
		     ((evenp (length path))     ; EVENP case: (last-el path) is a slot, which generates values
		      (let* ( (frameadd (cond ((pairp path) (first path))		; (f s) -> f
					      (t (butlast path))))			; (f s f' s') -> (f s f')
			      (slot0 (last-el path)) )
			(cond ((structured-slotp slot0)
			       (follow-multidepth-path (km-int frameadd :fail-mode fmode0)
						       slot0 '* :fail-mode fmode0))   ; target-class = *
			      (t (let* ( (slot (cond ((pathp slot0) (km-unique-int slot0 :fail-mode 'error))
						     (t slot0)))
					 (fmode (cond ((built-in-aggregation-slot slot) 'fail)
						      (t fmode0)))
					 (frames (km-int frameadd :fail-mode fmode)) )
				   (cond ((not (equal frames (val-to-vals frameadd)))
					  (km-int `#$(,(VALS-TO-VAL FRAMES) ,SLOT) :fail-mode fmode))	; [1]
					 (t (km-multi-slotvals frames slot :fail-mode fmode)))))))))) )

    )
  ) ;; end part 2 of list

;; put the 2 lists together to create the big list
(setq
 *km-handler-alist*
 (append *km-handler-alist1* *km-handler-alist2*))


;;; ======================================================================
;;;		QUOTED PATHS eg.  (Delta owns Plane (part *) Wing)
;;;
;;; a quoted path is of form:
;;;		(...... <slot-structure> <target-class>)
;;; where <slot-structure> is of the form
;;;		(<slot> *)
;;;   or 	(<slot> * <depth-limit>)
;;; ======================================================================

;;; here path is necessarily an ODD length, thus the last element is a target CLASS.
(defun structured-slotp (slot)
  (and (listp slot) (eq (second slot) '*)))

(defun follow-multidepth-path (values structured-slot target-class &key (fail-mode 'fail))
  (declare (ignore fail-mode))
  (let ( (slot (first structured-slot))
	 (depth-limit (or (third structured-slot) *multidepth-path-default-searchdepth*)) )
    (cond ((null values) nil)
	  ((not (integerp depth-limit))
	   (report-error 'user-error "Non-integer depth ~a given for slot-structure ~a in quoted path!~%"
			 depth-limit structured-slot))
	  ((< depth-limit 1)
	   (report-error 'user-error "Depth ~a given for slot-structure ~a in quoted path must be >= 1!~%"
			 depth-limit structured-slot))
	  (t (vals-in-class (follow-multidepth-path0 values slot depth-limit) target-class)))))

; Note: The start-values AREN'T necessarily part of the solution, hence the extra :start-values keyword
(defun follow-multidepth-path0 (values slot depth-limit &key (start-values values) values-so-far)
  (cond ((<= depth-limit 0) values-so-far)
	((null values) values-so-far)
	(t (let* ((new-values (km-int `#$(the ,SLOT of ,(VALS-TO-VAL VALUES)) :fail-mode 'fail))
		  (novel-new-values (ordered-set-difference new-values (append start-values values-so-far)
							    :test #'equal)))
	     (follow-multidepth-path0 novel-new-values slot (1- depth-limit)
				      :start-values values :values-so-far (append values-so-far novel-new-values))))))

;;; ======================================================================
;;;		ACCESS TO THE KNOWLEDGE-BASE
;;; These functions make the bridge between km expressions (see
;;; *km-handler-alist* below) and the KB access function get-global.
;;; ======================================================================

;;; ---------------------------------------
;;;   1. The basic routine for getting slot values is km-multi-slotvals.
;;;	 It is given a *list* of frames, and gets their values.
;;; ----------------------------------------

;;; (km-multi-slotvals frames slot):
;;; frames will always be a list.
;;; Find and concatenate the vals of slot for frames.
;;; MUST return a *list* of values.  <- ?? Oct 97: No!
;;; Some special handling for slots like "sum" etc. which instead of
;;; 	looking up values of frames they *sum* the frames (which of
;;; 	course must thus be numbers)
(defun km-multi-slotvals (frames0 slot &key (fail-mode 'fail))
  (declare (ignore fail-mode))
  (let ( (frames (mapcar #'dereference frames0)) )
    (cond ((no-reserved-keywords frames)		; check for syntax errors
	   (km-multi-slotvals0 frames slot)))))

;;; Returns a *LIST* of values   ((car) && (joe bad xd))
(defun km-multi-slotvals0 (frames slot)
  (cond
   ((not (check-isa-slot-object slot)) nil)
   ((and (eq slot '#$number) (null frames)) '(0))
;  ((null frames) nil)		No! Let aggregation of zero items continue
   (t (case slot
	(#$unification (km-int (val-sets-to-expr (mapcar #'list frames) :single-valuedp t)))
	(#$set-unification (km-int (val-sets-to-expr (mapcar #'list frames))))	; less aggressive; not really getting sets
	(#$first (list (first frames)))
	(#$second (list (second frames)))
	(#$third (list (third frames)))
	(#$fourth (list (fourth frames)))
	(#$fifth (list (fifth frames)))
	(#$last (last frames))
	(#$number (list (length frames)))
	(#$bag `#$((:bag ,@FRAMES)))
	(#$seq `#$((:seq ,@FRAMES)))
	(#$most-specific (remove-subsumers frames))
	(#$most-general (remove-subsumees frames))
	(#$bag2seq (cond ((and (singletonp frames) (km-bagp (first frames)))
			  (list (cons '#$:seq (bag-to-list (first frames)))))
			 (t (report-error 'user-error
					  "(the bag2seq of ~a): argument should be a single bag." (vals-to-val frames)))))
	(#$seq2bag (cond ((and (singletonp frames) (km-seqp (first frames)))
			  (list (cons '#$:bag (seq-to-list (first frames)))))
			 (t (report-error 'user-error
					  "(the seq2bag of ~a): argument should be a single seq." (vals-to-val frames)))))
	(#$append (cond ((null frames) nil)
			((and (singletonp frames) (km-seqp (first frames)))
			 (let ( (appended (append-seqs (first frames))) )
			   (cond (appended (list appended)))))
			((and (singletonp frames) (km-bagp (first frames)))
			 (let ( (appended (append-bags (first frames))) )
			   (cond (appended (list appended)))))
			(t (report-error 'user-error
					 "(the append of ~a): argument should be a single sequence of sequences, or bag of bags!"
					 (vals-to-val frames)))))
	(t (cond
	    ((and (member slot '#$(min max))				; can apply this to sets, as well as bags
		  (not (singletonp frames)))
	     (cond ((null frames)
		    (report-error 'user-error
			"(the ~a of NIL): ~a should be given at least one value to operate on!~%"
			slot slot))
		   (t (case slot
			    (#$min (aggregate-vals #'min frames))
			    (#$max (aggregate-vals #'max frames))))))
	    ((and (member slot '#$(sum average))
		  (null frames))
	     '(0))
	    ((isa slot '#$Set-Aggregation-Slot)
	     (let ( (quoted-function-name (km-unique-int `#$(the aggregation-function of ,SLOT))) )
	       (cond
		((not quoted-function-name)
		 (report-error 'user-error "No aggregation-function definition given for the Aggregation-Slot ~a!~%" slot))
		((not (quotep quoted-function-name))
		 (report-error 'user-error
			   "Function definition for Aggregation-Slot ~a should be a~%quoted function (eg. \"(sum has (aggregation-function ('#'+)))\"~%"
			   slot))
		(t (let ( (function (eval (second quoted-function-name))) )
		     (cond
		      ((not (functionp function))
		       (report-error 'user-error
			     "Function definition for Aggregation-Slot ~a should be~%a function! (eg. \"(sum has (aggregation-function ('#'+)))\"~%"
			     slot))
		      (t (list (apply function (list frames))))))))))
	    ((null frames) nil)
	    ((singletonp frames) (km-slotvals (first frames) slot))
	    (t (my-mapcan 				 ; Deduping and dereferencing done later
		#'(lambda (frame)
;;; OLD		    (km-slotvals frame slot))
;		    (km-format t "Here! frames = ~a, frame = ~a, slot = ~a~%" frames frame slot)
#|NEW|#		    (km-int `#$(the ,SLOT of ,FRAME))) ; NEW: Route via top-level KM call for clarity during tracing
		frames))))))))				       ; by end of top-level km fn

(defun aggregate-vals (function vals)
  (cond ((and (null vals) (not (eq function #'+))) (km-int '#$(a Number) :fail-mode 'error))	; just for #'+, allow zero arguments.
	((every #'numberp vals) (list (apply function vals)))
	(t (km-int '#$(a Number) :fail-mode 'error))))

;;; ---------------------------------------
;;;   2. The auxiliary routine for getting the value of a slot is km-slotvals,
;;;	 which gets the slot values on a single frame. This is only used by
;;;	 kulti-slotvals.
;;; ----------------------------------------

;;; (km-slotvals frame slot)
;;;   - slot is atomic. Frame may be a kb-instance (including (:set ...) (:triple ...)) or a string or number
;;;   - return the evaluated *list* of values for the slot of frame.
;;; NOTE: frame is already assumed to be dereferenced (using dereference)
;;;     before this procedure is called.
;;; This procedure first filters special cases, then calls km-slotvals-from-kb
;;;	for handling standard queries.
(defun km-slotvals (frame slot &key (fail-mode 'fail))
  (cond ((null frame) nil)
	((or (km-triplep frame)		; special handling for triples, eg.
	     (km-pairp frame)
	     (km-functionp frame)
	     (quoted-expressionp frame))
	 (case slot 				 ; (the name of (:triple *john wants *cash))
	   (#$name  (list (km-name frame))) ; returns "john wants cash"
	   (#$(instance-of classes) (tidy-classes slot (immediate-classes frame :enforce-constraints t))) ; synonyms
	   (#$all-classes           (all-classes frame))
; No, just fail quietly I think.
;	   (t       (report-error 'user-error "I don't know how to take the ~a of a triple ~a!~%" slot frame))
	   ))
	((and (member slot '#$(min max))			; (the min of 3.5) = 3.5p
	      (not (km-bagp frame)))
	 (list frame))
	((member slot '#$(sum min max average difference product quotient))
	 (cond ((km-bagp frame)
		(let ( (frames (bag-to-list frame)) )
		  (case slot
			(#$sum (aggregate-vals #'+ frames))
			(#$average (cond ((and (every #'numberp frames)
					       (not (null frames)))
					  (list (/ (first (aggregate-vals #'+ frames)) (length frames))))
					 (t (km-int '#$(a Number) :fail-mode 'error))))
			(#$min (aggregate-vals #'min frames))
			(#$max (aggregate-vals #'max frames))
			(#$product (aggregate-vals #'* frames))
			(#$quotient (aggregate-vals #'/ frames))
			(#$difference (aggregate-vals #'- frames)))))
	       (t (report-error 'user-error
				"(the ~a of ~a): ~a should be given a bag (:bag ...) as an argument!~% [(the bag of <set>) will convert sets to bags]"
				slot frame slot))))
	((km-argsp frame)						; (the age of (:args Pete Clark)) -> (the age of Pete)
	 (km-int `#$(the ,SLOT of ,(SECOND FRAME)) :fail-mode fail-mode))
	((eq slot '#$elements)
	 (cond ((not (km-structured-list-valp frame))
		(report-error 'user-error "Trying to find the elements of a non-sequence/non-bag ~a!~%Continuing, returning (~a)...~%" frame frame)
		(list frame))
	       (t (flatten-sets (seq-to-list frame)))))			; strip :seq off
	((eq slot '#$seq-length)
	 (cond ((not (km-structured-list-valp frame))
		(report-error 'user-error "Trying to find the length of a non-sequence ~a!~%       (Use `number' not `length' to find the number of elements in a set)~%" frame frame))
	       (t (list (length (seq-to-list frame))))))
	((eq slot '#$bag-length)
	 (cond ((not (km-structured-list-valp frame))
		(report-error 'user-error "Trying to find the length of a non-bag ~a!~%       (Use `number' not `length' to find the number of elements in a set)~%" frame frame))
	       (t (list (length (bag-to-list frame))))))
	((km-functionp frame)
	 (report-error 'user-error "Trying to take the slot of a function (not allowed!)~%     Doing (the ~a of ~a)~%" slot frame))
	((km-structured-list-valp frame)			; :triple, :args, :function handled earlier
	 (list (cons (first frame) (my-mapcan #'(lambda (el)
						  (km-int `#$(the ,SLOT of ,EL) :fail-mode fail-mode))
					      (rest frame)))))
	((class-descriptionp frame)			; eg. '(every Dog)
	 (case slot
	       (#$instance-of '#$(Class))
	       (#$superclasses (list (first (class-description-to-class+slotsvals frame :fail-mode 'error))))
	       (t (report-error 'user-error "Sorry! I don't know how to compute the ~a of the class ~a!~%" frame slot))))
	((listp frame)
	 (report-error 'user-error "Trying to get a slot value of a list of frames,~%rather than a single frame. slot: ~a. frame: ~a.~%" slot frame))
	((case slot
	       (#$abs   	        (list (cond ((numberp frame)   (abs frame)) (t frame))))
	       (#$log   	        (list (cond ((numberp frame)   (log frame)) (t frame))))
	       (#$exp   	        (list (cond ((numberp frame)   (exp frame)) (t frame))))
	       (#$sqrt  	        (list (cond ((numberp frame)  (sqrt frame)) (t frame))))
	       (#$floor 	        (list (cond ((numberp frame) (floor frame)) (t frame))))
	       (#$(instance-of classes) (tidy-classes slot (immediate-classes frame :enforce-constraints t)))	; synonyms
	       (#$superclasses          (tidy-classes slot (immediate-superclasses frame)))
	       (#$subclasses            (tidy-classes slot (immediate-subclasses frame)))
	       (#$instances 	        (immediate-instances frame))
	       (#$supersituations       (immediate-supersituations frame))
	       (#$all-instances         (all-instances frame))
	       (#$all-prototypes        (all-prototypes frame))
	       (#$all-classes           (all-classes frame))
	       (#$all-superclasses      (all-superclasses frame))
	       (#$all-subclasses        (all-subclasses frame))
	       (#$all-supersituations   (all-supersituations frame))
	       (#$all-subslots          (all-subslots frame))
	       (#$all-superslots        (all-superslots frame))
       	       (#$full-all-instances    (full-all-instances frame))	; full-all-instances = all-instances + all-prototypes
	       (#$domain 	        (tidy-classes slot (domains-of frame)))
	       (#$range 	        (tidy-classes slot (ranges-of frame)))
	       (#$inverse 	        (list (invert-slot frame)))
	       (#$called	        (km-int (vals-to-val (append (get-vals frame '#$called :situation *global-situation*)
								  (get-vals frame '#$uniquely-called :situation *global-situation*)))
					     ))		; e.g. ((:set a b (<> c)))  -> (a b)
	       (#$uniquely-called       (km-int (get-vals frame '#$uniquely-called :situation *global-situation*)))
	       (#$cardinality	        (listify (cardinality-of frame)))
	       (#$fluent-status         (listify (fluent-status frame)))))
	((member slot *built-in-nonfluent-lookup-only-slots*)
	 (get-vals frame slot :situation *global-situation*))
	(t (km-slotvals2 frame slot :fail-mode fail-mode))))

(defun tidy-classes (slot vals)
  (cond ((remove-subsumers-slotp slot) (remove-subsumers vals))
	((remove-subsumees-slotp slot) (remove-subsumees vals))
	(t vals)))

(defun km-slotvals2 (frame slot &key (fail-mode 'fail))
  (cond ((not (kb-objectp frame))
	 (cond ((eq slot '#$name) (list (km-name frame)))		; special case, e.g., (the name of "cat")
	       (t (report-error 'user-error "(the ~a of ~a): Attempt to find a property of a non-kb-object ~a!~%" slot frame frame))))
	((already-done frame slot)		; Already done! So just retrieve cached value [NB Make sure you get it from the right situation!]...
	 (let ( (values (remove-constraints (get-vals frame slot :situation (target-situation (curr-situation) frame slot)))) )
	   (km-trace 'comment "(Retrieving answer computed and cached earlier:")
	   (km-trace 'comment " (the ~a of ~a) = ~a))" slot frame values)
	   values))
        ((check-situations-mode frame slot) nil)
;;; New check added to make sure there's no inferencing attempted on prototypes (unless in prototype mode)
	((and (protoinstancep frame)
	      (not (am-in-prototype-mode)))
	 (report-error 'user-warning
		       "Attempt to do inference on a protoinstance ~a when not in prototype mode!~%         Doing (the ~a of ~a). Continuing, just doing a get-vals rather than full inference...~%" frame slot frame frame slot)
	 (let ((vals (remove-constraints (get-vals frame slot :situation *global-situation*))))
	   (cond ((notevery #'fully-evaluatedp vals)
		  (report-error 'user-error
				"The (get-vals '#$~a '#$~a :situation *global-situation*) returned a structure which isn't fully evaluated!~%        ~a~%"
				slot frame (desource+decomment vals))))
	   vals))
	((prog1
	     (km-slotvals-from-kb frame slot :fail-mode fail-mode)
	   (do-postponed-classifications frame slot)))
	((eq slot '#$name)			; failed to compute it so generate it
	 (let ( (name (km-name frame)) )
	   (cond (name (put-vals frame slot (list name) :install-inversesp nil)
		       (list name)))))))

;;; ======================================================================
;;;		GENERAL UTILITIES
;;; ======================================================================

;;; (vals-in-class vals class): Return only those vals which are in class.
(defun vals-in-class (vals class)
  (cond ((eq class '*) vals)
	(t (remove-if-not #'(lambda (val) (isa val class)) vals :from-end t))))

;;; returns t if no reserved keywords, nil otherwise
(defun no-reserved-keywords (vals)
  (cond ((not (intersection vals *reserved-keywords*)))
	(t (report-error 'user-error
"Keyword(s) ~a found where concept name(s) were expected, within a
list of ~a KM expressions: ~a
(Error = missing parentheses?)~%"
			 (concat-list (commaify (mapcar #'princ-to-string (intersection vals *reserved-keywords*))))
;			 (mapcar #'list (intersection vals *reserved-keywords*))
		         (length vals)
                         (concat-list (commaify (mapcar #'princ-to-string vals)))))))
;                         (mapcar #'list vals)))))

;;; ======================================================================
;;;		Evaluate unquoted bits in a quoted expression:
;;; ======================================================================

;;; RETURNS a *single* km value (including possibly a (:set ...) expression)
(defun process-unquotes (expr &key (fail-mode 'fail))
  (cond ((null expr) nil)
	((not (listp expr)) expr)
	((eq (first expr) 'unquote)
	 (cond ((not (pairp expr))
		(report-error 'user-error "Unquoted structure ~a should be a pair!~%" expr))
	       (t (vals-to-val (km-int (second expr) :fail-mode fail-mode)))))
	(t (cons (process-unquotes (first expr))
		 (process-unquotes (rest expr))))))

;;; (append-seqs '#$(:seq (:seq 1 2) (:seq 3 4))) -> #$(:|seq| 1 2 3 4)
(defun append-seqs (seq-of-seqs)
  (cond ((or (not (km-seqp seq-of-seqs))
	     (notevery #'km-seqp (seq-to-list seq-of-seqs)))
	 (report-error 'user-error "(the append of ~a): value should be a sequence of sequences!"
		       seq-of-seqs))
	(t `(#$:seq ,@(my-mapcan #'seq-to-list (seq-to-list seq-of-seqs))))))

(defun append-bags (bag-of-bags)
  (cond ((or (not (km-bagp bag-of-bags))
	     (notevery #'km-bagp (bag-to-list bag-of-bags)))
	 (report-error 'user-error "(the append of ~a): value should be a bag of bags!"
		       bag-of-bags))
	(t `(#$:bag ,@(my-mapcan #'bag-to-list (bag-to-list bag-of-bags))))))

;;; ----------
;;; Spot ignored variables in *km-handler-alist*
;;; Just used by me for tidying up the code
(defun find-ignored ()
  (mapc #'(lambda (entry)
	    (let* ( (pattern+vars+body (minimatch entry '(?pattern (lambda ?vars &rest))))
		    (pattern (first pattern+vars+body))
		    (vars (second pattern+vars+body))
		    (body (third pattern+vars+body))
		    (flat-body (flatten body))
		    (ignored-vars (remove-if #'(lambda (var) (member var flat-body)) vars)) )
	      (mapc #'(lambda (ignored-var)
			(km-format t "pattern: ~a - variable ~a ignored~%" pattern ignored-var))
		    ignored-vars)))
	*km-handler-alist*)
  t)


;;; ---------- for Jerome...

(defun rules-for (slot frameadd &key retain-commentsp)
  (let* ( (frame (km-unique-int frameadd :fail-mode 'error)) )
    (val-sets-to-expr (append (own-rule-sets frame slot :retain-commentsp retain-commentsp)
			      (inherited-rule-sets frame slot :retain-commentsp retain-commentsp))
		      :single-valuedp (single-valued-slotp slot))))

;;; ======================================================================
;;;	QUANTIFICATION: I get bus errors if I include these verbatim in the handler-alist itself, and use KM in compiled mode.
;;;	This is an Allegro bug. So I need to separate out the bodies here. It seems to be the #'every and #'find-if calls which cause the problem.
;;; ======================================================================

(defun allof-must (var set test)
  (cond ((not (km-varp var))
	 (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$allof ,var #$in ,set #$must ,test)))
	((every #'(lambda (instance)
		    (km-int (subst instance var test)))
		(km-int set))
	 '#$(t))))

(defun allof-where-must (var set test2 test)
  (cond ((not (km-varp var))
	 (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$allof ,var #$in ,set #$where ,test2 #$must ,test)))
	((every #'(lambda (instance)
		    (km-int (subst instance var test)))
		(km-int `#$(allof ,VAR in ,SET where ,TEST2)))
	 '#$(t))))

(defun oneof-where (var set test)
	(cond ((not (km-varp var))
	       (report-error 'user-error "~a: Second argument should be a variable (e.g., ?x)!~%" `(#$oneof ,var #$in ,set #$where ,test)))
	      (t (let* ( (answer (find-if #'(lambda (member)
					      (let ( (test0 (subst member var test)) )
						(km-int test0)))
					  (km-int set))) )
		   (cond (answer (list answer)))))))


