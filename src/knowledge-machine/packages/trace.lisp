
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: trace.lisp
;;; Author: Peter Clark
;;; Purpose: Debugging facilities for KM

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; ======================================================================
;;;		    FOR TRACING EXECUTION
;;; ======================================================================

(defvar *trace-classify* nil)
(defvar *trace-other-situations* nil)
(defvar *trace-unify* nil)
(defvar *trace-subsumes* nil)
(defvar *trace-constraints* nil)
(defvar *suspended-trace* nil)
(defvar *interactive-trace* nil)

;;; new global variable
(defvar *trace-to-file?* nil
  "if true, the km traces are sent to the trace file
   set by (trace-to-file-on [<filename>]) and (trace-to-file-off) from lisp
   set by (t2f-on [<filename>]) and (t2f-off) from km")

;;; ----------------------------------------
;;; Thanks to Raphael Van Dyck for this extension to allow tracing output
;;; to be directed to a file.

;;; new global variable
(defvar *trace-file* "%trace.km"
  "default trace file")

;;; new function
(defun trace-to-file-on (&optional filename)
  (setf *trace-to-file?* t)
  (when filename
    (setf *trace-file* filename))
  (format t "(Trace-to-file switched on)~%")
  '#$(t))

;;; new function
(defun trace-to-file-off ()
  (setf *trace-to-file?* nil)
  (format t "(Trace-to-file switched off)~%")
  '#$(t))

;;; Synonyms
(defun t2f-on (&optional filename) (trace-to-file-on filename))
(defun t2f-off () (trace-to-file-off))

;;; ---------- error recording ----------

(defun tracekm ()
  (reset-trace)
  (cond (*trace* (format t "(Tracing of KM is already switched on)~%"))
	(t (format t "(Tracing of KM switched on)~%") (km-setq '*trace* t) (setq *interactive-trace* t)))
  t)

(defun untracekm ()
  (reset-trace)
  (cond (*trace* (format t "(Tracing of KM switched off)~%") (setq *trace* nil) (setq *interactive-trace* nil))
	(t (format t "(Tracing of KM is already switched off)~%")))
  t)

(defun reset-trace ()
  (cond ((or *trace* *interactive-trace*)   ; user may have temporarily switched off either of these during last tracing.
	 (setq *interactive-trace* t)
	 (setq *trace* t)))
;  (setq *depth* 0) 			; new - trace might be reset in middle of computation, so don't do this!
  (setq *suspended-trace* nil)
  (setq *trace-classify* nil)
  (setq *trace-subsumes* nil)
  (setq *trace-other-situations* nil)
  (setq *trace-unify* nil)
  (setq *trace-constraints* nil)
  t)

(defun reset-trace-depth ()
  (setq *depth* 0))

(defun tracep () *trace*)
(defun traceunifyp () *trace-unify*)
(defun tracesubsumesp () *trace-subsumes*)
(defun traceclassifyp () *trace-classify*)
(defun traceconstraintsp () *trace-constraints*)
(defun traceothersituationsp () *trace-other-situations*)


;;; ----------------------------------------
;;;	SPY POINTS
;;; ----------------------------------------

;;; [1] minimatch expects &REST, but user will type &rest at KM prompt.
(defun spy (&optional expr0)
  (let ( (expr (subst '&rest '#$&rest expr0)) )			; [1]
    (cond ((and expr
		(not (member expr *spypoints* :test #'equal)))
	   (setq *spypoints* (cons expr *spypoints*))))
    (cond (*spypoints* (km-format t "The tracer will automatically switch on when evaluating these expressions/patterns:~%~{      ~a~%~}"
				  (subst '#$&rest '&rest *spypoints*)))
	  (t (km-format t "(You have no spypoints declared)~%")))
    '#$(t)))

(defun unspy ()
  (setq *spypoints* nil)
  (km-format t "(All spypoints removed)~%")
  '#$(t))

;;; ======================================================================
;;;		     THE TRACE UTILITY
;;; ======================================================================

#|
OWN NOTES:
depth = 0
  call (the parts of *MyCar) -> depth = 1
NOW: suppose I type "s":
	- suspend-trace = 1, trace = nil
EXIT.
Next: if CALL then depth goes up to 2.
      if FAIL, or EXIT then depth stays 1, and suspend-trace -> nil, trace -> t.
	on exit, depth will go back down to 0.
      if COMMENT, depth is unchanged, and trace/suspend-trace is unchanged.

If I type "n", trace is permenantly switched off, EXCEPT *interactive-trace* is left on.
If I type "z", *interactive-trace* is switched permanently off, EXCEPT *trace* is left on.
|#

(defvar *trace-goal-stack* nil)

;;; RETURNS: 'redo or 'fail
(defun km-trace (mode string &rest args)
; (km-format t "Current situation = ~a~%" (curr-situation))
  (cond ((eq mode 'call) (increment-trace-depth)))
; The below condition is now achievable, if an error triggers the debugger to be switched on.
; (cond ((and *suspended-trace* (< *depth* *suspended-trace*))		; debug message
;	 (report-error 'program-error "trace depth somehow crept below that at which trace was suspended! Continuing...~%")))
  (cond ((and (not *trace*)
	      (not (eq mode 'comment))
	      *suspended-trace*
	      (<= *depth* *suspended-trace*))	; would be eq, but I want to continue if debug message above sounds.
	 (unsuspend-trace)))
  (prog1				; reset *depth* for FAIL/EXIT *after* messages, but return result of messages.
      (cond (*trace-goal-stack* (clear-screen) (show-goal-stack) nil)
	    (*trace* (let ((stream (cond (*trace-to-file?* (open *trace-file*
								 :direction :output
								 :if-does-not-exist :create
								 :if-exists :append))
					 (t))))
		       (prog1
			   (km-trace2 mode string args :stream stream)
			 (cond ((streamp stream) (close stream)))))))
    (cond ((or (eq mode 'exit)(eq mode 'fail)) (decrement-trace-depth)))))

(defun km-trace2 (mode string args &key (stream t))
; (format t "~vT" *depth*)			; Bug in Harlequin lisp causes this not to tab properly!
  (print-trace-message mode string args :stream stream)
  (cond ((and #|(not *trace-to-file?*)|# *interactive-trace* (neq mode 'comment))
	 (cond ((neq stream t) (print-trace-message mode string args :stream t)))	; repeat to TTY, if writing to file
	 (finish-output)			; flush output if stream is buffered
	 (let ( (debug-option
                 ;; RVA 21Aug2006 fix km rep loop input output problem
                 ;; reading line from nil (*standard-input*) instead of t (*terminal-io*)
                 (read-line nil nil nil)) )
	   (cond ((string= debug-option "s")
		  (cond ((eq mode 'call) 		   ; don't suspend on an EXIT, or depth will immediately creep below
			 (suspend-trace))))		   ; the suspended depth
		 ((string= debug-option "S")
		  (cond ((eq mode 'call)
			 (suspend-trace (1- *depth*)))))
		 ((string= debug-option "o") (untracekm))
		 ((string= debug-option "-A")
		  (format t "(Will no longer trace absolutely everything)~%")
		  (setq *trace-classify* nil)
		  (setq *trace-subsumes* nil)
		  (setq *trace-other-situations* nil)
		  (setq *trace-unify* nil)
		  (setq *trace-constraints* nil)
		  (km-trace2 mode string args :stream stream))
		 ((string= debug-option "a") (throw 'km-abort (list 'km-abort "User aborted from the debugger")))
		 ((string= debug-option "A") (untracekm) (throw 'km-abort (list 'km-abort "User aborted from the debugger")))
		 ((string= debug-option "r")
		  (cond ((eq mode 'call)   		   ; strictly redundant to redo on a call (ie. before it's even been tried)
			 (km-trace2 mode string args :stream stream))
			(t 'redo)))
		 ((string= debug-option "n") (setq *trace* nil) (setq *suspended-trace* nil))
		 ((string= debug-option "f") 'fail)
		 ((string= debug-option "g") (show-goal-stack) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "w")
		  (let* ( (last-expr (stacked-expr (first (goal-stack))))
			  (exprs (cond ((and (listp last-expr) (eq (second last-expr) '&)) (&-expr-to-vals last-expr))
				       ((and (listp last-expr) (eq (second last-expr) '&&)) (append-lists (&&-exprs-to-valsets (list last-expr))))
				       (t (list last-expr)))) )
		    (mapc #'(lambda (expr)
			      (let ( (paths (mapcar #'source-path (sources expr))) )
				(cond (paths (km-format t "~%Expression ~a originated from:~%~{   ~a~%~}" (desource-for-printing expr) paths))
				      (t (km-format t "~%(I don't know where expression ~a originated from)~%" expr)))))
			  exprs))
		  (terpri)
		  (km-trace2 mode string args :stream stream))
		 ((string= debug-option "z") (setq *interactive-trace* nil))

		 ((string= debug-option "+A")
		  (format t "(Will now trace absolutely everything)~%")
		  (setq *trace-other-situations* t)
		  (setq *trace-subsumes* t)
		  (setq *trace-unify* t)
		  (setq *trace-constraints* t)
		  (setq *trace-classify* t)
		  (km-trace2 mode string args :stream stream))
		 ((string= debug-option "+S")
		  (format t "(Will now show more detailed trace in other situations)~%")
		  (setq *trace-other-situations*   t) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "-S")
		  (format t "(Will no longer show a detailed trace in other situations)~%")
		  (setq *trace-other-situations* nil) (km-trace2 mode string args :stream stream))

		 ; This is for my own debugging, and not advertised to the user
		 ((string= debug-option "+M")
		  (format t "(Will now show more detailed trace for some subsumption tests)~%")
		  (setq *trace-subsumes*   t) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "-M")
		  (format t "(Will no longer show more detailed trace for some subsumption tests)~%")
		  (setq *trace-subsumes* nil) (km-trace2 mode string args :stream stream))

		 ((string= debug-option "+U")
		  (format t "(Will now show a more detailed trace during unification)~%")
		  (setq *trace-unify*   t) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "-U")
		  (format t "(Will no longer show a detailed trace during unification)~%")
		  (setq *trace-unify* nil) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "+C")
		  (format t "(Will now show a more detailed trace during constraint checking)~%")
		  (setq *trace-constraints* t) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "-C")
		  (format t "(Will no longer show a detailed trace during constraint checking)~%")
		  (setq *trace-constraints* nil) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "+X")
		  (format t "(Will now show more detailed trace during classification)~%")
		  (setq *trace-classify*   t) (km-trace2 mode string args :stream stream))
		 ((string= debug-option "-X")
		  (format t "(Will no longer show a detailed trace during classification)~%")
		  (setq *trace-classify* nil) (km-trace2 mode string args :stream stream))

		 ((starts-with debug-option "d ")
		  (format t "----------------------------------------~%~%")
		  (showme-frame (intern (trim-from-start debug-option 2) *km-package*))
		  (format t "----------------------------------------~%")
		  (km-trace2 mode string args :stream stream))
		 ((and (string/= debug-option "")
		       (string/= debug-option "c"))
		  (print-trace-options)
		  (km-trace2 mode string args :stream stream)))))
	(t (format stream "~%"))))

(defun print-trace-message (mode string args &key (stream t))
  (format stream "~a" *depth*)
  (format stream (spaces (- (1+ *depth*) (length (princ-to-string *depth*)))))
  (cond ((eq mode 'comment) (format stream " ")))		   ; extra space tabulation for comments
  (case mode
	((call redo comment) (apply #'km-format `(,stream ,string . ,(desource-for-printing args))))   ; ie. (km-format t string arg1 ... argn)
	((exit fail)
	 (format stream (truncate-string (apply #'km-format `(nil ,string . ,(desource-for-printing args))) 80)))	; TRUNCATE these particular strings, and add ""
	(t (report-error 'program-error "km-trace2: Unknown trace mode ~a!~%" mode))))

(defun increment-trace-depth ()
  (cond ((>= *depth* *statistics-max-depth*) (setq *statistics-max-depth* (1+ *depth*))))
  (setq *depth* (1+ *depth*)))
(defun decrement-trace-depth () (setq *depth* (1- *depth*)))

#|
;;; Iterate again, making sure counters stay unchanged.
(defun retrace (mode string &optional args)
  (cond ((eq mode 'call) (setq *depth* (1- *depth*))))	   ; (<- as it will be immediately incremented again)
  (apply #'km-trace `(,mode ,string . ,args)))		   ; ie. (km-trace mode string arg1 ... argn)
|#


#|
THIS IS WHAT QUINTUS PROLOG GIVES YOU
Debugging options:
 <cr>   creep      p      print         r [i]  retry i      @    command
  c     creep      w      write         f [i]  fail i       b    break
  l     leap       d      display                           a    abort
  s [i] skip i                                              h    help
  z     zip        g [n]  n ancestors   +      spy pred     ?    help
  n     nonstop    < [n]  set depth     -      nospy pred   =    debugging
  q     quasi-skip .      find defn     e      raise_exception
|#

(defun print-trace-options ()
  (format t "----------------------------------------
Debugging options during the trace:
 <cr>,c   creep       - single step forward
  g       goal stack  - print goal stack
  s       skip        - jump to completion of current subgoal
  w       where       - Show which frame the current rule came from
  S       big skip    - jump to completion of parent subgoal
  r       retry       - redo the current subgoal
  n       nonstop     - switch off trace for remainder of this query
  a       abort       - return to top-level prompt
  A       abort & off - return to top-level prompt AND switch off tracer
  o       trace off   - permenantly switch off trace
  f       fail        - return NIL for current goal (use with caution!)
  z       zip         - complete query with noninterative trace
  d <f>   display <f> - display (showme) frame <f>
  h,?     help        - this message

Also to show additional detail (normally not shown) for this query *only*:
  +S      in other situation(s)
  +U      during unification
  +C      during constraint checking
  +X      during classification
  +A      trace absolutely everything
  +M	  during subsumption testing
  -S,-U,-C,-X,-A,-M to unshow

Or from the KM prompt:
  KM> (trace)     switches on debugger
  KM> (untrace)   switches off the debugger
----------------------------------------
"))

#|
An abbreviated list:
Debugging options:                              Also show detailed inference:
 <cr>,c   creep      f    fail                  +C  during classification
  s       skip       z    zip (noninterative)   +S  in other situation(s)
  r       retry      g    show goal stack       +U  during unification
  n       nonstop    d F  display frame F       -C,-S,-U to unshow
  o       trace off  S    big skip (to completion of parent goal)
  h,?     help
|#

#|
NB MUSTN'T suspend/unsuspend unless trace was already on
This is ok:
  (cond ((and (tracep) (not (traceclassifyp))) (prog2 (suspend-trace) <foo> (unsuspend-trace)))
	(t <foo>))
This is not!
  (prog2 (suspend-trace) <foo> (unsuspend-trace))
because the (unsuspend-trace) will restart the trace, even if the
trace was already off ie. (suspend-trace) had no effect.

NOTE!! <foo> MUSTN'T be a function returning multiple values! prog2
seems to strip all but the first value off!
|#

;;; Suspend trace until exit the call at depth *depth*
(defun suspend-trace (&optional (depth *depth*))
  (setq *suspended-trace* depth)
  (setq *trace* nil))

;;; If we suspended the trace, but then the debugger kicked in again automatically, and
;;; then we switched off the trace (option "n"), we *don't* want to switch it back on again!
(defun unsuspend-trace ()
  (cond (*suspended-trace*
	 (setq *suspended-trace* nil)
	 (setq *trace* t))))

;;; ======================================================================
;;;		COMMENTS
;;; ======================================================================

(defun make-comment (string &rest args)
  (cond (*show-comments* (apply #'km-format `(t ,(concat "(COMMENT: " string ")~%") ,@(desource-for-printing args))))))

(defun comments ()
  (cond (*show-comments* (format t "(Display of comments is already switched on)~%"))
	(t (format t "(Display of comments is switched on)~%") (km-setq '*show-comments* t)))
  t)

(defun nocomments ()
  (cond (*show-comments* (format t "(Display of comments is switched off)~%") (km-setq '*show-comments* nil))
        (t ;; (format t "(Display of comments is already switched off)~%") turned off pointless message dm 8/18/11
           nil))
  t)

;;; ======================================================================
;;;		ERRORS
;;; ======================================================================
#|
OLD Behaviors on error - KM 2.1
  *error-report-silent*     - t: ignore the error and continue. Overrides abort-on-error-report
  *abort-on-error-report*   - t: report error and abort (NEW: now throwing the error message back too)
 			    - NIL: report error and switch on debugger at next opportunity

REVISED: 4/30/08 - KM 2.2 and later
*on-error*
	abort    	(report error and do not continue, instead immediately return NIL)
	abort-silently  (don't report error and do not continue, instead immediately return NIL)
	debug    	(report error and turn on KM debugger)
	break    	(report error and break to Lisp)
	continue 	(report error and continue)
	ignore   	(don't report error and do continue)

example:
(let ((*abort-on-error-report* t)           ; default is nil
      (*silently-abort-on-error-report* t)
      (*error-report-silent* nil))          ; default is nil
  (km `#$(the subclasses of Car)))
> 1. nil
  2. "ERROR! No values found for (the subclasses of Car)!"
|#

;;; For Jihie - to supress error reporting
;;; [3] Thanks to Francis Leboutte for *silently-abort-on-error-report*
;;;     Set or bind this variable to t in order to suppress the error message
;;;     printed in the console when *abort-on-error-report* is t
;(defvar *error-report-silent* nil)		 ; **** another NEW LINE
;(defvar *abort-on-error-report* nil)
;(defvar *silently-abort-on-error-report* t)	 ; [3] - new default is t

(defvar *on-error* 'debug)		; default mode
(defun on-error () *on-error*)


;;; FLE 02Aug2005: the call to km-format is conditioned to the value of
;;; *silently-abort-on-error-report*
;;; RETURNS: NIL
(defun report-error (error-type string0 &rest args0)
  ;;; We've changed report-error to allow an optional FIRST argument, giving the error DATA as a structure
  ;;; If that happens, then identification of the other arguments have to be shifted 1 right:
  (let ((error-data (cond ((stringp string0)	; if the structure isn't supplied, then use the top of the goal stack
			   (stacked-expr (first (goal-stack))))
			  (t string0)))
	(string (cond ((stringp string0) string0)
		      (t (first args0))))
	(args (cond ((stringp string0) args0)
		    (t (rest args0)))))
;  (unless *error-report-silent*
;  (unless (member (on-error) '(continue-silently ignore))
     (let* ((error-str-prefix (case error-type
                               (user-error "ERROR! ")
                               (user-warning "WARNING! ")
                               (program-error "PROGRAM ERROR! ")
                               (nodebugger-error "ERROR! ")
                               (abort-error "ERROR! ")
                               (t (format nil "ERROR! Error in report-error! Unrecognized error type ~a!~%" error-type))))
	    (continuation (cond ((eq (on-error) 'continue) "[Will continue though] ")
				(t "")))
	    (error-str (concat error-str-prefix continuation
			       (apply #'km-format `(nil ,string ,@(desource-for-printing args))))))
; 1. Print error message
       (cond ((not (member (on-error) '(continue-silently ignore abort-silently))) (format t error-str)))
; 2. Store error data
       (cond ((eq error-type 'user-warning) (push (trim-whitespace error-str) *warnings*))
	     (t (push (trim-whitespace error-str) *errors*)
		(push error-data *error-structures*)))
; 3. Further actions
;       (km-format t "(on-error) = ~a~%" (on-error))
       (cond ((member error-type '(user-warning nodebugger-error)) nil) ; no action
	     ((member (on-error) '(ignore continue-silently)) nil) ; no action
	     ((or			; *abort-on-error-report*
		 (member (on-error) '(abort abort-silently))
		 (eq error-type 'abort-error))
             ;; FLE 02Aug2005: when using (km `#$(...)) this message is generally
             ;; useless
;             (unless (eq (on-error) 'abort-silently) ; *silently-abort-on-error-report*
;               (km-format t "Throwing error...~a~%" error-str))
	      (throw 'km-abort (list 'km-abort error-str error-data))) ; now redundant throwing error-str, error-data back
							        ; Instead it's returned by *errors* and *error-structures*
	     ((eq (on-error) 'continue) nil)
	     ((and (member (on-error) '(debug break))
		   (member error-type '(user-error program-error)))
	      (cond ((and (not *trace*)
			  (not *suspended-trace*))
		    (format t "
	-------------------------
	**Switching on debugger**
Options include:
  g: to see the goal stack
  r: to retry current goal
  a: to abort
  o: to switch off debugger
  A: abort & off - return to top-level prompt AND switch off tracer
  ?: to list more options
	-------------------------

")))
	     (setq *trace* t)
	     (setq *interactive-trace* t)
	     (setq *suspended-trace* nil)
	     (cond ((or (eq (on-error) 'break) *developer-mode*) (break)))
	     nil)
	     ((not (member *on-error* '(abort abort-silently debug continue continue-silently ignore break)))
	      (km-format t "ERROR! *on-error* = ~a, but must be one of:
	debug    	  (report error and turn on debugger)
	abort    	  (report error and do not continue, instead immediately return NIL)
	abort-silently    (don't report error and do not continue, instead immediately return NIL)
	continue 	  (report error and continue)
	continue-silently (don't report error and continue)
	ignore		         [synonym for continue-silently]
	break    	  (report error and break to Lisp)
Aborting (as I don't know what error reporting mode to use for reporting an error with the error reporting mode!)~%"
		      *on-error*)
	      (abort))
            ;; FLE 03Aug2005, add this:
            (t (warn "Unknown KM error type: ~s" error-type)
               nil)))))

;;; ======================================================================
;;;		CATCHING THE TRACING INFORMATION
;;; ======================================================================

(defun catch-explanations ()
  (km-format t "(KM will catch the explanations for the next KM call)~%")
  (setq *explanations* nil)
  (setq *catch-next-explanations* t))

;;; [1] ((call [0]) (call [1]) (call [2]) (exit [2]) (fail [1]))
;;; ->  ((call [0])
(defun catch-explanation (kmexpr-with-comments mode)
  (cond
   ((not (and (listp kmexpr-with-comments)
	      (member (first kmexpr-with-comments) *no-decomment-headwords*)))
    (let* ( (comment-tags (get-comment-tags kmexpr-with-comments))
	    (explanations (mapcar #'(lambda (comment-tag) (get-comment2 comment-tag mode)) comment-tags)) )
      (cond ((and explanations *catch-explanations*)
	     (case mode
		   ((call exit)
		    (km-setq '*explanations* (cons `(,(1+ *depth*) ,mode ,comment-tags ,explanations) *explanations*)))
		   (fail (km-setq '*explanations* (trim-failed-explanations *explanations* (1+ *depth*) comment-tags))))))
      (cond ((and explanations *print-explanations*)
	     (mapc #'(lambda (explanation)
		       (km-format t "~vT~a: ~a~%" *depth* (string-upcase mode) explanation))
		   explanations)))))))

(defun trim-failed-explanations (explanations depth comment-tags)
  (cond ((endp explanations)
	 (report-error 'program-error "Fail encountered in the explanation stack without a matching call!~%Depth ~a, comment-tags ~a~%"
		       depth comment-tags))
	((and (= (first (first explanations)) depth)
	      (eq (second (first explanations)) 'call)
	      (equal (third (first explanations)) comment-tags))
	 (rest explanations))
	(t (trim-failed-explanations (rest explanations) depth comment-tags))))

; [1] 'html-format rather than 'html because 'html symbol clashes with new.html.generator :-(
(defun show-explanations-xml (&key (stream t)) (show-explanations :format 'xml :stream stream))
(defun show-explanations-html (&key (stream t)) (show-explanations :format 'html-format :stream stream)) ; [1]

;;; --------------------

(defvar *indent-level* 0)

(defun show-explanations (&key (explanations *explanations*) (format 'ascii) (stream t))
  (setq *indent-level* 0)
  (cond ((eq format 'xml) (format stream "<explanation-structure>~%")))
  (mapc #'(lambda (explanation-str)
	    (let ( (depth (first explanation-str))
		   (mode (second explanation-str))
		   (comment-tags (third explanation-str))
		   (explanations (fourth explanation-str)) )
	      (mapc #'(lambda (explanation) (show-explanation explanation depth mode comment-tags
							      :format format :stream stream)) explanations)))
	(reverse explanations))
  (cond ((eq format 'xml) (format stream "</explanation-structure>~%")))
  t)

(defun show-explanation (explanation depth mode comment-tags &key format (stream t))
  (declare (ignore comment-tags))
  (let ( (sentence (make-phrase (km explanation)))
	 (nl (cond (stream *newline-str*) (t ""))) )
    (case format
;	  (ascii (km-format stream (concat "~vT~a: ~a" nl) depth (string-upcase mode) sentence))
	  (ascii (prog2
		     (cond ((eq mode 'call) (setq *indent-level* (1+ *indent-level*))))
		     (format stream (concat (spaces (* 2 *indent-level*)) "* " sentence "~%"))
		   (cond ((eq mode 'exit) (setq *indent-level* (max 0 (1- *indent-level*)))))))
	  (xml (format stream (concat "<explanation depth=~a mode=~a>~a</explanation>" nl)
		       depth (string-downcase mode) sentence))
	  (html-format (case mode
		      (call (format stream (concat "<ul><li>~a" nl) sentence))
		      (exit (format stream (concat "<li>~a</ul>" nl) sentence))
		      (t (report-error 'program-error "show-error: Unrecognized mode ~a~%" mode))))
	  (t (report-error 'program-error "show-explanation: Unrecognized format ~a!~%" mode)))))

;;; --------------------

(defun grab-explanations-xml () (grab-explanations :format 'xml))
(defun grab-explanations-html () (grab-explanations :format 'html-format))

(defun grab-explanations (&key (explanations *explanations*) (format 'ascii))
  (setq *indent-level* 0)
  (append
   (cond ((eq format 'xml) (list (format nil "<explanation-structure>"))))
   (mapcan #'(lambda (explanation-str)
	      (let ( (depth (first explanation-str))
		     (mode (second explanation-str))
		     (comment-tags (third explanation-str))
		     (explanations (fourth explanation-str)) )
		(mapcar #'(lambda (explanation)
			    (show-explanation explanation depth mode comment-tags
					      :format format :stream nil))
			explanations)))
	   (reverse explanations))
   (cond ((eq format 'xml) (list (format nil "</explanation-structure>"))))))

;;; ----------------------------------------
;;;	SPY POINTS - for Jason Chaw
;;; ----------------------------------------

;;; [1] minimatch expects &REST, but user will type &rest at KM prompt.
(defun silent-spy (&optional expr0)
  (let ( (expr (subst '&rest '#$&rest expr0)) )			; [1]
    (cond ((and expr
		(not (member expr *silent-spypoints* :test #'equal)))
	   (setq *silent-spypoints* (cons expr *silent-spypoints*))))
    (cond (*silent-spypoints* (km-format t "KM will log subgoals when evaluating these expressions/patterns:~%~{      ~a~%~}"
				  (subst '#$&rest '&rest *silent-spypoints*)))
	  (t (km-format t "(You have no silent spypoints declared)~%")))
    '#$(t)))

(defun silent-unspy ()
  (setq *silent-spypoints* nil)
  (km-format t "(All silent spypoints removed)~%")
  '#$(t))

(defun inspect-silent-spy-log()
  *silent-spypoints-log*)

(defun clear-silent-spy-log()
  (setq *silent-spypoints-log* nil))

