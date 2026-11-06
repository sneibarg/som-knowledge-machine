
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: loadkb.lisp
;;; Author: Peter Clark
;;; Date: 21st Oct 1994

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defvar *creations* nil)
(defvar *logging-creations* nil)
(defconstant *checkpoint* 'checkpoint)
(defparameter *exclude-explanations-for-prototype-slots* nil)

(defvar *current-renaming-alist* nil)
(defvar *stats* nil)			; internal back door for keeping records
(defvar *filename-extensions*
  (car `(#+(and Symbolics Lispm)              ("lisp" . "bin")
         #+(and dec common vax (not ultrix))  ("LSP"  . "FAS")
         #+(and dec common vax ultrix)        ("lsp"  . "fas")
 	 #+ACLPC                              ("lsp"  . "fsl")
 	 #+CLISP                              ("lisp" . "fas")
         #+KCL                                ("lsp"  . "o")
         #+ECL                                ("lsp"  . "so")
         #+IBCL                               ("lsp"  . "o")
         #+Xerox                              ("lisp" . "dfasl")
	 ;; Lucid on Silicon Graphics
	 #+(and Lucid MIPS)                   ("lisp" . "mbin")
	 ;; the entry for (and lucid hp300) must precede
	 ;; that of (and lucid mc68000) for hp9000/300's running lucid,
	 ;; since *features* on hp9000/300's also include the :mc68000
	 ;; feature.
	 #+(and lucid hp300)                  ("lisp" . "6bin")
         #+(and Lucid MC68000)                ("lisp" . "lbin")
         #+(and Lucid Vax)                    ("lisp" . "vbin")
         #+(and Lucid Prime)                  ("lisp" . "pbin")
         #+(and Lucid SUNRise)                ("lisp" . "sbin")
         #+(and Lucid SPARC)                  ("lisp" . "sbin")
         #+(and Lucid :IBM-RT-PC)             ("lisp" . "bbin")
	 ;; PA is Precision Architecture, HP's 9000/800 RISC cpu
	 #+(and Lucid PA)		      ("lisp" . "hbin")
         #+excl ("cl"   . ,(pathname-type (compile-file-pathname "foo.cl")))
         #+(or :cmu :scl)  ("lisp" . ,(or (c:backend-fasl-file-type c:*backend*) "fasl"))
;	 #+(and :CMU (not (or :sgi :sparc)))  ("lisp" . "fasl")
;        #+(and :CMU :sgi)                    ("lisp" . "sgif")
;        #+(and :CMU :sparc)                  ("lisp" . "sparcf")
	 #+PRIME                              ("lisp" . "pbin")
         #+HP                                 ("l"    . "b")
         #+TI ("lisp" . #.(string (si::local-binary-file-type)))
         #+:gclisp                            ("LSP"  . "F2S")
         #+pyramid                            ("clisp" . "o")

	 ;; Harlequin LispWorks
	 #+:lispworks 	      ("lisp" . ,COMPILER:*FASL-EXTENSION-STRING*)
;        #+(and :sun4 :lispworks)             ("lisp" . "wfasl")
;        #+(and :mips :lispworks)             ("lisp" . "mfasl")
         #+:mcl                               ("lisp" . ,(pathname-type (compile-file-pathname "foo.lisp")))
         #+:coral                             ("lisp" . "fasl")

         ;; Otherwise,
         ("lisp" . ,(pathname-type (compile-file-pathname "foo.lisp")))))
  "Filename extensions for Common Lisp.
A cons of the form (Source-Extension . Binary-Extension). If the
system is unknown (as in *features* not known), defaults to what compile-file-pathname
produces.")

;;; ======================================================================
;;;			LOADING A KB
;;; ======================================================================

#|
load-kb Options:
   :verbose t	       		    - print out evaluation of expressions during load (useful for debugging a KB)
   :with-morphism <table> 	    - Experimental: table is a list of <old-symbol new-symbol> pairs.
				      Occurences of old-symbol are syntactically changed to new-symbol before
				      evaluation. See note [1] below.
   :eval-instances t		    - Force recursive evaluation of the slot-val expressions on the instances.
				      As a result, this creates the instance graph eagerly rather than lazily.
   :in-global t			    - Evaluate expressions in the global situation, not the current situation.

[1] SYMBOL RENAMING:
  This isn't quite right: a new symbol renaming table over-rides, rather than augments,
  any earlier symbol table. Also it's rather ugly with the global variable...update later...
  (load-kb "fred.km" :verbose t :with-morphism '((Node Elec-Device) (Arc Wire)))
  Symbol renaming is performed as a purely syntactic preprocessing step.
|#

(defun load-kb (file &key verbose with-morphism eval-instances load-patterns print-statistics silentp)
  (cond ((not silentp) (format t "Loading ~a...~%" file)))
  (reset-inference-engine)
  (let ((*logging* nil)			; switch off logging
	(*logging-creations* nil))
    (unwind-protect				; protect logging status in case syntax error in KB
	(progn
	  (let ((renaming-alist (cond (with-morphism (setq *current-renaming-alist*
						       (triples-to-alist with-morphism))
					*current-renaming-alist*)
				      (t *current-renaming-alist*)))
		(stream (open file :direction :input :if-does-not-exist nil)) )
	    (cond
	     ((null stream)
	      (cond (*am-reasoning* (report-error 'user-error (km-format nil "No such file ~a!~%" file)))
		    (t #|load-kb called from USER: prompt|# (km-format t "No such file ~a!~%" file)
		       (values nil (km-format nil "No such file ~a!~%" file)))))
	     (t (global-situation)
		(multiple-value-bind
		    (result error)
		    (load-exprs (case-sensitive-read-km stream nil nil) stream verbose renaming-alist
				eval-instances load-patterns)
		  (close stream)
		  (reset-done)		; remove all `already computed' flags
		  (cond (with-morphism (setq *current-renaming-alist* nil)))
		  (cond ((and error	  ;;; NOTE: Error will already have been caught AND reported by load-exprs
			 		  ;;; error is an error WITHIN the file being loaded.
			      (not (member (on-error) '(continue continue-silently ignore))))
			 (cond (*am-reasoning* (report-error 'user-error (format nil "Loading of ~a aborted!~%" file)))
			       (t (format t "Loading of ~a aborted!~%" file)
				  (values nil (format nil "Loading of ~a aborted!~%" file)))))
			(t (cond ((not silentp) (format t "~a loaded!~%" file)))
			   (cond (print-statistics (princ (report-statistics)) (terpri)))
			   (values result)))))))))))

;;; 1 March 06, Francis Leboutte
;;; Rewritten non recursively (mostly - see new auxiliary function load-expr)
;;;  o to fix a bug in LispWorks for Windows (stack overflow) when loading not that large
;;;    KM files
;;;  o this iterative version should be more efficient
;;;  o Note: first returned value is ignored in the caller
;;; 3/20/01 - rewritten to pass error back up to load-kb
(defun load-exprs (expr stream &optional verbose renaming-alist eval-instances load-patterns)
  (multiple-value-bind (result error)
      (load-expr expr stream verbose renaming-alist eval-instances load-patterns)
    (cond (result
           (loop
            (let ((expr (case-sensitive-read-km stream nil nil)))
              (multiple-value-bind (result error)
                  (load-expr expr stream verbose renaming-alist eval-instances load-patterns)
                (unless result
                  (return (values result error)))))))
          (t (values result error)))))

;;; Returns t if load successful
;;; NIL of expr = nil (signifies EOF; needs updating)
;;; (values nil error) if error occurred and on-error /= continue
(defun load-expr (expr stream &optional verbose renaming-alist eval-instances load-patterns)
  (let ((renamed-expr (rename-symbols expr renaming-alist)))
    (cond
     ((null renamed-expr) nil)
     ((and (listp renamed-expr)
           (eq (first renamed-expr) '#$symbol-renaming-table))
      (format t "(Symbol renaming table encountered and will be conformed to)~%")
      (load-expr (case-sensitive-read-km stream nil nil)
                 stream verbose (triples-to-alist (second renamed-expr))
                 eval-instances load-patterns))
     ((and load-patterns
           (notany #'(lambda (pattern)				; only do these
                       (minimatch renamed-expr pattern))
                   load-patterns))
      t)
     (verbose (print-km-prompt)
              (km-format t " ~a~%" renamed-expr)
	      (let ((*am-reasoning* nil))    ; was (reset-inference-engine), but *am-resoning* nil will trigger (r-i-e)
              (multiple-value-bind
                  (results error)
                  (km-eval-print renamed-expr :fail-mode *top-level-fail-mode*)
                (cond ((or eval-instances (am-in-prototype-mode)) (eval-instances results)))
                (cond ((and error (not (member (on-error) '(continue continue-silently ignore))))
		       (values nil error))
                      (t t)))))
     (t ; (reset-inference-engine) - no, let's keep the counter running for the whole KB
      (setq *catch-explanations* nil)	; but DO need these bits below reset
      (setq *instances-being-unified* nil)
      (setq *deferred-unifications* nil)
      (setq *failed-unification-attempts* nil)
      (cond (*catch-next-explanations*
             (setq *explanations* nil)
             (setq *catch-explanations* t)
             (setq *catch-next-explanations* nil)))
      (let ((*am-reasoning* nil))	; so (km '#$(load-kb ...)) will still make load-kb a top-level call
	(multiple-value-bind
	    (results error)
;           (km-eval renamed-expr :fail-mode *top-level-fail-mode*)
	    (km renamed-expr :reset-statistics nil)
	  (cond ((minimatch renamed-expr '#$(the ?slot of ?expr)) (setq *last-answer* results)))
	  (cond ((or eval-instances (am-in-prototype-mode)) (eval-instances results)))
	  (cond ((and error (not (member (on-error) '(continue continue-silently ignore))))
		 (values nil error))
		(t t))))))))

;;; ----------

(defun rename-symbols (expr renaming-alist) (sublis renaming-alist expr))

;;; '((1 -> a) (2 -> b)) -> ((1 . a) (2 . b))
;;;	                      ^   ^
;;;		           local global
;;; We do this conversion so that we can use built-in sublis to do the symbol renaming.
(defun triples-to-alist (triples)
  (cond ((quotep triples) (triples-to-alist (unquote triples)))
	((or (not (listp triples))
	     (not (every #'(lambda (x) (and (triplep x)
					    (symbolp (first x))
					    (eq (second x) '->)))
;					    (symbolp (third x))))
			 triples)))
	 (report-error 'nodebugger-error
		       ":with-morphism: renaming table should be a list of triples of the form~% ((OldS1 -> NewS1) (OldS2 -> NewS2) ...)~%"))
	(t (mapcar #'(lambda (triple)
	      (cond ((not (triplep triple))
		     (report-error 'nodebugger-error
				   "Non-triple found in the symbol renaming table!~%Non-triple was: ~a. Ignoring it...~%" triple))
		    (t (cons (first triple) (third triple)))))
		   triples))))

;;; ----------------------------------------
;; Useful macro, callable from top-level prompt.
(defun reload-kb (file &key verbose with-morphism eval-instances load-patterns)
  (reset-kb)
  (load-kb file :verbose verbose
	     :with-morphism with-morphism
	     :eval-instances eval-instances :load-patterns load-patterns))

;;; Same, callable from within KM
;(defun reload-kb0 (file &key verbose with-morphism eval-instances load-patterns)
;  (reset-kb)
;  (load-kb0 file :verbose verbose
;	        :with-morphism with-morphism
;		:eval-instances eval-instances :load-patterns load-patterns))

;;; ======================================================================
;;;		LOWEST-LEVEL ACCESS TO THE PROPERTY LISTS
;;; ======================================================================

;;; Converted to using hash table for KB-objects thanks to Adam Farquhar
(defvar *kb-objects* (make-hash-table :test #'eq))

(defun getobj (name0 facet)
 (let ((name (dereference name0)))
  (cond ((and (not (member facet *all-facets*))
	      (not (isa-situation-facet facet)))
	 (report-error 'program-error "(getobj ~a ~a) Don't recognize facet ~a!~%(Should be one of ~a)~%"
		       name facet facet *all-facets*))
	((kb-objectp name)
	 (setq *statistics-kb-access* (1+ *statistics-kb-access*))
	 (get name facet))	; new - add dereference
	((is-km-term name) nil)		; Valid get, but no attributes. This includes 1 'a "12" (:seq a b c) #'+ (:set a b c)
	((equal name name0)
	 (report-error 'program-error "Accessing frame ~a - the frame name `~a' should be an atom!~%" name name))
	(t (report-error 'program-error
			 "Accessing frame ~a (dereferences to ~a) - the frame name `~a' should be an atom!~%"
			 name0 name name)))))

;;; To DELETE an object, now use delete-frame (above).
;;; (putobj nil won't remove object from *kb-objects*)
(defun putobj (fname slotsvals facet)
  (cond ((and (not (member facet *all-facets*))
	      (not (isa-situation-facet facet)))
	 (report-error 'program-error "(putobj ~a ~a) Don't recognize facet ~a!~%(Should be one of ~a)~%" fname facet facet *all-facets*))
	(slotsvals ; (setf (get fname facet) slotsvals)        ;put it on the p-list
;		   (make-transaction `(setf ,fname ,facet ,slotsvals))        ;put it on the p-list
	           (km-setf fname facet slotsvals)
		   (km-add-to-kb-object-list fname))
	(t (km-remprop fname facet))))

;;; ======================================================================
;;;		ROLLBACK MECHANISMS
;;; ======================================================================

(defun reset-creations () (setq *creations* nil))

(defun start-creations-logging (&key (with-comment t))
  (cond (*logging-creations* (cond (with-comment (format t "(Logging of concept creations is already switched on)~%"))))
	(t (cond (with-comment (format t "(Started logging of concept creations)~%")))
	   (setq *logging-creations* t)))
  t)

(defun stop-creations-logging (&key (with-comment t))
  (cond ((not *logging-creations*) (cond (with-comment (format t "(Logging of concept creations is already switched off)~%"))))
	(t (cond (with-comment (format t "(Stopping logging of concept creations)~%")))
	   (setq *logging-creations* nil) (setq *creations* nil)))
  t)

(defun set-creations-checkpoint (&key (checkpoint-id *checkpoint*) (with-comment t) multiple-checkpoints)
  (cond ((not *logging-creations*)
	 (format t "WARNING! Trying to set-creations-checkpoint, but you should first call (start-creations-logging)!~%")
	 (format t "WARNING! I'll start creation's logging now for you.~%")
	 (start-creations-logging)))
  (cond ((not multiple-checkpoints) (reset-creations)))
  (push `(km-gensym-counter ,*km-gensym-counter*) *creations*)
  (push checkpoint-id *creations*)
  (cond (with-comment (format t "Creations checkpoint is set~%")))
  t)


;;; [1] can happen as description-subsumes-description does an (undo) hence can be added twice to the stack
;;; [2] Is bound to another item, so its body should have already been deleted by km-bind. Thus we just need to delete it directly,
;;;     but better do this *after* deleting everything for real, or else we might lose data. A -> B -> C, delete B, so now A dereferences to NIL
;;; [3] Need delete-frame rather than delete-frame-structure, as we want to delete inverse links too
(defun undo-creations (&key (checkpoint-id *checkpoint*) (with-comment t) remove-checkpoint dont-delete)

  ;; added by MW, 2012-04-26: we need more control over what gets deleted and what doesn't
  (etypecase dont-delete
    (null t)
    (hash-table t)
    (cons
     (let ((hash (make-hash-table)))
       (dolist (item dont-delete)
	 (setf (gethash item hash) t))
       (setf dont-delete hash))))

  (cond
   ((not *logging-creations*)
    (format t "Unable to undo concept creations - concept creations not switched on! Do (start-creations-logging) first.~%"))
   (*logging*
    (format t "You're not allowed to undo concept creations while logging is on! Do (stop-logging) first.~%"))
   (t (let ((cpu-start-time (get-internal-run-time))
	    (n-to-undo (position checkpoint-id *creations*)))
	(cond (with-comment (format t "Undo creations: starting~%")))
	(cond ((not n-to-undo)
	       (format t "Unable to undo concept creations - can't find checkpoint ~a to undo back to.~%" checkpoint-id)
	       (format t "Do (set-creations-checkpoint) to create a checkpoint.~%"))
	      (t (let ((creations-to-delete (make-hash-table)))		; create a quickly accessible list of creations to delete
		    (loop
			for i = (pop *creations*)			; will pop the checkpoint off *creations*, so put it back later [4]
			until (or (eq i checkpoint-id) (null i))
			when (or (not dont-delete) (not (gethash i dont-delete)))
			do (setf (gethash i creations-to-delete) t))
		    (let ((undesirable-deletions
			   (my-mapcan #'(lambda (retained-i)
					  (cond ((and ; (anonymous-instancep retained-i) - no, we can delete named instances too
						      (not (gethash retained-i creations-to-delete)) ; not going to delete it
						      (gethash (get-binding retained-i) creations-to-delete)) ; but it's bound to something to delete :-(
						 (remove-if-not #'(lambda (x) (gethash x creations-to-delete)) (dereference-chain retained-i)))))
				      (get-all-objects)))
			  (*show-comments* nil))
		      (cond (undesirable-deletions
			     (mapc #'(lambda (x)
				       (km-format t "   ~a created since checkpoint, but won't delete it (pre-checkpoint instance is unified with it)~%" x)
				       (remhash x creations-to-delete))
				   (remove-duplicates undesirable-deletions))))
		      (maphash (lambda (i v)
				 (declare (ignore v))
				 (cond ((not (anonymous-instancep i)) nil)
				       ((not (known-frame i))  nil) ; [1]
				       ((bound i) nil) 		    ; [2]
				       (t (delete-frame i :unintern t)))) ; [3]
			       creations-to-delete)
		      (maphash (lambda (i v)
				 (declare (ignore v))
				 (cond ((bound i) (delete-frame-structure i :unintern t)))) ; [2]
			       creations-to-delete)
		      (let ((km-gensym-counter (first *creations*)))
			(cond ((and (pairp km-gensym-counter)
				    (eq (first km-gensym-counter) 'km-gensym-counter)
				    (integerp (second km-gensym-counter)))
			       (setq *km-gensym-counter* (second km-gensym-counter))
			       (cond (remove-checkpoint (pop *creations*))
				     (t (push checkpoint-id *creations*))))		; [4]
			      (t (format t "ERROR! Failed to find number to reset *km-gensym-counter* to (Leaving it unchanged)~%"))))))
		 (clear-obj-stack)
		 (cond (with-comment (format t "Undo creations: ~a concepts deleted in ~,2f sec~%" n-to-undo
					     (/ (- (get-internal-run-time) cpu-start-time) internal-time-units-per-second))))
		 t))))))

;;; DOESN'T include i
(defun dereference-chain (i)
  (let ((i2 (get-binding i)))
    (cond (i2 (cons i2 (dereference-chain i2))))))

;;; From Michael Wessel 5/8/12
(defun get-km-creations (&key (checkpoint-id *checkpoint*))
   (cond
    ((not *logging-creations*)
     nil)
    (*logging*
     nil)
    (t (let* ((creations *creations*)
	     (n-to-undo (position checkpoint-id creations)))
	(cond ((not n-to-undo)
	       nil)
	      (t
	       (loop
		   for i = (pop creations)
		   until (or (eq i checkpoint-id) (null i))
		   collect i)))))))

;;; ======================================================================

#|
KM> (every man has (parts ((a Head))))
KM> (Pete has (instance-of (Man)))
KM> (undo)
Undone (Pete has (instance-of (Man)))...
KM>
|#

(defvar *history* nil)
; (defvar *logging* nil) - in header.lisp

(defun reset-history () (setq *history* nil))

(defun checkpoint-p (x) (and (pairp x) (equal (first x) *checkpoint*)))
(defun checkpoint-id (x) (second x))

(defun set-checkpoint (&optional (checkpoint-id 't))
  (cond ((or *logging* *internal-logging*) (push (list *checkpoint* checkpoint-id) *history*) t)))

;;; From Ken Murray
(defun next-checkpoint ()
  (second (first (member *checkpoint* *history* :key #'first))))

(defun undo-possible (&optional checkpoint-id)
  (cond (checkpoint-id (member (list *checkpoint* checkpoint-id) *history* :test #'equal))
	(t (assoc *checkpoint* *history*))))

;;; revise this: (undo <checkpoint-id>) will undo right back to <checkpoint-id> (if it exists)
;;; Returns NIL if no undo possible, <checkpoint-id> if so.
;;; If checkpoint-id = nil, then just undo to the last checkpoint.
;;; [1] When called from a program, need to do this. When called from KM> prompt, this is done automatically anyway
;;;     by (reset-inference-engine)
;;; [2] With *internal-logging*, the done flags ARE on the history trace and so undo0 will undo them. This is better
;;;     than undoing absolutely everything.
(defun undo (&optional checkpoint-id)
  (cond ((undo-possible checkpoint-id)
	 (cond ((not *internal-logging*) (reset-done)))		; [1] NB do BEFORE objects are forgotten! Also [2]
	 (undo0 *history* checkpoint-id))))

(defun undo0 (history checkpoint-id)
  (cond ((null history) 		; should never be encountered
	 (setq *history* nil)
	 (km-format t "Nothing more to undo!~%"))
	((and (checkpoint-p (first history))
	      (or (null checkpoint-id)
		  (equal checkpoint-id (checkpoint-id (first history)))))
	 (prog1
	     (checkpoint-id (first history))		; return the checkpoint-id associated with the checkpoint
	   (setq *history* (rest history))))
	(t (cond ((not (checkpoint-p (first history))) (undo1 (first history))))
	   (undo0 (rest history) checkpoint-id))))

(defun undo1 (command)
;  (km-format t "Undoing ~a...~%" command)
  (eval command))

;;; ----------

;;; This is how setf works: (setf (get symbol property) new-values)
(defun log-undo-command (command)
  (cond ((or *logging* *internal-logging*) (push command *history*))))

(defun start-logging (&key (with-comment t))
  (cond (*logging* (cond (with-comment (format t "(Logging of KM commands is already switched on)~%"))))
	(t (cond (with-comment (format t "(Started logging KM commands)~%")))
	   (setq *logging* t)))
  t)

(defun stop-logging (&key (with-comment t))
  (cond ((not *logging*) (cond (with-comment (format t "(Logging of KM commands is already switched off)~%"))))
	(t (cond (with-comment (format t "(Stopping logging of KM commands)~%")))
	   (setq *logging* nil) (setq *history* nil)))
  t)

;;; ----------

#|
Macro: Evaluate with no side-effects (Thanks to Francis Leboutte)
e.g., (keeping-kb
		(km '#$(a Car with (color (*red))))
		(km '#$(the color of (thelast Car))))
will remove the created Car after returning a result.
|#
(defmacro keeping-kb (&body body)
   `(let ((*logging* t))
      (set-checkpoint '%keeping-kb-cpid%)
      (multiple-value-prog1
          (progn ,@body)
        (undo '%keeping-kb-cpid%))))

;;; Make accessible from KM prompt
(add-lisp&KM-function 'keeping-kb)

 ;;; ----------

;;; Could optimize this if eval is too slow
(defun km-setq (variable value)
  (let ( (old-value (eval variable)) )
    (cond
     ((equal old-value value))
     (t (log-undo-command `(setq ,variable ',old-value))
	(eval `(setq ,variable ',value))))))		; need to unquote the variable

;;; (km-push 'a '*x*)
(defun km-push (value variable)
  (log-undo-command `(pop ,variable))
  (eval `(push ',value ,variable)))

;;; (km-pop '*x*)
(defun km-pop (variable)
  (let ((popped (first (eval variable))))
    (log-undo-command `(push ',popped ,variable))
    (eval `(pop ,variable))))

(defun km-setf (symbol property value)
  (let ( (old-value (get symbol property)) )
    (cond
     ((equal old-value value))
     (t (cond (old-value (log-undo-command `(setf (get ',symbol ',property) ',old-value)))
	      (t (log-undo-command `(remprop ',symbol ',property))))
	(cond ((null value) (remprop symbol property))
	      (t (setf (get symbol property) value)))))))

(defun km-remprop (symbol property)
  (let ( (old-value (get symbol property)) )
    (cond
;    ((null old-value))	- no!! even if value is nil, we still need to remprop to remove the symbol itself!
     (t (log-undo-command `(setf (get ',symbol ',property) ',old-value))
	(remprop symbol property)))))

(defun km-add-to-kb-object-list (fname)
  (cond ((not (gethash fname *kb-objects*))
	 (log-undo-command `(remhash ',fname *kb-objects*))
					;	 (km-format t "pushing ~a onto *creations*...~%" fname)
	 (cond (*logging-creations* (push fname *creations*)))
	 (setf (gethash fname *kb-objects*) t))))

(defun km-remove-from-kb-object-list (fname)
  (cond ((gethash fname *kb-objects*)
	 (log-undo-command `(setf (gethash ',fname *kb-objects*) t))
	 (remhash fname *kb-objects*))))

;;; Inverse For undo only
;(defun km-remhash-kb-objects (fname) (remhash fname *kb-objects*))
;(defun km-addhash-kb-objects (fname) (setf (gethash fname *kb-objects*) t))

;;; ======================================================================
;;;	get-all-objects -- update thanks to Francis Leboutte
;;; ======================================================================

#|
get-all-objects and get-all-concepts rewritten using do-objects macro
and using delete functions instead of remove
|#

;;; macro to loop in all the objects in *kb-objects*
;;; example: (do-objects object (print object))
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro do-objects (var &body body)
    `(maphash (lambda (,var v)
                (declare (ignore v))
                ,@body)
              *kb-objects*)))

;;; NOTE: We *don't* do dereferencing here, because we want to delete the old concepts with a (reset-kb)
;;; This list includes instances bound (pointing) to other instances AND deleted instances.
(defun get-all-objects ()
  (let ((results nil))
    (do-objects object
      (push object results))
    results))

;;; should be faster
;;; EXCLUDES comment tags. Here we *do* do a dereference, hence must remove non-kb-objects in the list (from unifications)
(defun get-all-concepts ()
  (let ((results nil))
    (do-objects object
      (let ((frame (dereference object)))
        (when (kb-objectp frame)			; NOTE: exclude user comments
          (push frame results))))
    (remove-duplicates results)))	; dereference may cause duplicates

;;; ------------------------------

;;; If t, we simply obliterate the frame's entire property list. The Lisp Manual advises that this is a relatively
;;; dangerous operation, as it may destroy important information that the implementation may happen to
;;; store in property lists.
;;; If NIL, we only delete the KM-specific properties, e.g., if the symbol is also used for other purposes.
(defparameter *fast-delete-frame-structure* nil)

;;; Note, is reversible (if *logging* is t)
;;; RETURNS: fname, or NIL if :unintern'ed
;;; NOTE: Be careful with :unintern t, because code references to fname will now reference fname in no package, rather than the KM package
(defun delete-frame-structure (fname &key (remove-from-kb-object-list t) unintern)
  (cond
   ((and *fast-delete-frame-structure* (not *logging*))
    (setf (symbol-plist fname) nil)
    (cond (unintern (km-unintern fname))
	  (t fname)))
   (t (km-remprops fname)
      (cond (remove-from-kb-object-list (km-remove-from-kb-object-list fname))) ; reversible
      (cond ((and (not *logging*) unintern) (km-unintern fname))
	    (t fname)))))

;;; Remove *all* properties on the property list
(defun km-remprops (symbol)
  (mapc #'(lambda (property)
	    (cond ((km-propertyp property) (km-remprop symbol property))))
	(odd-elements (symbol-plist symbol))))

(defun km-propertyp (property)
  (or (member property *all-facets*)
      (member property '(done cached-explanations ununify-data binding comment definition defined-instances defined-subclasses defined-prototypes explanation))
      (starts-with (symbol-name property) "OWN-")
      (starts-with (symbol-name property) "MEMBER-")
      (starts-with (symbol-name property) "EXPLANATION")))

;;; Rename this from "exists"; it really means fname is a known frame (Is an error to try this check for numbers and
;;; strings).
(defun known-frame (fname)
  (cond ((kb-objectp fname)
	 (or (gethash fname *kb-objects*)
	     (built-in-concept fname)))
	(t (report-error 'program-error "Attempt to check if a non kb-object ~a is a frame!~%" fname))))

(defun unusable-frame-name (fname) (known-frame fname))
;  (cond ((kb-objectp fname)
;	 (or (gethash fname *kb-objects*)
;	     (get-binding frame)			; [1]
;	     (built-in-concept fname)))
;	(t (report-error 'program-error "Attempt to check if a non kb-object ~a is a frame!~%" fname))))

;;; return the list of KM properties of symbol (KM properties only)
(defun km-symbol-plist (symbol)
  (loop for l on (symbol-plist symbol) by #'cddr
        as prop = (first l)
        when (km-propertyp prop)
        collect prop
        and
        collect (second l)))

;;; to put a list of properties on symbol
(defun put-list (symbol list)
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  (loop for l on list by #'cddr
        do
        (setf (get symbol (first l))
              (second l))))

;;; to put a list of properties on symbol - this is UNDOABLE
(defun km-put-list (symbol list)
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  (loop for l on list by #'cddr
        do
        (km-setf symbol (first l) (second l))))

;; --------------------

(defun reset-kb ()
  (let ((*logging* nil)
	(*logging-creations* nil))
    (global-situation)
    (instance-of-is-nonfluent)		; set it back
    (make-comment "Resetting KM...")
    (mapc #'(lambda (frame)
	      (delete-frame-structure frame))	; includes clearing explanations and cached-explanations
	  (get-all-objects))
    (clrhash *kb-objects*)
    (clear-obj-stack)
;   (clear-km-errors)
    (setq *curr-prototype* nil)
;   (setq *instances-with-cached-explanations* nil)	; not used any more
    (setq *classes-using-assertions-slot* nil) ; optimization flag
    (setq *are-some-subslots* nil)	; optimization flag
    (setq *are-some-prototypes* nil)	; optimization flag
    (setq *are-some-definitions* nil)	; optimization flag
    (setq *are-some-prototype-definitions* nil)	; optimization flag
    (setq *are-some-constraints* nil)	; optimization flag
    (setq *are-some-tags* nil)		; optimization flag
    (setq *are-some-defaults* nil)		; optimization flag
    (setq *am-in-situations-mode* nil)
; NO! Allow any change to persist.
;   (setq *built-in-remove-subsumers-slots* '#$(instance-of classes superclasses member-type)) ; in case user changes this
    (setq *visible-theories* nil)
    (setq *default-fluent-status* *default-default-fluent-status*)
    (setq *km-gensym-counter* 0)
;    (setq *clone-operation-id-counter* 0)
;    (setq *pid-counter* 0)
    (setq *max-padding-instances* 0)
    (setq *internal-logging* nil)
					; (reset-inference-engine)		; no, want to keep inference counter going!
    (enable-classification)
    (reset-history)
    (reset-creations)
    (clear-goal-stack)
    (reset-trace)
    (reset-trace-depth)
    (reset-done)
    t))

;;; [1] This should *always* be enabled EXCEPT during restoration of a saved-state.
;;; To be sure, we re-enable it with a (reset-inference-engine) call in case somehow
;;; there's an abort during a saved-state restoration, and we don't want to be left
;;; with installing-inverses disabled.
(defun reset-inference-engine ()
  (setq *postponed-classifications* nil)
; (setq *am-classifying* nil) - no longer used as a global so don't need to reset. Rather is always within lexical scoping
  (setq *catch-explanations* nil)
  (setq *internal-logging* nil)
  (setq *instances-being-unified* nil)
  (setq *deferred-unifications* nil)
  (setq *failed-unification-attempts* nil)
  (cond (*catch-next-explanations*
	 (setq *explanations* nil)
	 (setq *catch-explanations* t)
	 (setq *catch-next-explanations* nil)))
  (cond (*profiling* (profile-reset)))
  (clear-goal-stack)
  (reset-statistics)
  (reset-trace)
  (reset-trace-depth)
  (enable-installing-inverses))		; [1]

(defun clear-situations ()
  (let ((*logging* nil)
	(*logging-creations* nil))
    (reset-history)
    (reset-creations)
    (global-situation)
    (let ( (facets (my-mapcan #'(lambda (situation)
				  (mapcar #'(lambda (facet)
					      (curr-situation-facet facet situation))
					  (cons 'explanation *all-facets*)))
			      (remove *global-situation* (all-situations)))) )
      (mapc #'(lambda (frame)
		(cond ((isa frame '#$Situation)
		       (delete-frame frame))
		      ((intersection (symbol-plist frame) facets) ; i.e., has situation-specific info...
		       (mapc #'(lambda (facet) (remprop frame facet)) facets))))
	    (get-all-concepts))
      (setq *am-in-situations-mode* nil)
      t)))

;;; ======================================================================
;;;			SAVING A KB
;;; ======================================================================

(defun save-kb (file &key (reset-kb t) (include-explanationsp t))
  (let ( (stream (tell file)) )
    (write-kb :stream stream :reset-kb reset-kb :include-explanationsp include-explanationsp)
    (close stream)
    (format t "~a saved!~%" file) t))

;;; [1] We disable installing inverses so that, when restoring the KB state, we guarantee that
;;; the ordering of slot-vals on inverse slots is preserved (otherwise the install inverses
;;; procedure may change the ordering,
;;; e.g. SAVED: fsv', f'sv', v'invs(f'f) would restore as fsv', f'sv', v'invs(ff') without this.
;;; [2] Without this got the error: Error: During case-sensitive-read:
;;;			The symbol "*RECURSIVE-CLASSIFICATION*" is not external in the KM package. [file position = 93565677]
;;;     As the file contained KM:*RECURSIVE-CLASSIFICATION*", just ":" as *recursive-classification* was external during the save, but not during the load.
(defun write-kb (&key (stream *standard-output*) (objects (get-all-objects))
		      situations0 (reset-kb t) (include-explanationsp t))
  (cond
   ((and (not (streamp stream))
	 (not (eq stream t)))
    (report-error 'nodebugger-error
		  "write-kb given a non-stream as an argument!~%(Use (save-kb \"myfile\") to save KB to the file called \"myfile\")~%"))
   (t (let ((situations (or situations0 (all-situations)))
	    (*package* *km-package*))	; NOTE: Must be in KM package to remove the KM:: and KM: prefixes in the saved KB. [2]
	(multiple-value-bind
	 (concepts comment-tags)
	 (sort-objects-for-writing objects)
	 (format stream "~%;;; Current state of the KB (~a, KM ~a)~%" (now) *km-version-str*)
	 (cond ((singletonp situations0) (km-format stream ";;; Showing data for situation ~a only.~%~%" (first situations0)))
	       (situations0 (km-format stream "Showing data for situations ~a only.~%~%" situations0))
	       (t (cond ((and reset-kb (neq reset-kb '#$nil)) (format stream "~%(reset-kb)~%")))
		  (km-format stream "~%(disable-slot-checking)       ; (Temporarily disable while rebuilding KB state)~%")
		  (km-format stream "                              ; (Will be restored to original value by final SETQ statements)~%")
;;; NOTE: Below need to disable this even if *are-some-definitions* is nil at save-time, because it may be t at load-time
		  (km-format stream "~%(disable-classification)      ; (Temporarily disable while rebuilding KB state)~%")
		  (km-format stream "                              ; (Will be restored to original value by final SETQ statements)~%")
		  (km-format stream "~%(disable-installing-inverses) ; (Temporarily disable while rebuilding KB state)~%")	; [1]
		  (km-format stream "                              ; (Will be switched back on by (enable-installing-inverses) at the end)~%")
;;; Strictly redundant, as final SETQ statements will set this
;		  (cond ((member '#$instance-of *built-in-inertial-fluent-slots*)
;			 (km-format stream "~%(instance-of-is-fluent)~%")))
;		  (format stream "~%;;; ----------~%~%")
		  ))
; Note: need to write out taxonomy first because some ordering things, e.g., most-specific-first in frame-io.lisp
; when indexing definitions, need it.
; It gets redundantly written out a 2nd time in CONTENTS, but that's ok.
	 (km-format stream "~%;;; ---------- TAXONOMY ----------~%~%")
	 (mapc #'(lambda (concept)
		   (cond ((not (bound concept))
			  (save-frame concept :situations situations
				      :nulls-okayp nil  ; Don't write out "(_Car has...)" if no values
				      :stream stream
				      :slots-to-show '#$(superclasses))
;			  (princ ";;; ----------" stream)
;			  (terpri stream)
;			  (terpri stream)
			  )))
	       concepts)
	 (km-format stream "~%;;; ---------- CONTENTS ----------~%~%")
	 (mapc #'(lambda (concept)
		   (cond ((not (bound concept))
			  (save-frame concept :situations situations :nulls-okayp t :stream stream)
			  (princ ";;; ----------" stream)
			  (terpri stream)
			  (terpri stream))))
	       concepts)
	 (cond (include-explanationsp
		(km-format stream "~%;;; ---------- EXPLANATIONS ----------~%~%")
		(mapc #'(lambda (concept)
			  (cond ((not (bound concept))
				 (save-explanations concept :stream stream))))
		      concepts)
; Maybe not needed after all
;		(km-format stream "~%;;; ---------- DERIVATION CACHE ----------~%~%")
;		(mapc #'(lambda (concept)
;			  (cond ((not (bound concept))
;				 (save-explanations2 concept :stream stream))))
;		      concepts)
		))
	 (cond (comment-tags
		(km-format stream "~%;;; ---------- COMMENTS ----------~%~%")
		(mapc #'(lambda (comment-tag)
			  (km-format stream "~a~%~%" `(#$comment ,comment-tag ,@(get comment-tag 'comment)))
			  (princ ";;; ----------" stream)
			  (terpri stream)
			  (terpri stream))
		      comment-tags)))
; NO: Restore it with the SETQ statements at the end. It may that classification should stay off, if it was before.
;	 (cond (*are-some-definitions*
;	        (km-format stream "~%(enable-classification)     ;;; (Re-enable it after restoring KB state)~%")))
	 (km-format stream "~%;;; ----------------------------------------~%")
	 (km-format stream "~%(enable-installing-inverses)  ; (Re-enable it after restoring KB state)~%")
	 (write-behavior-variables stream)
	 (write-state-variables stream)
	 (format stream ";;; --- end (~a frames written) ---~%~%"  (length (remove-if #'bound objects))))))))

;;; Output to file;
;;; [1] WARNING! (format stream <string>) doesn't work if string contains a "~". So must do (format stream "~a" <string>)
;;; vals-to-show: any anonymous instance NOT in vals-to-show will NOT be written out
;;; save-prototypep: t if called by save-prototype in prototypes.lisp
(defun save-frame (concept &key (stream t) (situations (all-situations)) save-prototypep
		essentials partially-cloned-from slots-to-show (theories (all-theories)) nulls-okayp include-explanationsp)
  (cond ((not (is-km-term concept))
	 (report-error 'nodebugger-error "Doing (save-frame ~a) - the frame name `~a' should be a KB term!~%"
		       concept concept))
	(t (format stream "~a" (write-frame concept :situations situations :essentials essentials
					    :slots-to-show slots-to-show :partially-cloned-from partially-cloned-from
				    :save-prototypep save-prototypep :theories theories :nulls-okayp nulls-okayp)) ; [1]
	   (cond (include-explanationsp
		  (save-explanations concept :stream stream)
;		  (save-explanations2 concept :stream stream)
		  ))
	   t)))

;;; Specify explanation-types to restrict which ones to save (types are #$a, #$cloned-from, #$added-at, or
;;; #$projected-from). NIL = save all types.
(defun save-explanations (concept &key (stream t) essentials explanation-types)
  (mapc #'(lambda (isv-explanation)
	    (cond ((or (null explanation-types)
		       (member (explanation-type (fourth isv-explanation)) explanation-types))
		   (save-explanation isv-explanation :stream stream :essentials essentials))))
	(get-all-explanations concept nil)))

; isv-explanation = (<participant> <slot> <val> <expln>)
(defun save-explanation (isv-explanation &key (stream t) essentials)
  (cond
   ((and
     (or (null essentials)
	 (null (nonessentials-in isv-explanation :essentials essentials)))
     ;; added by MW-2011-06-24: don't save explanations for slots we don't care about
     (not (member (second isv-explanation) *exclude-explanations-for-prototype-slots*)))	; customizable parameter [temp hack]
    (km-format stream "(explanation (:triple ~a ~a ~a)~%  (~a))~%"
	       (first isv-explanation) (second isv-explanation) (third isv-explanation) (fourth isv-explanation)))
;   (t (km-format t "DEBUG: Dropping explanation containing a non-essential ~a:~%  ~a~%"
;		 (delistify (remove-duplicates (nonessentials-in isv-explanation :essentials essentials)))
;		 isv-explanation))
   ))

#|
Note: This function is ONLY called in the context of saving prototype explanations (detected
	by :essentials being non-nil), so we ASSUME we are in that context always.
Note: For efficiency we don't collect all the nonessentials, just the first we find (as we only care about their presence)
[1] A cloned-from explanation is a special case where we *do* allow a non-participant in the explanation:
	(cloned-from _ProtoDrive1 _Drive1 _ProtoCar1)   ; cloned from _ProtoCar1 in _ProtoDrive1 to _Drive1
    Here, the 2nd and 4th elements are the source protoinstance and protoroot respectively from which _Drive1 was built.
    So we only need to check _Drive1 is indeed a essential.
    For old explanation DBs, the third (and fourth) elements may be missing, hence the existence check (third explanation)
|#
(defun nonessentials-in (isv-explanation &key essentials)
  (let* ((triple (triple-in isv-explanation))
	 (i (first triple))
	 (v (third triple))
	 (explanation (explanation-in isv-explanation)))
    (cond ((not (member i essentials))
	   (report-error 'user-error
			 "(save-explanations ~a :essentials ~a): ~a should be in the list of essentials!~%"
			 isv-explanation essentials i)))
    (or (nonessentials-in-expr v :essentials essentials)		; v must be essential
	(case (explanation-type explanation)
	  (#$cloned-from (cond ((and (third explanation) ; [1]
				     (not (member (third explanation) essentials)))
				(list (third explanation)))))
	  (t (nonessentials-in-expr explanation :essentials essentials))))))

(defun nonessentials-in-expr (expr &key essentials)
  (cond ((member expr essentials) nil)		; Purely for efficiency (if expr is essential, then no nonessentials!)
	(t (set-difference (remove-if-not #'anonymous-instancep (flatten expr)) essentials))))

;;; This saves the 2nd type of explanations, namely cached expressions that an instance was derived from to prevent
;;; rederiving it a 2nd time. I *don't* think we need this though - it's purely an efficiency thing.
;(defun save-explanations2 (concept &key (stream t))
;  (mapc #'(lambda (cached-explanation)
;	    (km-format stream "(explained-by ~a ~a)~%" concept cached-explanation))
;	(cached-explanations-for concept)))

;;; Various variables about the current state, to write back so we can pick up
;;; where we left off if we reload...
(defun write-behavior-variables (&optional (stream t))
  (km-format stream "
;;; ----------------------------------------
;;;	KM'S INTERNAL BEHAVIOR PARAMETER VALUES
;;; ----------------------------------------

")
  (mapc #'(lambda (km-parameter)
	    (km-format stream "(SETQ ~s '~s)~%" km-parameter (eval km-parameter)))
	*km-behavior-parameters*)
  (km-format stream "~%"))

(defun write-state-variables (&optional (stream t))
  (km-format stream "
;;; ----------------------------------------
;;;	KM'S INTERNAL STATE PARAMETER VALUES
;;; ----------------------------------------

")
  (mapc #'(lambda (km-parameter)
	    (km-format stream "(SETQ ~s '~s)~%" km-parameter (eval km-parameter)))
	*km-state-parameters*)
  (km-format stream "~%"))

;;; ------------------------------

; [1] copy-seq as sort is destructive!
; [2] When reading (in-situation <S> ...) KM will check S is a situation, we
;     must ensure Situations are written out *first* so the check is passed at reload time.
(defun sort-objects-for-writing (objects0)
  (let* ( ; (prototypes (km-int '#$(the prototypes of (the all-subclasses of Thing))))
	  (comment-tags (remove-if-not #'user-commentp objects0))
	  (objects (remove-if #'user-commentp objects0))
	  (slot-classes (intersection (cons '#$Slot (all-subclasses '#$Slot)) objects))
	  (prototypes (remove-if-not #'prototypep objects))		; Doesn't involve the tracer (which is confusing to the user)
	  (situation-classes (cond ((member '#$Situation objects) (cons '#$Situation (all-subclasses '#$Situation)))))
	  (situation-instances (remove-if-not #'(lambda (situation)		; [2]
						  (isa situation '#$Situation))
					      objects))
	  (theory-classes (cond ((member '#$Theory objects)
				 (intersection (cons '#$Theory (all-subclasses '#$Theory)) objects))))
	  (theory-instances (remove-if-not #'(lambda (theory)		; [2]
						  (isa theory '#$Theory))
					      objects))
	  (rest-objects (ordered-set-difference objects0 (append slot-classes prototypes situation-classes situation-instances theory-classes
							theory-instances comment-tags))) )
    (values (append (sort (copy-seq slot-classes) #'string-lessp)
		    (sort (copy-seq theory-classes) #'string-lessp)
		    (sort (copy-seq theory-instances) #'string-lessp)
		    (sort (copy-seq situation-classes) #'string-lessp)
		    (sort (copy-seq situation-instances) #'string-lessp)
		    (sort (copy-seq prototypes) #'string-lessp)
		    (sort (copy-seq rest-objects) #'string-lessp))
	    (sort (copy-seq comment-tags) #'string-lessp))))

;;; ======================================================================
;;;		SAVING THE KB TO MEMORY (RATHER THAN DISK)
;;; ======================================================================

(defvar *stored-kb* nil)
(defun store-kb ()
  (let ( (now (now)) )
    (setq *stored-kb* (list now (get-kb)))
    (make-comment "State of KB stored (~a)~%" now)
    '#$(t)))

(defun restore-kb (&key unintern-symbols)
  (cond ((null *stored-kb*)
	 (format t "No stored KB state to restore!~%"))
	(t (put-kb (second *stored-kb*) :unintern-symbols unintern-symbols)
	   (make-comment "State of KB restored to that stored at ~a.~%" (first *stored-kb*))
	   '#$(t))))

;;; Return the KB as a massive data structure (!)
;;; More efficient implementation than before
(defun get-kb ()
 (let ((cpu-start-time (get-internal-run-time)))
  (prog1
    (append
     '((reset-kb))
     (copy-tree
      (mapcan #'(lambda (concept)
		  `((setf (symbol-plist ',concept) ',(symbol-plist concept))
		    (km-add-to-kb-object-list ',concept)))
	      (sort (get-all-objects) #'string<)))
     (mapcar #'(lambda (km-parameter)
		 `(setq ,km-parameter ',(eval km-parameter)))
	     (append *km-behavior-parameters* *km-state-parameters*)))
    (let* ((cpu-end-time (get-internal-run-time))
	   (cpu-time (/ (- cpu-end-time cpu-start-time) internal-time-units-per-second)))
      (make-comment "KB state gathered using get-kb (~a objects) in ~,2f secs" (length (get-all-objects)) cpu-time)))))

;;; [1] Note, copy-tree IS necessary. Jason Chaw found a case where doing (put-kb *x*), then a (reset-kb) via
;;; a second (put-kb *x*) would change *x* itself. Apparently *x* contained (setf (symbol-plist '|Move|) <struct>)
;;; resulting in the symbol plist being |Move| <struct>, or literally |Move| <pointer to <struct> in *x*>.
;;; Then (reset-kb) changed it to |Move| (done nil) which had the side-effect of ALSO replacing <struct> in *x* with
;;; (done nil).
;;; NOTE: Current KB is deleted by a call to (reset-kb), included at the first element of the exprs in kb
(defun put-kb (kb &key unintern-symbols)
  (make-comment "Restoring KB from stored state...")
  (let ((old-concepts (cond (unintern-symbols (get-all-concepts)))))
    (mapc #'eval (copy-tree kb))	; Note, includes (reset-kb) which clears the history list [1]
    (cond (unintern-symbols (mapc #'km-unintern (set-difference old-concepts (get-all-concepts)))))
    t))

;;; Returns NIL if uninterned, or the concept name otherwise.
(defun km-unintern (concept)
  (cond ((and (anonymous-instancep concept) ; steer clear of other possibly shared symbols
	      (null (symbol-plist concept))) ; not used by other s/w
;			      (km-format t "DEBUG: Uninterning ~a~%" concept)
	 (unintern concept *km-package*)
	 nil)
	(t concept)))

;;; Thanks to Francis Leboutte for this.
;;; This new version:
;;; - uses km-symbol-plist to make fastsave-kb portable (see comment below)
;;; - produces a more compact file
;;; - has a compile argument: to compile the fkm file.
;;;  Loading the compiled file should be faster. On LispWorks 4.4, fastloading a compiled file
;;;  instead of a fkm file is about 20% faster.
(defun fastsave-kb (file &key (reset-kb t) (compile nil))
  (let ((stream (tell file)))
    (when *using-km-package*
      (print '(in-package :km) stream))
    (let ((*package* (if *using-km-package* (find-package :km) *package*)))
      (when reset-kb
        (print '(reset-kb) stream))
;     (do-objects concept	- No, need the dereferenced list
      (mapc #'(lambda (concept)
        ;; setting the symbol-plist was not safe because a symbol's property list is a global
        ;; resource that can contain information established by unrelated programs - for example
        ;; by the LW compiler (and probably other Lisp compilers).
        ;; (print `(setf (symbol-plist ',concept) ',(symbol-plist concept)) stream)
		(cond ((not (bound concept))
		       (print `(put-list ',concept ',(dereference (km-symbol-plist concept))) stream) ; concept necessarily dereferenced as boundp = nil
		       (print `(km-add-to-kb-object-list ',concept) stream))))
;	    (get-all-concepts))
      	    (get-all-objects))
      (mapc #'(lambda (km-parameter)
                (print `(setq ,km-parameter ',(eval km-parameter)) stream))
            (append *km-behavior-parameters* *km-state-parameters*))
      (close stream)
      (format t "~a saved!~%NOTE: Load this file using (fastload-kb ~s), not (load-kb ~s)~%"
              file file file)
      (when compile
        (compile-file file))
      t)))

;;; This is for Francis, so the default compile option is "t"
(defun faslsave-kb (file &key (reset-kb t) (compile t))
  (fastsave-kb file :reset-kb reset-kb :compile compile))

;;; (fastload-kb "tmp") - this will have KM try extensions .fasl, .fkm, and .km in that order for the most recent
;;; Load fkm-file compiled if it exists and is not out-of-date,
;;; else load fkm-file (source).
;;; force-fkm: t, to load fkm-file (source) anyway.
(defun fastload-kb (fkm-file &key (force-fkm t))		; was nil
  (format t "Fast-loading ~a...~%" (pathname-name fkm-file))
  (let* ((file (if force-fkm
                   (progn (load fkm-file) fkm-file)
                 (load-b fkm-file))))	; load compiled version only if up to date
    (format t "~a loaded!~%" file)))

;;;; Older version
;(defun fastload-kb (file)
;  (format t "Fast-loading ~a...~%" file)
;  (load file)
;  (format t "~a loaded!~%" file))

;;; Load the compiled file if it exists and is not out-of-date,
;;; else load the (fkm - or lisp) file.
;;; File: a fkm or lisp file.
(defun load-b (file)
  (let ((compiled-file (make-pathname :defaults file
                                      :type (cdr *filename-extensions*))))
    (if (and (probe-file compiled-file)
             (>=  (file-write-date compiled-file)(file-write-date file)))
        (progn
	  (format t "Lisp-compiled version of this file is more recent, so loading that instead...~%")
	  (load compiled-file) compiled-file)
      (progn (load file) file))))

;;; ======================================================================
;;;	   LOAD NEWEST FUNCTIONS (Thanks to Francis Leboutte)
;;; ======================================================================

;;; load the most recent file among the km, fkm and compiled fkm files.
;;; File: a file name or pathname (with or without the file type - file type doesn't have
;;;  to be specified).
(defun load-newest-kb (file &key
                    (reset-kb nil)
                    verbose with-morphism eval-instances load-patterns)
  (flet ((date (file)
           (if (probe-file file)
               (file-write-date file)
             0)))
    (when reset-kb
      (reset-kb))
    (let* ((km-file (make-pathname :defaults file :type "km"))
           (fkm-file (make-pathname :defaults file :type "fkm"))
           (fasl-file (make-pathname :defaults file :type (cdr *filename-extensions*)))
           (km-file-date (date km-file))
           (fkm-file-date (date fkm-file))
           (fasl-file-date (date fasl-file))
;	   (dummy (km-format t "fasl-file = ~a~%" fasl-file))
           (loaded-file
            (cond ((and (>= fasl-file-date fkm-file-date)
                        (>= fasl-file-date km-file-date))
                   (load fasl-file)
		   (format t "~a loaded!~%" fasl-file))
                  ((>= fkm-file-date km-file-date)
                   (load fkm-file)
		   (format t "~a loaded!~%" fkm-file))
                  (t (load-kb km-file
                              :verbose verbose
                              :with-morphism with-morphism
                              :eval-instances eval-instances
                              :load-patterns load-patterns)))))
      (declare (ignore loaded-file))
;      (format t "~a loaded!~%" loaded-file)  - earlier load statements already do a print
      '#$(t)
      )))

; Done manually now earlier
; (add-lisp&KM-function 'load-newest-kb)

 ;;; ======================================================================
;;;	QUICK LOADING OF FILES WITH ONLY SIMPLE KM STRUCTURES IN
;;; ======================================================================

#|
These simple-loading functions directly access the KB database, rather than through
calls to KM. This simple-loading is limited:
  (i) detecting of redundant assertions by checking for duplicates, rather than subsumees.
 (ii) all slots asssumed multivalued
simpleload-kb will install inverses.
|#

(defun simpleload-kb (km-file &key (install-inversesp t))
  (format t "Simple-loading ~a...~%" km-file)
  (let ( (stream (see km-file)) )
    (loop while (simpleload-expr (case-sensitive-read-km stream nil nil) :install-inversesp install-inversesp))
    (close stream))
  (format t "~a read!~%" km-file))

(defun simpleload-expr (item &key (install-inversesp t))
  (cond ((null item) nil)
	((not (eq (second item) '#$has))
	 (report-error 'user-warning "simpleload-kb doesn't know how to process expression ~a! Ignoring it...~%" item)
	 t)    ; t to continue to next item
	(t (simple-add-slotsvals (first item) (rest (rest item)) :install-inversesp install-inversesp))))

;;; Faster version of frame-io.lisp routine
(defun simple-add-slotsvals (instance add-slotsvals &key (install-inversesp t))
  (let* ( (old-slotsvals (get instance 'own-properties))
	  (new-slotsvals (simple-compute-new-slotsvals instance old-slotsvals add-slotsvals :install-inversesp install-inversesp)) )
    (cond ((and (equal old-slotsvals new-slotsvals)      ; no changes needed
		(not (null add-slotsvals))))
	  (t (cond (new-slotsvals (setf (get instance 'own-properties) new-slotsvals)))))
    (cond ((not (gethash instance *kb-objects*))
	   (setf (gethash instance *kb-objects*) t))))
  instance)

(defun simple-compute-new-slotsvals (instance old-slotsvals add-slotsvals &key (install-inversesp t))
  (cond
   ((null old-slotsvals)
    (cond (install-inversesp (mapc #'(lambda (slotvals)
				       (cond ((not (non-inverse-recording-slot (slot-in slotvals)))
					      (simple-add-inverses instance (slot-in slotvals) (vals-in slotvals)))))
				   add-slotsvals)))
    add-slotsvals)
   (t (let* ( (old-slotvals (first old-slotsvals))
	      (slot	 (slot-in old-slotvals))
	      (old-vals	 (vals-in old-slotvals))
	      (add-vals	 (vals-in (assoc slot add-slotsvals)))
	      (extra-vals   (ordered-set-difference add-vals old-vals :test #'equal))
	      (new-vals 	 (append old-vals extra-vals)) )	; simpleer than subsumption checks in frame-io.lisp
	(cond ((and extra-vals install-inversesp (not (non-inverse-recording-slot slot)))
	       (simple-add-inverses instance slot extra-vals)))
	(cons (make-slotvals slot new-vals)
	      (simple-compute-new-slotsvals instance (rest old-slotsvals)
					  (remove-if #'(lambda (sv)
							 (eq (car sv) slot))
						     add-slotsvals)
					  :install-inversesp install-inversesp))))))

;;; [1] New - install inverses too
(defun simple-add-inverses (instance slot extra-vals)
  (let ( (inv-slot (invert-slot slot)) )
    (mapc #'(lambda (extra-val)
	      (cond ((and (kb-objectp extra-val)
			  (not (non-inverse-recording-concept extra-val)))
		     (let ( (old-invvals (get-vals extra-val inv-slot)) )
		       (cond ((not (member instance old-invvals))
			      (let ( (old-invslotsvals (get extra-val 'own-properties)) )
;				(km-format t "Doing (setf ~a ~a ~a)~%" extra-val 'own-properties
;					   (update-assoc-list old-invslotsvals
;							      (make-slotvals inv-slot (cons instance old-invvals))))
				(cond ((not (gethash extra-val *kb-objects*))
				       (setf (gethash extra-val *kb-objects*) t)))
				(setf (get extra-val 'own-properties)
				      (update-assoc-list old-invslotsvals
							 (make-slotvals inv-slot (cons instance old-invvals)))))))))))
	  extra-vals)))

;;; ======================================================================
;;;		KM VERSION NUMBER CONTROL
;;; ======================================================================

(defun requires-km-version (version-number-str)
  (cond ((km-version-greater-than version-number-str *km-version-str*)
	 (format t "~%Sorry! This KB requires KM version ~a or later.~%" version-number-str)
	 (format t "Please download the latest KM from the KM Web page at:~%")
	 (format t "     http://www.cs.utexas.edu/users/mfkb/km/~%~%")
	 (abort))
	(t '(|t|))))

;;; (km-version-greater-than "1.4.1.2" "1.4.1") -> t
(defun km-version-greater-than (v1 v2)
  (cond
   ((not (stringp v1))
    (report-error 'user-error
      "Bad KM version number ~a encountered (should be a dotted list of integers, e.g. \"1.4.3.1\")~%" v1))
   ((not (stringp v2))
    (report-error 'user-error
      "Bad KM version number ~a encountered (should be a dotted list of integers, e.g. \"1.4.3.1\")~%" v2))
   (t (let ( (v1-bits (mapcar #'read-from-string (break-up v1 '(#\.))))
	     (v2-bits (mapcar #'read-from-string (break-up v2 '(#\.)))) )
	(cond ((notevery #'integerp v1-bits)
	       (report-error 'user-error
		"Bad KM version number ~a encountered (should be a dotted list of integers, e.g. \"1.4.3.1\")~%" v1))
	      ((notevery #'integerp v2-bits)
	       (km-format t
		  "(requires-km-version: Can't check because KM version declaration is not a list of integers)~%")
	       (km-format t "(requires-km-version: Skipping requires-km-version check)~%"))
	      (t (km-version-bits-greater-than v1-bits v2-bits)))))))

;;; (km-version-bits-greater-than '(1 3 1) '(1 2 1 2)) -> t
;;; (km-version-bits-greater-than '(1 3 1) '(1 3)) -> t
;;; (km-version-bits-greater-than '(1 3) '(1 3)) -> NIL
;;; (km-version-bits-greater-than '(1 3 1) '(1 4)) -> NIL
(defun km-version-bits-greater-than (v1-bits v2-bits)
  (cond ((equal v1-bits v2-bits) nil)			; mustn't be the same
        ((null v2-bits))
	((and v1-bits (> (first v1-bits) (first v2-bits))))
	((and v1-bits (= (first v1-bits) (first v2-bits)))
	 (km-version-bits-greater-than (rest v1-bits) (rest v2-bits)))))


;;; ======================================================================
;;;	NEW: load files authored using the triple notation
;;; ======================================================================

;;; e.g., (load-triples "physics1.triples")
(defun load-triples (file)
  (format t "Loading ~a...~%" file)
  (cond ((load-triples0 (read-file file 'case-sensitive-sexpr))
	 (format t "~a loaded!~%" file))
	(t (format t "Loading of ~a aborted!~%" file)))
  t)

(defun load-triples0 (triples)
  (let ((non-triple (find-if #'(lambda (triple) (not (triplep triple))) triples)))
    (cond
     (non-triple (report-error 'nodebugger-error "load-triples: Non-triple ~a encountered in file!~%" non-triple))
     (t (let ((instances (remove-duplicates (mapcar #'first triples))))
	  (mapc #'(lambda (instance)
		    (let* ((itriples (remove-if-not #'(lambda (triple) (eq (first triple) instance)) triples))
			   (slots (remove-duplicates (mapcar #'second itriples))))
		      (mapc #'(lambda (slot)
				(let* ((istriples (remove-if-not #'(lambda (triple) (eq (second triple) slot)) itriples))
				       (values (remove-duplicates (mapcar #'third istriples))))
				  (cond ((kb-objectp instance) (km-unique `#$(,INSTANCE has (,SLOT ,VALUES)))) ; [1]
					(t (mapcar #'(lambda (value)
						       (cond
							((and (kb-objectp value)
							      (neq slot '#$instance-of))
							 (km-unique `#$(,VALUE has (,(INVERT-SLOT SLOT) (,INSTANCE)))))
							(t (report-error 'user-warning "Unable to assert triple (~a ~a ~a)! Dropping it...~%"
									 instance slot value))))
						   values)))))
			    slots)))
		instances)
	  t)))))

