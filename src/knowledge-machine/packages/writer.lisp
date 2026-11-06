
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: writer.lisp
;;; Author: Peter Clark
;;; Date: Mar 1996 spliced out later
;;; Purpose: Copy of updated write-frame from server/frame-dev.lisp

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; frame can be *any* valid KM term, including strings, numbers, sets, sequences, functions, and normal frames.
;;; RETURNS: A string containing the printed form of the frame.
(defun write-frame (frame &key (situations (all-situations)) (theories (all-theories)) htmlify nulls-okayp
			       essentials partially-cloned-from slots-to-show save-prototypep)
  (cond
   ((and (kb-objectp frame) (bound frame)) (km-format nil ";;; (~a is bound to ~a)~%~%" frame (dereference frame)))
   (t (let ( (frame-string (write-frame0 frame situations theories htmlify essentials
					 partially-cloned-from slots-to-show save-prototypep)) )
	(cond ((string/= frame-string "") frame-string)
	      ((built-in-concept-type frame)
	       (concat (km-format nil ";;; (Concept ~a is a built-in " frame)
		       (built-in-concept-type frame)
		       (format nil ")~%~%")))
	      (nulls-okayp
	       (km-format nil "(~a has)~%~%" frame))
	      ((and (null slots-to-show)
		    (null (set-difference (all-situations) situations))
		    (null (set-difference (all-theories) theories)))
	       (km-format nil ";;; (Concept ~a is not declared anywhere in the KB)~%~%" frame))
	      ((and (null slots-to-show)
		    (null (all-theories)))
	       (km-format nil ";;; (Concept ~a is not declared in the situations ~a)~%~%" frame situations))
	      ((null slots-to-show)
	       (km-format nil ";;; (Concept ~a is not declared in the situations ~a nor the theories ~a)~%~%" frame situations theories))
	      (t ""))))))

(defun write-frame0 (frame &optional (situations (all-situations))
		     (theories (all-theories)) htmlify essentials partially-cloned-from slots-to-show save-prototypep)
  (cond ((stringp frame) (km-format nil ";;; (~a is a string)~%~%" frame))
	((numberp frame) (km-format nil ";;; (~a is a number)~%~%" frame))
	((descriptionp frame) (km-format nil ";;; (~a is a quoted expression)~%~%" frame))
	((km-seqp frame) (km-format nil ";;; (~a is a sequence)~%~%" frame))
	((km-setp frame) (km-format nil ";;; (~a is a set)~%~%" frame))
	((km-argsp frame) (km-format nil ";;; (~a is an argument list)~%~%" frame))
	((functionp frame) (km-format nil ";;; (~a is a Lisp function)~%~%" frame))
	((kb-objectp frame)
	 (concat-list
	  (cons (cond ((member *global-situation* situations)		; do *Global first
		       (write-frame-in-situation frame *global-situation* :htmlify htmlify :essentials essentials
						 :partially-cloned-from partially-cloned-from :slots-to-show slots-to-show
						 :save-prototypep save-prototypep))
		      (t ""))
		(append
		 (let ( (prototypes (get-vals frame '#$prototypes :situation *global-situation*)) )
		   (cond ((and prototypes (null slots-to-show))
			  (append (list (km-format nil "#|"))
				  (mapcan #'(lambda (prototype)
					      (cons (km-format nil "~%;;; Prototype ~a defined by:~%" prototype)
						    (mapcar #'(lambda (expr)
;								(km-format nil "~a~%" expr))
								(concat (expr2string expr htmlify) (format nil "~%")))
							    (dereference (get prototype 'definition)))))
					  prototypes)
				  (list (km-format nil "|#~%~%"))))))
		 (mapcar #'(lambda (theory)
			     (write-frame-in-situation frame theory :htmlify htmlify :theoryp t :essentials essentials
						       :partially-cloned-from partially-cloned-from
						       :slots-to-show slots-to-show :save-prototypep save-prototypep))
			 theories)
		 (append
		  (flatten (write-situation-specific-assertions frame :htmlify htmlify))
		  (mapcar #'(lambda (situation)
			      (write-frame-in-situation frame situation :htmlify htmlify :essentials essentials
							:partially-cloned-from partially-cloned-from
							:slots-to-show slots-to-show :save-prototypep save-prototypep))
			  (remove *global-situation* situations)))))))
	(t (report-error 'user-error "~a is not a KB object!~%" frame))))

(defun write-situation-specific-assertions (situation-class &key htmlify)
  (cond
   ((is-subclass-of situation-class '#$Situation)
    (let ( (assertions (second (assoc '#$assertions
				      (desource-for-printing (get-slotsvals situation-class :facet 'member-properties :situation *global-situation*))))) )
      (cond (assertions
	     (mapcar #'(lambda (assertion)
			 (cond ((not (quotep assertion))
				(report-error 'user-error "Unquoted assertion ~a in situation-class ~a! Ignoring it...~%"
					      assertion situation-class) "")
			       (t (let ( (modified-assertion (sublis '#$((SubSelf . Self) (#,Self . TheSituation)) (second assertion)
								     :test #'equal)) )
				    (list (km-format nil "(in-every-situation ")
					  (objwrite situation-class htmlify)
					  (km-format nil "~%  ")
					  (objwrite modified-assertion htmlify)
					  (km-format nil ")~%~%"))))))
		     assertions)))))))


;;; If no data, then returns ""
(defun write-frame-in-situation (frame situation
				 &key htmlify theoryp essentials partially-cloned-from slots-to-show save-prototypep)
  (let ( (own-props (desource-for-printing (get-slotsvals frame :facet 'own-properties    :situation situation)))
	 (mbr-props (desource-for-printing (get-slotsvals frame :facet 'member-properties :situation situation)))
	 (own-defn  (desource-for-printing (get-slotsvals frame :facet 'own-definition    :situation situation)))
	 (mbr-defn  (desource-for-printing (get-slotsvals frame :facet 'member-definition :situation situation))) )
    (concat
     (cond (own-defn
	    (concat-list
	     (flatten
	      (write-frame2 frame situation own-defn  nil '#$has-definition :htmlify htmlify :theoryp theoryp
			    :essentials essentials :partially-cloned-from partially-cloned-from
			    :slots-to-show slots-to-show :save-prototypep save-prototypep)))))
     (cond ((and own-props
		 (not (and (singletonp own-props) (eq (first (first own-props)) '#$assertions)))) ; filter out these!
	    (concat-list (flatten (write-frame2 frame situation own-props nil '#$has :htmlify htmlify :theoryp theoryp
						:essentials essentials :partially-cloned-from partially-cloned-from
						:slots-to-show slots-to-show :save-prototypep save-prototypep)))))
     (cond (mbr-defn  (concat-list (flatten (write-frame2 frame situation mbr-defn  '#$every '#$has-definition
					  :htmlify htmlify :theoryp theoryp :essentials essentials
					  :partially-cloned-from partially-cloned-from
					  :slots-to-show slots-to-show :save-prototypep save-prototypep)))))
     (cond ((and mbr-props
		 (not (and (singletonp mbr-props) (eq (first (first mbr-props)) '#$assertions)))) ; filter out these!
	    (concat-list (flatten (write-frame2 frame situation mbr-props '#$every '#$has :htmlify htmlify
					:theoryp theoryp :essentials essentials
					:partially-cloned-from partially-cloned-from
					:slots-to-show slots-to-show :save-prototypep save-prototypep))))))))

;;; theoryp = 'ignore suppresses the (in-theory ... ) wrapper, but we ignore that for now
(defun write-frame2 (frame situation slotsvals0 quantifier joiner
		     &key htmlify theoryp essentials partially-cloned-from slots-to-show save-prototypep (tab 0))
  (let ( (slotsvals (dereference slotsvals0))
	 (tab2 (cond ((eq situation *global-situation*) tab)
		    (t (+ 2 tab)))) )
    (cond
     ((or (null slots-to-show)
	  (intersection slots-to-show (mapcar #'slot-in slotsvals)))
      (list
          (cond ((and (neq situation *global-situation*) (neq theoryp 'ignore))
		 (list (cond ((eq theoryp t) (km-format nil "(in-theory "))
			     (t (km-format nil "(in-situation ")))
		       (objwrite situation htmlify)
		       (km-format nil "~%"))))
	  (cond ((not (= tab2 0)) (format nil "~vT" tab2)))    ; (format nil "~vT" 0) prints one space (Lisp bug?)
	  (cond (quantifier (km-format nil "(~a " quantifier))  	; "(every "
		(t "("))
	  (objwrite frame htmlify)
	  (km-format nil " ~a " joiner)				; "has" or "has-definition"
	  (write-slotsvals slotsvals (+ tab2 2) htmlify essentials partially-cloned-from slots-to-show save-prototypep)
	  ")"
	  (cond ((and (neq situation *global-situation*)
		      (neq theoryp 'ignore)) ")"))
	  (format nil "~%~%")))
     (t ""))))

(defun write-slotsvals (slotsvals &optional (tab 2) htmlify essentials partially-cloned-from slots-to-show save-prototypep)
  (mapcar #'(lambda (slotvals)
	      (cond ((or (null slots-to-show)
			 (member (slot-in slotvals) slots-to-show))
		     (write-slotvals slotvals tab htmlify essentials partially-cloned-from save-prototypep))))
	  slotsvals))

;;; essentials is the special flag from AURA to only PARTIALLY save the prototypes (just the essential elements)
(defun write-slotvals (slotvals &optional (tab 2) htmlify essentials partially-cloned-from save-prototypep)
  (cond ((null slotvals) (format nil " ()"))
	((eq (slot-in slotvals) '#$assertions) "")
	((and save-prototypep ; DROP cloned instances for modularity. Will be reinstalled as inverses when clones reloaded.
;	      (member (slot-in slotvals) '#$(has-clones has-built-clones))
	      (member (slot-in slotvals) *prototype-slots-not-to-save-to-file*))
	 "")
	(essentials
	 (let* ((slot (slot-in slotvals))
		(vals (vals-in slotvals))
		(skolem-vals (remove-if-not #'anonymous-instancep (flatten vals)))
		(vals2 ; vals2 are the values to *ACTUALLY* write out
		       (cond ((eq slot '#$clone-built-from) ; DROP clone-built-from flags for prototypes whose clones
			      (ordered-set-difference vals partially-cloned-from)) ; are only being partially saved
			     ((eq slot '#$prototype-participants)
			      (cond ((set-difference essentials vals)
				     (report-error
              "ERROR! saving prototype: some essential instances are not prototype-participants of the prototype!~%   ~a~%"
	       (set-difference essentials vals)))
;				    (t essentials)	; (NB essentials is a subset of vals)
				    (t (ordered-intersection vals essentials))   ; preserve ordering in vals, for safety
				    ))
;			     ((member slot (cons '#$cloned-from *unclonable-slots*)) vals) ; write ALL these out
			     ((member slot *slots-with-nonparticipant-skolems*) vals) ; write ALL these out
			     ((not (set-difference skolem-vals essentials)) ; all vals are essential or constants, so write them all out!
			      vals)
			     ; [1] If val-skolems includes a non-essential, then drop it
			     (t (remove nil
				 (mapcar #'(lambda (val)
					    (let* ((*trace-prototype-assertions* nil) ; ok to update prototypes
						   (val-skolems (remove-if-not #'anonymous-instancep (flatten val))))
					      (cond ((null (set-difference val-skolems essentials)) ; [1]
						     val))))
					vals)))
			     )))
;	   (format t "slot = ~a, vals2 = ~a~%" slot vals2) (pause)
	   (cond (vals2 (write-slotvals (make-slotvals (slot-in slotvals) vals2))))))
	(t (list (format nil "~%~vT(" tab)
		 (objwrite (slot-in slotvals) htmlify)
		 " "
		 (write-vals (remove-dup-instances (vals-in slotvals))
			     (+ tab 3 (length (km-format nil "~a" (slot-in slotvals))))
			     htmlify)
		 (cond ((> (length slotvals) 2)
			(report-error 'user-error "Extra element(s) in slotvals list!~%~a. Ignoring them...~%" slotvals)))
		 ")"))))


(defun write-vals (vals &optional (tab 2) htmlify)
  (cond ((null vals) "()")
	(t (list "("
		 (objwrite (first vals) htmlify)
		 (mapcar #'(lambda (val)
			     (list (format nil "~%~vT" tab) (objwrite val htmlify)))
			 (rest vals))
		 ")"))))

(defun write-kmexpr (kmexpr _tab htmlify) (declare (ignore _tab)) (objwrite kmexpr htmlify))

;;; (expr2string '#$(the '(age of #,person))) -> "(the '(age of #,person))"
(defun expr2string (expr &optional htmlify) (concat-list (remove nil (flatten (objwrite expr htmlify)))))

;;; convert to strings to remove package info:
;;; [1c] USER(143): (first '`(the ,car))
;;; excl::backquote
(defun objwrite (expr &optional htmlify)
  (cond ((atom expr) (objwrite2 expr htmlify))
	((and (pairp expr)
	      (symbolp (first expr))
	      (assoc (first expr) *special-symbol-alist*))
	 (let ( (special-symbol-str (second (assoc (first expr) *special-symbol-alist*))) )
	   (list special-symbol-str (objwrite (second expr) htmlify))))
	((listp expr)
	 (list "("
	       (objwrite (first expr) htmlify)
	       (mapcar #'(lambda (item)
			   (list " " (objwrite item htmlify)))
		       (rest expr))
	       ")"))
	(t (report-error 'user-error "Don't know how to (objwrite ~a)!~%" expr))))

;;; Default server action, when interfaced with Web browser. Not used in KM stand-alone
(defparameter *html-action* '"frame")
; (defparameter *html-window* '"target=right")
(defparameter *html-window* '"")

;;; The primitive write operation
;;; [1] Include ||s: (symbol-name '|the dog|) -> "the dog", while (km-format nil "~a" '|the dog|) -> "|the dog|".
(defun objwrite2 (expr htmlify &key (action *html-action*) (window *html-window*))
  (cond ((and htmlify (kb-objectp expr) (known-frame expr)) 		; with KM only, htmlify is always nil
	 (htextify expr (km-format nil "~a" expr) :action action :window window)) ; [1]
	((eq expr nil) "()")
	(t (km-format nil "~a" expr))))

;;; ======================================================================
;;		SHOW DEFINITIONS IN THE KB
;;; ======================================================================

(defun list-definitions (&optional (top-class '#$Thing))
 (let ((*print-right-margin* 9999))
  (mapc #'(lambda (depth+string)
	    (format t (second depth+string)))
	(sort (mapcan #'(lambda (class) (list-defined-subclasses class)) (cons top-class (all-subclasses top-class))) #'< :key #'first))
  t))

(defun list-defined-subclasses (class)
  (let ((defined-subclasses (get class 'defined-subclasses))
	(defined-prototypes (get class 'defined-prototypes)))
    (append
     (mapcan #'(lambda (subclass) (list-definitions-for-class subclass class)) defined-subclasses)
     (mapcan #'(lambda (prototype) (list-definitions-for-prototype prototype class)) defined-prototypes)
    )))

(defun list-definitions-for-class (class superclass)
  (let ((depth (depth-to-thing superclass))
	(slotsvals (get-slotsvals class :facet 'member-definition :situation *global-situation*)))
    (cond (slotsvals
	   (list (list depth (concat (km-format nil "~2d ~a -> ~a [class] IF:~%" depth superclass class)
				     (concat-list (flatten (write-frame2 superclass *global-situation* (desource slotsvals) '#$a '#$has :tab 8))))))))))

;;; [1] (get Plant-cell 'defined-prototypes) -> (|_Plant-Cell-Inside-Hypotonic-Solution22322| |_Plant-cell5965|)
;;;	Note it includes Plant-cell itself, as Plant-cell has a definition on it (the-class Eukaryotic-cell with ...)
;;;     Given a new Plant-cell instance, (classify ...) automatically ignores these as the Plant-cell instance is already necessarily
;;;		an instance of a Plant-cell. However, we don't want to list it here.
(defun list-definitions-for-prototype (prototype superclass)
  (let ((depth (depth-to-thing superclass))
	(prototype-scopes (get-vals prototype '#$prototype-scope :situation *global-situation*)))
    (remove nil
     (mapcar #'(lambda (prototype-scope)
		 (let* ((class (get-unique-val prototype '#$prototype-of))
			(superclass2+slotsvals (class-descriptionp prototype-scope))
			(superclass2 (first superclass2+slotsvals))
			(slotsvals (second superclass2+slotsvals)))
;			(classes (classes-in-description prototype-scope)))
		   (cond ((and slotsvals
			       (eq superclass superclass2))
			  (list depth
				(concat
				 (km-format nil "~2d ~a -> ~a [prototype] IF:~%" depth superclass2 class)
				 (concat-list (flatten (write-frame2 superclass2 *global-situation* slotsvals '#$a '#$has :tab 8)))))
			  ))))
	     prototype-scopes))))

;; (depth-to-thing '#$Cell) -> 6  as Cell -> Living-Entity -> Physical-Object -> Tangible-Entity -> Spatial-Entity -> Entity -> Thing
(defun depth-to-thing (class) (depth-to-thing1 (list class) 0))

(defun depth-to-thing1 (classes depth-so-far)
  (cond
   ((member '#$Thing classes) depth-so-far)
   (t (depth-to-thing1 (my-mapcan #'immediate-superclasses classes) (1+ depth-so-far)))))


