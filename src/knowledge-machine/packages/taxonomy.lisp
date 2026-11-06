
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: taxonomy.lisp
;;; Author: Peter Clark
;;; Date: April 96
;;; Purpose: Print out the frame hierarchy
;;; Warning: Frighteningly inefficient.

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defconstant *indent-increment* 3)
(defconstant *prune-points* nil)
(defconstant *ignore-items* nil)
(defparameter *maxdepth* 9999)

(defun taxonomy (&optional (current-node '#$Thing) (relation-to-descend '#$subclasses) htmlify)
  (write-lines (make-tax current-node relation-to-descend htmlify))
  '#$(t))

;;; Rather ugly -- returns two values
;;; (i) a list of strings, = the taxonomy
;;; (ii) a list of all the concepts processed (= all of them)
(defun make-tax (&optional (current-node '#$Thing) (relation-to-descend '#$subclasses) htmlify)
  (cond ((eq relation-to-descend '#$subclasses)
	 (clean-taxonomy)))
  (cond ((and (eq current-node '#$Thing)
	      (eq relation-to-descend '#$subclasses))
	 (let* ( (all-objects (dereference (get-all-concepts)))
		 (top-classes (immediate-subclasses '#$Thing)) )
	   (multiple-value-bind
	    (strings all-nodes-done)
	    (make-taxes (sort (remove '#$Thing top-classes) #'string< :key #'symbol-name)
			relation-to-descend htmlify nil *indent-increment*)
	    (let ( (unplaceds (remove-if-not #'named-instancep
					     (set-difference all-objects (cons '#$Thing all-nodes-done)))) )
	      (append (cons "Thing" strings)
		      (mapcar #'(lambda (unplaced)
				  (tax-obj-write unplaced *indent-increment* htmlify :instancep '?))
			      (sort unplaceds #'string< :key #'symbol-name)))))))
	(t (make-tax0 current-node relation-to-descend htmlify))))

(defun make-tax0 (current-node relation-to-descend &optional htmlify nodes-done (tab 0))
  (let ( (item-text (tax-obj-write current-node tab htmlify)) )
    (cond ((member current-node *ignore-items*)
	   (values (list item-text
			 (format nil "~vTignoring children..."
				 (+ tab *indent-increment*)))
		   nodes-done))
	  (t (let* ( (all-instances  (km-int `#$(the instances of ,CURRENT-NODE)))
		     (named-instances (remove-if-not #'named-instancep all-instances))
		     (instances-text (mapcar #'(lambda (instance)
						 (tax-obj-write instance (+ tab *indent-increment*) htmlify :instancep t))
					     (sort named-instances #'string< :key #'symbol-name)))
		     (specs (sort (km-int `#$(the ,RELATION-TO-DESCEND #$of ,CURRENT-NODE))
				  #'string<
				  :key #'symbol-name)) )			; alphabetical order
	       (cond ((and specs (member current-node nodes-done))
		      (values (list item-text
				    (format nil "~vT..."
					    (+ tab *indent-increment*)))
			      nodes-done))
		     (t (multiple-value-bind
			 (string new-nodes-done)
			 (make-taxes specs relation-to-descend htmlify (cons current-node (append all-instances nodes-done))
				     (+ tab *indent-increment*))
			 (values (cons item-text (cons instances-text string)) new-nodes-done)))))))))

(defun make-taxes (current-nodes relation-to-descend &optional htmlify nodes-done (tab 0))
  (cond ((not (listp current-nodes)) (values nil nodes-done))	; in case of a syntax error in the KB
	((endp current-nodes) (values nil nodes-done))
	((> (/ tab *indent-increment*) *maxdepth*)
	 (values (list (format nil "~vT...more..."
			       (+ tab *indent-increment*)))
		 nodes-done))
	((not (atom (first current-nodes)))   			; in case of a syntax error in the KB
	 (make-taxes (rest current-nodes) relation-to-descend htmlify nodes-done tab))
	((and (eq relation-to-descend '#$instance-of)
	      (or (anonymous-instancep (first current-nodes))		; don't show anonymous instances
		  (not (kb-objectp (first current-nodes)))))		; or numbers or strings
	 (make-taxes (rest current-nodes) relation-to-descend htmlify nodes-done tab))
	(t (multiple-value-bind
	    (string mid-nodes-done)
	    (make-tax0 (first current-nodes) relation-to-descend htmlify nodes-done tab)
	    (multiple-value-bind
	     (strings new-nodes-done)
	     (make-taxes (rest current-nodes) relation-to-descend htmlify mid-nodes-done tab)
	     (values (list string strings) new-nodes-done))))))

(defun tax-obj-write (concept tab htmlify &key instancep)
  (concat
   (cond ((= tab 0) "")
	 ((eq instancep '?) (format nil "?~a" (spaces (1- tab))))  ; Unfortunately, (format nil "~vT" 0) = " " not ""
	 ((eq instancep t) (format nil "I~a" (spaces (1- tab))))  ; Unfortunately, (format nil "~vT" 0) = " " not ""
	 (t (format nil "~vT" tab)))  ; Unfortunately, (format nil "~vT" 0) = " " not ""
   (objwrite2 concept htmlify)))
;   (cond (htmlify (htextify concept (symbol-name concept) :action '"frame")) ; htmlify always nil for KM only
;	 (t (km-format nil "~a" concept)))))





