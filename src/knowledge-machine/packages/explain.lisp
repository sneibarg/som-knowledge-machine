
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: explain.lisp
;;; Author: Peter Clark
;;; Purpose: Have KM explain its reasoning

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; These constraints are annotated with source info, but not other constraints
(defparameter *annotated-constraints* '#$(must-be-a exactly at-most at-least))
; (defparameter *subslot-comment-tag* '|[subslot-reasoning]|) - move to header.lisp as is used in get-slotvals.lisp
(defparameter *subslot-comment* 		; built-in comment tag
    '#$(comment [subslot-reasoning] ""
		(:seq "The" TheSubslot "of" Value1 "=" Value2 ", and" TheSubslot "is a subslot of" TheSlot)
		(:triple Value1 TheSubslot Value2)))

#|
TERMINOLOGY:
A COMMENT is a tag [cat], converted internally to (comm [cat] Self), denoting a comment tag for
	explanation purposes.
        Special case: for subslot queries, the internal comment tag form has an extra argument: (comm [subslot-reasoning] Self <subslot>), see get-slotvals.lisp
A SOURCE is a structure (@ _Car1 Car parts Engine), embedded in an expression as the LAST element, denoting the frame
	where the expression originally came from.

Both COMMENTS and SOURCES are embedded WITHIN KM expressions, e.g,
	(a Engine [cat])
	(a Engine (@ _Car1 Car parts))
	(*engine2 [cat])
	(*engine2 (@ _Car1 Car parts))

;;; ======================================================================

RECORDING EXPLANATIONS
  (record-explanation-for target val expr &key situation)
	target = (the <slot> of <instance>)

 - The explaining expr may include a "source" annotation about the origin of the
   expression e.g. (a Engine (@ Car parts))
 - situation is the situation in which the computation was done, *not* necessarily
   *Global for non-fluent slots. [This might mean there's duplicate explanations in
   the KB, one in each situation, for non-fluent slots].
   WITH THE EXCEPTION of automatic classification, where instance-of explanations
   are stored globally. [SpecialCase] handles this below.

   NOTE:
   STORING explanations for (f s v) are put just under f.
   (setf f 'explanation-<situation> ((f s1 v1 exp11) (f s1 v1 exp12) ... (f s2 v2 expn21) (f s2 v2 expn22)...))

   RETRIEVING explanations for (f s v) will LOOK in both f and v for (f s v) and (v inverse-s f) respectively.

   An example of the explanation structure on the property list is:
   (get '#$_Drive-With-Passenger1 'explanation) ->
     ((_Drive-With-Passenger1 instance-of Drive-With-Passenger (cloned-from _Drive-With-Passenger6 _Drive-With-Passenger1))
      (_Drive-With-Passenger1 object _Car3 (cloned-from _Drive-With-Passenger6 _Drive-With-Passenger1))
      (_Drive-With-Passenger1 object _Car3 (cloned-from _Drive3 _Drive-With-Passenger1))
      (_Drive-With-Passenger1 instance-of Drive (cloned-from _Drive3 _Drive-With-Passenger1))
      )

RETRIEVING EXPLANATIONS
 - (why [instance slot val situation])
   NEW: (why [triple situation])
   will print out an explanation for this triple, using the functions below.

 - (get-explanations instance slot val [situation])

   returns a list of ISV-MULTI-EXPLANATIONS for this triple.
   An isv-explanation has one of these two structures:
		 (instance slot val (<explanation>*))
		 (val invslot instance (<explanation>*))
   [ **NOTE** The *internal* storage are individual entries (instance slot val <explanation>) - no list ]

   3/17/08: This seems slightly arcane to include both forward and backward directions. However, there's one
   type of explanation which is directional, namely the (every X has ....) explanations. We could add a flag
   to show the directionality, e.g.,
	   (explanation (:triple _Control1 object _Device2)    ((a Device (@ _Drive1 Control object))))
           (explanation (:triple _Device2 object-of _Control1) ((inverse (a Device (@ _Drive1 Control object)))))

   where <explanation> is one of the KM expressions deriving the triple, with FOUR different possible forms:
     - (cloned-from _ProtoDrive1 _Drive1 _ProtoCar1)   ; cloned from _ProtoCar1 in _ProtoDrive1 to _Drive1
     - (added-at Drive-With-Passenger "Here's my comment")  ; manually added
     - (projected-from _Situation3)
     - The first element of a traditional KM expr, which could be anything eg.:
          (a Device (@ _Drive1 Control object))		    ; traditional (every Control has (object ((a Device))))
	  (1 + 1)
	  ((a Dog))					    ; if user accidentally put too many parentheses
	  (retain-expr (a Old))

NOTE:
  get-explanations AGGREGATES (i s v expln1) (i s v expln2) ... into (i s v expln*)
  (get-all-explanations instance slot) & (get-explanation-data instance) does NOT aggregate the explanations together.

  NOTE: We'll call the structure returned by get-all-explanations ISV-EXPLANATIONS to make the distinction.

  - (get-comments <explanation>)

   GIVEN <explanation>, we can find the full KM rule and any comments about it as
   follows:

	(multiple-value-bind
	 (descriptions justifications rule path body)
	 (get-comments <expr>))

    where:
    - descriptions is a list of English translations of the rule
    - justifications is a list of English justifications of the rule
    - body is the expression which was evaluated, justifying the triple.
    - path is the location of that body, in the form of
	(class1 slot1 class2 slot2 ...)
    - rule is a simple syntactic combination of the path + body, looking
      like this:
	(every class1 has
	   (slot1 ((a class2 with
		      (slot2 (body))))))

 - (explain-all)

   List the *entire* explanation database (could be lots!!)

COMMENTS:
 a. (every Car has (parts ((a Engine [Car1]))))
 b. (a Car with (parts ((a Engine [Car1]))))  -> _Car12

For a., [Car1] is converted to structure (comm [Car1] Self) so that we
can catch "Self".

For b., [Car1] is converted to structure (comm [Car1] _Car12), again catching
Self -- this helps with prototypes also, so that as the prototype is cloned,
the comment is cloned also.
|#
; Moved to interpreter.lisp
;(defvar *patterns-to-annotate*
;    '#$(((the ?x of ?y) (?y))
;	((the ?x ?y of ?z) (?z))))

;;; (explanation-type <explanation>) -> #$added-at, #$cloned-from, #$projected-from, or the first element of a KM expr
(defun explanation-type (explanation) (first explanation))

;;; (explanation-in '(f s v explanation)) -> explanation
;;; (explanations-in '(f s v explanations)) -> explanations
(defun explanation-in (isv-explanation) (fourth isv-explanation)) 		; returned by get-all-explanations
(defun explanations-in (isv-multi-explanation) (fourth isv-multi-explanation))	; returned by get-explanations

;;; (explanation-in '(f s v explanation)) -> (f s v)
(defun triple-in (isv-explanation) (subseq isv-explanation 0 3))

;;; ======================================================================
;;;		SOURCES:
;;;  A source denotes the source of an expression.
;;;		It's format is: (@ <class> <slot> ... )
;;; ======================================================================
#|
SOURCES *NOT* allowed on
	- &, &&, &+ structures
	- structured list vals (:triple ...)
		otherwise a (desource-top-level ...) doesn't prune them all

ALSO: I aggressively decomment and desource constraints in
;(defun find-constraints-in-exprs (exprs)
;  (desource+decomment (find-constraints exprs 'plural)))

In an ideal world, it'd be better to pass these comments back with the constraints
for tracking down where they came from, but the constraint engine won't handle that
for now!
|#
(defun sourcep (tag)
 (and (listp tag)
      (eq (first tag) '@)))

;;; (source-path '(@ Car parts Engine)) -> (Car parts Engine)
;;; GIVEN: a source data structure
;;; RETURN: the actual path the source denotes
;;; ASSUME sourcep test has already been passed
;(defun source-path (source) (rest source))
(defun source-path (source) (rest (rest source)))	; revised

;;; Find the class of origin - backwards compatible with Shaken
;;; (@ _Cell1 Cell has-part) -> Cell
(defun originated-from-class (source) (third source))

;;; (@ _Cell1 Cell has-part) -> _Cell1
(defun inherited-to-instance (source) (second source)) ; new!

#|
8/2/08 - I don't *THINK* this can ever be more than one class (?)
Find classes of origin: NOTE: argument is an EXPRESSION not a SOURCE (different to originated-from-class)
INPUT: expr is an element of the list returned by (get-explanations1 f s v). Three types:
  - (cloned-from _Drive3 _Drive1) 			 ; cloned from protoype _Drive3
  - (a Device (@ _Drive1 Control object))		 ; traditional (every Control has (object ((a Device))))
  - (added-at Drive-With-Passenger "Here's my comment")  ; manually added
  - (projected-from _Situation3)
|#
(defun originated-from-classes (expr)
  (cond ((and (eq (explanation-type expr) '#$cloned-from)
	      (known-frame (third expr)))	; NEW: If node leading to triple is deleted, skip the originating class
	 (let ((source-protoroot (second expr)))
;	   (km-int `#$(the classes of ,SOURCE-PROTOINSTANCE))
;	   (immediate-classes source-protoroot)))
	   (prototype-classes source-protoroot))) ; NOTE: immediate-classes may contain redundant classes in AURA
						  ;       as *built-in-remove-subsumers-slots* = nil
	((eq (explanation-type expr) '#$added-at) ; (added-at '#$MyClass <comment>)  is an expln
	 (list (second expr)))
	((eq (explanation-type expr) '#$projected-from) nil)
	(t (mapcar #'originated-from-class (sources expr)))))

;;; Cat -> [@Cat]
;;; NEW: Include Self so we can track the instance inheriting the expression
;(defun make-source (class) (list '@ class))
(defun make-source (class) (list '@ '#$Self class))

(defun add-to-source (source item) (append source (list item)))

;;; DESOURCE - removes sources
;;; Neah, parenthesizing and deparenthesizing causes too many problems.
;;; Just refuse to parenthesize stuff in the first place.
;;; [1] (desource '(a Wheel with (position ((front (@ Car has-part Wheel position)))))
;;; should go to (a Wheel with (position ( front )))
;;;          not (a Wheel with (position ((front))))
;;; [2] Unusual to have a null :seq but possible (and is in rkf-clib-one.km)
(defun desource (expr)
  (cond ((delistifiable-sourced-pairp expr)
	 (desource (first expr)))
        ((listp expr)
;	      (or *record-explanations* *record-sources*))	; assume is ALWAYS true
	 (remove-if #'sourcep (mapcar #'desource expr)))
	(t expr)))

; OLD: - well, may was well keep this as it simplifies the expressions a little
; [1] Special case: we DO allow freestanding comments on instance-of,
; so want (instance-of (Car [comm1])) -> (instance-of (Car)), not (instance-of Car)
; [2] :nodelistification t:: ((x [com1]) && (y)) -> ((x) && (y)) NOT (x && (y))
(defun decomment (expr &key (no-delistification t))
  (cond ((and (delistifiable-commented-pairp expr)
	      (not no-delistification))
	 (decomment (first expr)))
	((and (listp expr)
	      (eq (first expr) '#$instance-of)) ; [1]
	 (remove-if #'comment-tagp (mapcar #'(lambda (x) (decomment x :no-delistification t)) expr)))
        ((listp expr)
;	      (or *record-explanations* *record-sources*))	; assume is ALWAYS true
;	 (remove-if #'comment-tagp (mapcar #'decomment expr)))
	 (remove-if #'comment-tagp (mapcar #'(lambda (x) (decomment x :no-delistification t)) expr)))  ; [2]
	(t expr)))

#|
;;; REVISION:
;;; Unlike sources, comments can be freestanding and KM never adds parens to contain them, so we should never need
;;; to strip off those parens again.
(defun decomment (expr)
  (cond ((listp expr) (remove-if #'comment-tagp (mapcar #'decomment expr)))
	(t expr)))
|#

; OLD
;(defun desource (expr)
;  (cond ((and (listp expr)
;	      (or *record-explanations* *record-sources*))
;	 (remove-if #'sourcep (mapcar #'desource expr)))
;	(t expr)))

; in header.lisp
; (defparameter *developer-mode* nil)

;;; ----------

;;; DESOURCE0 - removes sources AND converts comments back into the non-internal form for presentation purposes
;;; For my own debugging
(defun desource-for-printing (expr)
  (cond (*developer-mode* expr)
	(t (desource1 expr))))

;;; (desource1 '#$(comm [cat] _Cat3)) -> [cat]
(defun desource1 (expr)
  (cond ((listp expr)
	 (cond ((and (= (length expr) 3)			; (comm [cat] _Cat3) -> [cat]
		     (eq (first expr) '#$comm))
		(second expr))
	       ((delistifiable-sourced-pairp expr)
		(desource1 (first expr)))
	       (t (remove-if #'sourcep (mapcar #'desource1 expr)))))
	(t expr)))

;;; ----------

(defun sources (expr) (cond ((listp expr) (remove-if-not #'sourcep expr))))

;;; ======================================================================
;;;		MANIPULATING COMMENTS
;;; ======================================================================

(defconstant *comment-marker-char* #\[)

(defun comment-tagp (tag)
  (or (internal-commentp tag)
      (user-commentp tag)))

(defun comment-or-sourcep (tag)
  (or (internal-commentp tag) 	; (comm [cat] Self)
      (sourcep tag)		; (@ _Car1 Cat parts)
      (user-commentp tag)))	; [cat]

;;; e.g., (comm [cat] Self)
(defun internal-commentp (tag)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))  ; optimized by Francis Leboutte
  (and (listp tag)
       (eq (first tag) '#$comm)))

;(defun user-commentp (tag) (and (symbolp tag) (char= (first-char (symbol-name tag)) *comment-marker-char*)))
; Optimized by Francis Leboutte
; Extended by Sunil Mishra to include additional test for a closing ] as well as opening [
(defun user-commentp (tag)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (and (symbolp tag)
       (let ((name (symbol-name tag)))
         (and (char= (schar name 0) #\[)
	      (let ((last (1- (length name)))) ; compute only if necessary - smh 2012-06-19
		(char= (schar name last) #\]))))))
#|
(defun user-commentp (tag)
   (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
   (and (symbolp tag)
        (let ((name (symbol-name tag)))
         (and (char= (schar name 0) #\[)
              (char= (schar name (1- (length name))) #\])))))
|#


;;; ----------

;;; Only applied to slotsvals at load time, not to anything else
(defun convert-comments-to-internal-form (expr &optional (self '#$Self))
  (cond ((internal-commentp expr) expr)		; avoid repeatedly doing this
        ((user-commentp expr) (convert-comment-to-internal-form expr self))
	((listp expr) (mapcar #'(lambda (e) (convert-comments-to-internal-form e self)) expr))
	(t expr)))

;;; [Car1] -> (comm [Car1] Self)
(defun convert-comment-to-internal-form (user-comment &optional (self '#$Self))
  `(#$comm ,user-comment ,self))

;;; ----------

; Less efficient implementation; improved version below thanks to Sunil Mishra.
;(defun desource+decomment (expr &key retain-commentsp)
;  (cond ((and (listp expr)
;	      (not retain-commentsp))
;	 (remove-if #'comment-or-sourcep (mapcar #'desource+decomment expr)))
;	(t expr)))

;;; desource+decomment: DECOMMENTS *AND* DESOURCES
;;; USER(3): (desource+decomment '(cat [1] (dog [3] ([4] [45] man))))
;;; (cat (dog (man)))
;;; [1] :delistifyp NEW RULE: If remove a comment/source AND the result is a singleton list THEN delistify.
;;; 	(desource+decomment '(a Man with (size (((a [2] Large)))) [1])) -> (a Man with (size (((a Large)))))
;;; 	(desource+decomment '(a Man with (size (([2] *large))) [1])) -> (a Man with (size (*Large)))
;;; The one exception to this is comments on the top-level of instance-of slots, where comment tags ARE allowed
;;; to be "naked".
;;; NOTE: If retain-commentsp = t, then this function has NO EFFECT
(defun desource+decomment (expr &key retain-commentsp (delistifyp t))
  (cond (retain-commentsp expr)
	(t (multiple-value-bind
	       (decommented-expr comment-foundp)
	       (desource+decomment1 expr)
	     (cond ((and delistifyp
			 comment-foundp
			 (not (km-structured-list-valp expr))
			 (not (eql (first expr) '#$no-inheritance))) ; no longer used, but must stay listified
		    (delistify decommented-expr)) ; (*cat [1]) -> *cat not (*cat)
		   (t decommented-expr))))))

;;; [1] (desource+decomment '#$(instance-of (Thing [cat]))) -> (instance-of (Thing))   (*don't* delistify (Thing))
(defun desource+decomment1 (expr)
  (declare (optimize (speed 3) (safety 0)))
  (cond ((null expr) nil)
	((listp expr)
	 (let ((car-expr (car expr))
	       (cdr-expr (cdr expr)))
	   (cond ((comment-or-sourcep car-expr)
		  (values (desource+decomment1 cdr-expr) t))
		 ((and (pairp expr)
		       (eq car-expr '#$instance-of))	; Special case: DO allow freestanding comments on instance-of
;		  (km-format t "here! cdr-expr = ~a~%" cdr-expr)
		  (list car-expr (desource+decomment1 (first cdr-expr)))) ; [1] desource+decomment1 DOESN'T delistify
		 (t (let ((car-result (desource+decomment (car expr))))
		      (multiple-value-bind
			  (cdr-result comment-foundp)
			  (desource+decomment1 (cdr expr))
			(if (and (eql car-result (car expr))
				 (eql cdr-result (cdr expr)))
			    expr
			  (values (cons car-result cdr-result) comment-foundp))))))))
	(t expr)))

;;; Much simpler: (decomment-list #'(Engine [Engine-1])) -> (Engine).
;;; Used for removing comments from instance-of slot-values. (There are no sources on instance-of links)
;(defun decomment-list (list) (remove-if #'comment-tagp list))

#|
(defun desource+decomment (expr &key retain-commentsp)
  (declare (optimize (speed 3) (safety 0)))
   (if retain-commentsp
       expr
       (cond ((null expr) nil)
	    ((listp expr)
	     (let ((car-expr (car expr))
		   (cdr-expr (cdr expr)))
	       (if (comment-or-sourcep car-expr)
		   (desource+decomment cdr-expr)
		   (let ((car-result (desource+decomment (car expr)))
			 (cdr-result (desource+decomment (cdr expr))))
		     (if (and (eql car-result (car expr))
			      (eql cdr-result (cdr expr)))
			 expr
	               (cons car-result cdr-result))))))
	    (t expr))))
|#
;;; For the mistake of using extra parens, (Y has (slot ( ((a X)) ) rather than (Y has (slot ((a X))):
;;; [1] don't do ((a X (@ _Car2)) (@ _Car1)) -> (a X (@ Car2)), as then this will fail to match a handler and give
;;; a wierd message. Instead have it -> ((a X (@ Car2)))
(defun desource-top-level (expr)
  (cond ((delistifiable-sourced-pairp expr)
	 (desource-top-level (first expr)))
	((listp expr)
	 (remove-if #'sourcep expr))
	(t expr)))

;;; ------------------------------

#|
     (*black [comment1]) -> *black, not (*black)
 But (:seq [comment1]) -> (:seq)
 and (no-inheritance [comment1]) -> (no-inheritance)
 [1] (desource '(a Wheel with (position ((front (@ Car has-part Wheel position)))))
      should go to (a Wheel with (position ( front )))
          not (a Wheel with (position ((front))))
 [2] Unusual to have a null :seq but possible (and is in rkf-clib-one.km)
|#
(defun delistifiable-commented-or-sourced-pairp (expr)
  (and (pairp expr)			; [1]
       (comment-or-sourcep (second expr))
       (not (km-structured-list-valp expr)) ; note (:seq (@ p)) -> (:seq), not :seq [2]
       (not (eql (first expr) '#$no-inheritance)))) ; no longer used, but must stay listified

(defun delistifiable-sourced-pairp (expr)
  (and (pairp expr)			; [1]
       (sourcep (second expr))
       (not (km-structured-list-valp expr)) ; note (:seq (@ p)) -> (:seq), not :seq [2]
       (not (eql (first expr) '#$no-inheritance)))) ; no longer used, but must stay listified

(defun delistifiable-commented-pairp (expr)
  (and (pairp expr)			; [1]
       (comment-tagp (second expr))
       (not (km-structured-list-valp expr)) ; note (:seq (@ p)) -> (:seq), not :seq [2]
       (not (eql (first expr) '#$no-inheritance)))) ; no longer used, but must stay listified

;;; ------------------------------

;;; NEW: (desource+decomment-top-level (*black (comm [Comment1] _Dog1))) -> *black, not (*black)
(defun desource+decomment-top-level (expr)
  (cond ((delistifiable-commented-or-sourced-pairp expr)
	 (first expr))
	((listp expr)
	 (remove-if #'comment-or-sourcep expr))
	(t expr)))

;;; Opposite - don't store all the embedded sources for the explanation database
;;; (a (b (@ x)) (@ y)) -> (a b (@ y))

(defun desource-all-but-top-level (expr)
  (cond ((listp expr) (mapcar #'desource expr))
	(t expr)))

;;; ----------

(defun get-comment-tags (expr)
  (cond ((listp expr) (remove-if-not #'comment-tagp expr))))

(defun get-comment-tags-recursive (expr)
  (cond ((comment-tagp expr) (list expr))
	((listp expr) (my-mapcan #'get-comment-tags-recursive expr))))

;;; Returns five values
;;; 	- list of English explanations
;;;	- list of English justifications
;;;	- the KM rule
;;;	- the location part of the KM rule
;;;	- the expression part of the KM rule
(defun get-comments (expr)
  (cond ((listp expr)
	 (let* ( (sources (sources expr))
		 (expr0 (desource expr))
		 (source-path (source-path (first sources)))
		 (rule (build-rule expr))
		 (explanations+justifications (transpose (mapcar #'get-comment (get-comment-tags expr)))) )
	   (cond ((>= (length sources) 2)
		  (report-error 'nodebugger-error "get-comments: More than one source path ~a (?). Just using first...~%" sources)))
	   (values (remove nil (first  explanations+justifications))
		   (remove nil (second explanations+justifications))
		   rule
		   source-path
		   expr0)))))

;;; ----------

;;; USER(22): (print (build-rule '#$(a Distributor (@ Car parts Engine parts))))
;;; (every Car has (parts ((a Engine with (parts ((a Distributor)))))))
;;;
;;; [1] New: 1/10/01 - allow rules to be explicitly stored too (for Shaken) - result is then reflexive:
;;; USER(22): (print (build-rule '#$(every Car has (parts ((a Engine with (parts ((a Distributor)))))))))
;;; (every Car has (parts ((a Engine with (parts ((a Distributor)))))))
;;; REMOVED: 12/19/07
;;; READDED BACK: 11/9/11 - We now store classification rules verbatim  (every Photosynthesis-By-Plant has-definition (...))
;;;		  Thus (every...) statements may still occur, but only with has-definition as the 3rd argument (every ... has-definition ...)
;;; :ignore-constraintsp - any rule which comes from a must-be-a constraint is ignored (dropped).
(defun build-rule (expr0 &key ignore-constraintsp)
  (cond
   ((eq (explanation-type expr0) '#$every) expr0)			; [1]
   ((eq (explanation-type expr0) '#$cloned-from) expr0)
   ((eq (explanation-type expr0) '#$added-at) expr0)
   ((eq (explanation-type expr0) '#$projected-from) expr0)
   (t (let* ((source (first (sources expr0)))  ; should never be multiple sources, but just in case!
	     (expr (desource expr0))
	     (source-path (source-path source)))
	(cond
	 ((and ignore-constraintsp (intersection *annotated-constraints* (flatten source-path) :test #'equal)) nil)
;	 ((and ignore-constraintsp (member '#$must-be-a (flatten source-path) :test #'equal)) nil)
	 ((or (null source-path)
	      (oddp (length source-path)))
	  (cond ((oddp (length source-path))
		 (report-error 'nodebugger-error "build-rule: Even path length for path ~a! Don't know how to build a rule...~%" source-path)))
	  (list '|<location unknown>| expr))
	 (t (build-embedded-val source-path expr :every-a '#$every :has-with '#$has)))))))
;	 (t `(#$every ,(first source-path) #$has (,(second source-path) (,(build-embedded-val (rest (rest source-path)) expr))))))))))

;;; Returns an (a ... with ...) structure
;;; e.g., (build-embedded-val '#$(Leg parts) '#$(a Toe)) -> (a Leg with (parts ((a Toe))))
(defun build-embedded-val (path expr &key (every-a '#$a) (has-with '#$with))
  (cond ((null path)
	 (cond ((and (eq every-a '#$must-be-a) (listp expr) (eq (first expr) '#$a)) ; (a Toe) -> (must-be-a Toe)
		`(#$must-be-a ,@(rest expr)))
	       (t expr)))
;	((and (listp (first path))	; REVISED
;	      (eq (first (first path)) '#$must-be-a))
;	 `(#$must-be-a ,(second (first path))
;	   		#$with (,(second path) (,(build-embedded-val (rest (rest path)) expr)))))
	(t (let* ((class (first path))
		  (slot0 (second path))
		  (must-be-a-p (and (pairp slot0) (eq (second slot0) '#$must-be-a))) ; e.g, (parts must-be-a)
		  (slot (cond (must-be-a-p (first slot0))
			      (t slot0))))
;	     (km-format t "slot0 = ~a~%" slot0)
;	     (km-format t "slot = ~a~%" slot)
	     `(,every-a ,class ,has-with
			(,slot (,(build-embedded-val (rest (rest path)) expr
						     :every-a (cond (must-be-a-p '#$must-be-a)
								    (t '#$a))))))))))

;;; ------------------------------

(defun comment (comment-tag data)
  (cond ((not (comment-tagp comment-tag))
	 (report-error 'user-error "~a~%       Comment tag ~a should be a symbol in square brackets, e.g. [Car1]!"
		       `(#$comment ,comment-tag ,data) comment-tag))
	(t (km-add-to-kb-object-list comment-tag)
	   (setf (get comment-tag 'comment) data))))

(defun show-comment (comment-tag)
  (cond ((not (comment-tagp comment-tag))
	 (report-error 'user-error "~a~%       Comment tag ~a should be a symbol in square brackets, e.g. [Car1]!"
		       `(#$show-comment ,comment-tag) comment-tag))
	(t (get comment-tag 'comment))))

#|
This version returns the *whole* ("a" "b" (:set (the part of Self))):

KM> (comment [x] "a" "b" (:set (the part of Self)))

USER: (get '|[x]| 'comment)
("a" "b" (:set (the part of Self)))

CL-USER(19): (get-comment '#$(comm [x] _Car1))		; internal form of comment
("a" "b" (:set (the part of _Car1)))

CL-USER(20): (get-comment2 '#$(comm [x] _Car1) 'call)
"b"

CL-USER(21): (get-comment2 '#$(comm [x] _Car1) 'exit)
"a"
|#
;;; [1] Should no longer arise -- *all* comments are converted to internal form
(defun get-comment (comment-tag)
  (cond ; ((user-commentp comment-tag) (get comment-tag 'comment)) ; [1]
	((internal-commentp comment-tag)
	 (let ( (comment (get (second comment-tag) 'comment))
		(self (third comment-tag)) )
	   (bind-self comment self)))))

;;; This version you pass mode (call/exit/fail/subgoals), and the appropriate element of the (comment ...) list is returned
;;; [1] Should no longer arise -- *all* comments are converted to internal form
(defun get-comment2 (comment-tag mode)
  (cond ; ((user-commentp comment-tag) (get comment-tag 'comment)) [1]
	((internal-commentp comment-tag)
	 (let* ((self (third comment-tag))
		(comments (cond ((eq (second comment-tag) *subslot-comment-tag*) (rest (rest *subslot-comment*)))
				(t (bind-self (get (second comment-tag) 'comment) self)))))
	   (case mode
		 (call (second comments))
		 ((exit fail) (first comments))
		 (subgoals (third comments)))))))

;;; ======================================================================
;;;		RECOGNIZING SPECIAL TYPES OF COMMENTS
;;; ======================================================================

;;; (x has ...)
;;; (every x has ...)
;;; (in-situation (x has ...))
(defun km-assertion-expr (expr)
  (and (listp expr)
       (or (intersection expr '#$(a an some has has-definition now-has == &))	; new: add now-has (missed in 1.4.5.83)
	   (and (eq (first expr) '#$in-situation)
		(km-assertion-expr (third expr))))))

;;; In interpreter.lisp, we strip the assignment data off expressions EXCEPT for
;;; certain special forms, where the data is stripped off lower down in the processing.
;;; [PS Better make sure there are special handlers to deal with these cases!!]
;;; These special forms are:
;;;	1. (:set a b c)
;;; NEW: No, we're going to remove handling of sets, so we consider "record it later" here, but then don't bother later.
;;;	 Hmm...
(defun record-explanation-later (expr)
  (and *record-explanations*
       (or (and (km-setp expr)
	   	(notevery #'atom (rest expr)))			; if all atoms, then don't pass it further down
	   (and (listp expr)
		(unification-operator (second expr))))))
;		(member (second expr) '(&& & &+ &+! &! &&! == ===))))))

;;; ======================================================================
;;; 		MAINTAINING THE EXPLANATION DATABASE ITSELF
;;; ======================================================================

#|
explanations are triples <slot val explanation>
target = (the <slot> of <instance>) - we ASSUME this is GUARANTEED by this point.
Or this? (defun record-explanation-for (target val expr &key (situation (cond ((existential-exprp expr) *global-situation*)
										(t (curr-situation)))))
[1] If call (km-int '#$_Expose2), km-int *will* call km1 if '#$_Expose2 dereferences to something else e.g. _Expose3. BUT we don't
want to record _Expose3 as an explanation for _Expose2, hence the listp test.
[2] was getting combinatorial: a b c ((:set m1) (:set m1 m2) (:set m1 m2 m3) ... (:set m1 m2 m3 c))
    No! We *do* need :set!
	(every Amino-Acid-Sequence has
	  (has-region ((a Carboxyl-Terminus (@ Amino-Acid-Sequence has-region))
	               (a Amino-Terminus (@ Amino-Acid-Sequence has-region)))))

[_Situation21] KM> (the has-region of _Enzyme36)
1 -> (the has-region of _Enzyme36)
1  (2) From inheritance: (:set (a Carboxyl-Terminus) (a Amino-Terminus))
...
 0: (record-explanation-for (|the| |has-region| |of| |_Enzyme39|) |_Carboxyl-Terminus40|
                            (:|set| (|a| |Carboxyl-Terminus| (@ |Amino-Acid-Sequence| |has-region|))
                             (|a| |Amino-Terminus| (@ |Amino-Acid-Sequence| |has-region|))))
We can't pair the right set member with the evaluated result, as this information is lost in the interpreter.

[3] Hmm...we remove the :sets if a more specific explanation is available, presumably from the :set being broken up.
new-explanation: (:set a b)   old-explanation (:set a b c)	-> store (:set a b), discard (:set a b c)
new-explanation: a	      old-explanation (:set a b c)	-> store a

[4]
KM> (every Car has (parts ((a Engine) (a Wheel))))
KM> (the parts of (a Car))
CL-USER(31): (get-explanation-data '#$_Car520)
((_Car520 parts _Wheel522 (a Wheel (@ _Car520 Car parts)))
 (_Car520 parts _Engine521 (a Engine (@ _Car520 Car parts)))
 (_Car520 instance-of Car (a Car)))
CL-USER(32): (reset-done)
KM> (the parts of _Car520)	; same query
CL-USER(33): (get-explanation-data '#$_Car520)
((_Car520 parts _Wheel522 (:set _Engine521 _Wheel522)) 	; <------- we really don't want these new ones!
 (_Car520 parts _Engine521 (:set _Engine521 _Wheel522)) 	; <------- we really don't want these new ones!
 (_Car520 parts _Wheel522 (a Wheel (@ _Car520 Car parts)))
 (_Car520 parts _Engine521 (a Engine (@ _Car520 Car parts)))
 (_Car520 instance-of Car (a Car)))

NOTE: record-explanation-for doesn't get called for unification (&, &&, etc.) operators -- in process-km1-result,
record-explanation-later is t for such expressions and hence record-explanation-for is postponed (and in fact
never gets called in the end for such exprs)
|#
(defun record-explanation-for (target val expr0 &key (situation (curr-situation)) ignore-clone-cycles forcep)
 (cond ((or *record-explanations*
	    (and *record-explanations-for-clones*
		 (member (explanation-type expr0) '#$(cloned-from added-at))))	; two clone-based explanation structures
	(let* ((slot (second target))
	       (expr1 (modify-set-explanation expr0))
	       (expr (desource-all-but-top-level expr1)))	; don't need to store embedded sources in expln database
	  (cond
	   ((and (listp *record-explanations*) ; Now can be a LIST of slots worth recording explanations for
		 (not (member slot *record-explanations*))	; i.e., is not worth recording explanation
		 (not (member (invert-slot slot) *record-explanations*)))
	    nil)
	   ((and (listp target)		; lazy-unify sometimes now gives :target (the <slot> of (i1 &! i2))
		 (not (kb-objectp (fourth target)))) nil)
	   ((and (km-setp expr)
		 (notevery #'(lambda (val) (is-km-term (desource val))) (set-to-list expr)))
	    (report-error 'program-error
			  "A not-fully-evaluated :set was unexpectedly passed as an explanation to ~a.~%"
			  `(record-explanation-for ,target ,val ,expr)))
	   ((and (listp expr) 		; [1]
		 val
		 (not (km-setp expr))	; NEW: *ignore* sets. These arise from [4]
;		 (or (not (km-setp expr))	- should never be :set any more
;		     (notevery #'(lambda (val) (is-km-term (desource val))) (set-to-list expr))) ; 	:set must have at least one path in it...
		 (or (not (km-triplep val)) (not (null (arg3of val))))) ; ignore (:triple x y NIL) computations
	    (let* ((instance (fourth target))
		   (isv-explanation (list instance slot val expr))
		   (old-isv-explanations (get-all-explanations instance slot :situation situation
							       :ignore-clone-cycles ignore-clone-cycles)) )
	      (cond ((member isv-explanation old-isv-explanations :test #'equal)) ; a	       a    -> a

		    ; 10/7/11 - it might not actually have been asserted, if val's class is already <| class
		    ; IF it's an instance-of slot BUT the value was never asserted THEN ignore the explanation
		    ((and (not forcep)
			  (or (member slot *built-in-remove-subsumers-slots*)
			      (member slot *built-in-remove-subsumees-slots*))
			  (not (member val (get-vals instance slot))))
;		     (km-format t "DEBUG: Not asserting value + explanation for ~a (more specific assertion already in the KB) [1]~%"
;			`(,instance ,slot ,val))
		     nil
		     )
		    (t (put-explanations instance slot (cons isv-explanation old-isv-explanations)
					 :situation situation)))
; Disable until Sunil says go ahead (HLO-2022)
	      ;;; NEW: (record-explanation-for '#$(the parts of _Car1) '#$_Engine1 '#$(a Engine (@ _Car1 Car parts)))
	      ;;; Explanation supports TWO assertions: (i) Exists x parts(_Car1,x)  and (ii) instance-of(x,Engine)
	      ;;; So we need to make sure the explanation for this 2nd assertion is ALSO recorded
	      (cond ((and (neq slot '#$instance-of)
			  (kb-objectp val)
			  (existential-exprp expr))
		     (let ((class (second (desource expr)))) ; (a Car) -> Car
		       ; 10/7/11 - it might not actually have been asserted, if val's class is already <| class
		       (cond ((member class (get-vals val '#$instance-of))
			      (record-explanation-for `#$(the instance-of of ,VAL) class expr :situation situation
						      :ignore-clone-cycles ignore-clone-cycles))
;			     (t (km-format t "DEBUG: Not asserting value + explanation for ~a (more specific assertion already in the KB) [2]~%"
;					   `(,val #$instance-of ,class)))
			    ))))))
	   )))))

;;; ----------

#|
REDUNDANT NOW: :set explanations are never stored.
;;; Slightly complex, to minimise storage of :sets
(defun update-isv-explanations (old-isv-explanations isv-explanation)
  (cond
   ((endp old-isv-explanations) (list isv-explanation))
   (t (let ( (old-isv-explanation (first old-isv-explanations)) )
	(cond ((not (equal (triple-in old-isv-explanation) (triple-in isv-explanation)))
	       (cons old-isv-explanation (update-isv-explanations (rest old-isv-explanations) isv-explanation)))
	      (t (let ( (explanation (explanation-in isv-explanation))
			(old-explanation (explanation-in old-isv-explanation)) )
		   (cond ; ((equal explanation old-explanation) old-explanations)	; (tested for earlier)
		    ((km-setp explanation) ; EXPR       OLD-EPXR
		     (km-format t "DEBUG: Found a set explanation doing ~a!~%"
				`(update-isv-explanations ,old-isv-explanations ,isv-explanation))
		     (cond ((not (km-setp old-explanation)) ; (:set a b)   a    -> a
			    (cond ((member (desource old-explanation) explanation :test #'equal) old-isv-explanations) ; DROP explanation
				  (t (cons old-isv-explanation (update-isv-explanations (rest old-isv-explanations) isv-explanation)))))
			   ((subsetp explanation old-explanation :test #'equal) ; (:set a b) (:set a b c) -> (:set a b)
			    (update-isv-explanations (rest old-isv-explanations) isv-explanation)) ; DROP old-isv-explanation
			   (t (cons old-isv-explanation (update-isv-explanations (rest old-isv-explanations) isv-explanation)))))
		    ((and (km-setp old-explanation) ; a  	      (:set a b)  -> a
			  (member (desource explanation) old-explanation :test #'equal))
		     (update-isv-explanations (rest old-isv-explanations) isv-explanation)) ; DROP old-isv-explanation
		    (t (cons old-isv-explanation (update-isv-explanations (rest old-isv-explanations) isv-explanation)))))))))))
|#

;;; (:set (a Cat (@ Person pet)) (a Dog (@ Person pet))) -> (:set (a Cat) (A Dog) (@ Person pet))
(defun modify-set-explanation (expr)
  (cond ((km-setp expr)
	 (let* ( (vals (set-to-list expr))
		 (sources (remove-duplicates (my-mapcan #'sources vals) :test #'equal)) )
	   (vals-to-val (append (desource vals) sources))))
	(t expr)))

(defun why (&optional triple (situation (curr-situation)))
  (cond ((and (null triple)
	      (null *last-answer*))
	 (km-format t "There are no answers to explain!~%"))
	((null triple)
	 (let* ( (slot+frameadd (minimatch *last-question* '#$(the ?slot of ?frameadd)))
		 (slot (first slot+frameadd))
		 (frameadd (second slot+frameadd)) )
	   (cond
	    ((not slot+frameadd)
	     (km-format t "Which conclusion are you asking about? (Here, I can't guess). Enter in the form
   	(why (:triple <instance> <slot> <value>))
e.g.
   KM> (why (:triple _Car1 parts _Engine1))~%"))
	    (t (let ( (values *last-answer*)
		      (instances (km-int frameadd)) )	; if *last-answer*, then frames necc. not null
		 (km-format t "I'll assume you're asking me:~%Why ~a = ~a...~%~%" *last-question* values)
		 (mapc #'(lambda (instance)
			   (mapc #'(lambda (value)
				     (why0 `(#$:triple ,instance ,slot ,value) situation))
				 values))
		       instances)
		 '#$(t))))))
	(t (why0 triple situation))))

#|
For example:

KM> (why (:triple *MyCar parts _Engine1))
(:triple *MyCar parts _Engine1 [in *Global]) because:
   ENGLISH: "All cars have engines"
   JUSTIFICATION: "Engines are required for propulsion"
   RULE: ([Fpp] a Engine with (parts ((a Spark-Plug [Vehicle2]))))

   ENGLISH: "A Car"
   JUSTIFICATION: "I said so"
   RULE: (a Engine [Car1])
|#
(defun why0 (triple &optional (situation (curr-situation)))
  (let* ( (instance0 (arg1of triple))
	  (slot (arg2of triple))
	  (val0 (arg3of triple))
	  (instance (dereference instance0))
	  (val (dereference val0))
	  (isv-multi-explanations (get-explanations instance slot val situation)) )	; returns two, forward and back
    (cond ((not (equal instance instance0)) (km-format t "(~a is bound to ~a)~%" instance0 instance)))
    (cond ((not (equal val val0)) (km-format t "(~a is bound to ~a)~%" val0 val)))
    (cond
     ((null isv-multi-explanations)
      (km-format t "(:triple ~a ~a ~a [in ~a]) because:~%  (no explanation available)~%" instance slot val situation))
     (t (mapc #'(lambda (isv-explanation)
		  (let ( (i (first isv-explanation))
			 (s (second isv-explanation))
			 (v (third isv-explanation))
			 (explanations (explanation-in isv-explanation)) )
		    (km-format t "(:triple ~a ~a ~a [in ~a]) because:~%" i s v situation)
		    (mapc #'(lambda (explanation)
			      (multiple-value-bind
			       (english justification rule path body)
			       (get-comments explanation)
			       (declare (ignore path body))			; is always included in rule anyway
			       (cond (justification (km-format t "   ENTRY TEXT: ~a~%" justification)))
			       (cond (english (km-format t "   EXIT TEXT: ~a~%" english)))
			       (km-format t "   RULE: ~a~%" (desource-for-printing rule))))
			  explanations)
		    (terpri)))
	      isv-multi-explanations)))
    '#$(t)))

;;; ======================================================================
;;;		GETTING THE EXPLANATIONS FOR A TRIPLE
;;; ======================================================================

#|
(get-explanations i s v) ->
	( (i    s v (<expr11> <expr12> ... <expr1m>))
	  (v invs i (<expr21> <expr22> ... <expr2n>)) )

Each element in this (max length 2) list has the structure:
(<instance> <slot> <val> <explanations>)   where <explanations> = (<explanation>*)

Each <explanation> describes how (i s v) or (v invs i) was computed, and has 4 different forms:
  - (a Device (@ _Drive1 Control object))	; traditional, e.g., (every Control has (object ((a Device))))
    (a Device)					; traditional (the source frame could not be located through)
  - (cloned-from _Drive3 _Drive1)		; cloned from protoype _Drive3
  - (added-at Drive-With-Passenger "Here's my comment") ; manually added
  - (projected-from _Situation3)		;

Note: is **MAPCAN-SAFE**
|#
(defun get-explanations (instance slot val &optional (situation (curr-situation)))
  (remove nil (list (get-explanations0 instance slot val situation)
		    (get-explanations0 val (invert-slot slot) instance situation))))

;;; OLD
;;; (defun get-explanations0 (instance slot val &optional (situation (curr-situation)))
;;;   (let ( (explanations (remove-duplicates (get-explanations1 instance slot val situation) :test #'equal)) )
;;;    (cond (explanations (list instance slot val explanations)))))
;;;
;;; NEW: instance-of explanations are a special case, retrieved globally.
;;; RETURNS: an (i s v explanations) structure.
;;;    If you just want the explanations only, use get-explanations1
(defun get-explanations0 (instance slot val &optional (situation (curr-situation)))
  (let* ((explanations (get-explanations1 instance slot val situation)))
    (cond (explanations (list instance slot val explanations)))))

;;; RETURNS: List of explanations,
;;; 	where an explanation = (every ...), (cloned-from ...), (added-at ...), (projected-from ...)
(defun get-explanations1 (instance0 slot val0 &optional (situation (curr-situation)))
  (let* ((instance (dereference instance0))
	 (val (dereference val0))
	 (explanations (mapcar #'fourth (remove-if-not #'(lambda (x)
							   (and (eq (second x) slot)
								(equal (third x) val)))
;								 (is-subslot-of (second x) slot)))	; has-part is explanation for has-structure
						       (get-all-explanations instance slot :situation situation))))
	 (projected-from-situation (some #'(lambda (explanation)
					      (cond ((and (listp explanation)
							  (eq (explanation-type explanation) '#$projected-from))
						     (second explanation))))		 ; i.e. return the source situation
					  explanations)) )
    (cond (projected-from-situation
	   (remove-duplicates
	    (append (remove-if #'(lambda (explanation)
				   (and (listp explanation)
					(eq (explanation-type explanation) '#$projected-from)))
			       explanations)
		    (get-explanations1 instance slot val projected-from-situation))
	    :test #'equal))
	  (t (remove-duplicates explanations :test #'equal)))))

;;; ======================================================================
;;;        API TO THE EXPLANATION DATABASE: low-level get/put:
;;; ======================================================================
#|
RETURNS: a list of (i s v explanation)
NOTE: Will return multiple (i s v explanation) for the same i-s-v if >1 expln (explanations aren't aggregated)
1/11/02: NEW: This now looks *up* into the global situation too, to collect explanations attached to prototypes,
which get deposited in the global situation even if we're in KM situation-mode.
2/8/02: No, this transfer from global to local is done in the interpreter, and only on a demand-driven basis
4/13/06: No, let's go back to this, instead of doing the copying in km-slotvals-from-kb
NOTE: slot is solely to determine the target-situation to look in. slot can be NIL, in which case target-situation
is the current situation.
NEW: Always do a dereferencep in case it's called from Lisp directly
NOTES:
  - Can switch of ignore-clone-cycles check for when loading the KB, where load order matters.
  - Will *not* return subslot explanations, e.g., (get-all-explanations _Cell1 has-structure) will not return has-part
    explanations (where has-part is a subslot of has-structure). Rather, the subslot agglomeration is handled
    in get-explanations above.
|#
(defun get-all-explanations (instance0 slot &key (situation (curr-situation)) ignore-clone-cycles)
;  (cond ((eq instance0 '|_Finger5|) (break)))
 (let ((instance (dereference instance0)))
  (cond ((kb-objectp instance)
	 (let* ((target-situation (target-situation situation instance slot))
		(global-isv-explanations (get-explanation-data instance :situation *global-situation*))
		(decycled-global-isv-explanations
		 (cond (ignore-clone-cycles (dereference global-isv-explanations))
		       (t (remove-clone-cycles (dereference global-isv-explanations)))))
		(all-isv-explanations (cond ((eq target-situation *global-situation*) decycled-global-isv-explanations)
					    (t (append (dereference
							(get-explanation-data instance :situation target-situation))
						       decycled-global-isv-explanations)))))
	   (cond ((not (equal global-isv-explanations decycled-global-isv-explanations))
		  (put-explanations instance slot decycled-global-isv-explanations :situation *global-situation*)))
	   #-allegro (remove-duplicates all-isv-explanations :test #'equal :from-end t)
	   #+allegro (remove-duplicates-from-end all-isv-explanations :test #'equal)			; smh 2012-06-18
	   )))))

#+allegro
(defun remove-duplicates-from-end (list &key (test #'eql)) ; defined only over lists!
  (declare (optimize (speed 3) (safety 0)))
  (if (loop for x on list
	  repeat 20
	  finally (when x (return t)))
      (loop with ht = (make-hash-table :test test :values nil)
	  for x in list
	  unless (gethash x ht)
	  collect x
	  and do (excl:puthash-key x ht))
    (cond ((member test (load-time-value (list 'eql #'eql)))
	   (loop with ret = nil
	       for x in list
	       unless (member x ret)
	       do (push x ret)
	       finally (return (nreverse ret))))
	  ((member test (load-time-value (list 'equal #'equal)))
	   (loop with ret = nil
	       for x in list
	       unless (member x ret :test #'equal)
	       do (push x ret)
	       finally (return (nreverse ret))))
	  ((member test (load-time-value (list 'equalp #'equalp)))
	   (loop with ret = nil
	       for x in list
	       unless (member x ret :test #'equalp)
	       do (push x ret)
	       finally (progn (when (member nil ret)
				(break "nil nil nil"))
			      (return (nreverse ret))))))))

;;; slot is representative of the isv-explanations, and determines which target situation the explanations go in.
;;; If slot = nil, then they go in the current situation.
(defun put-explanations (instance slot isv-explanations &key (situation (curr-situation)))
;(let ((stream (tell-append "zoom.txt"))
;      (id (gensym)))
;     (format t "ZOOM ~a~%" id)
;     (format stream "ZOOM ~a~%" id)
;  (top-level.debug:zoom stream)
;  (close stream))
  (cond ((not (kb-objectp instance))
	 (report-error 'program-error "Attempt to put an explanation associated with a non-kb-object ~a!~%" instance))
	(t (put-explanation-data instance isv-explanations :situation (target-situation situation instance slot)))))

;;; ----------
;;; Low level get/put. NOTE No dereferencing!
(defun get-explanation-data (instance &key (situation (curr-situation)) dereference)
  (cond (dereference (dereference (get instance (curr-situation-facet 'explanation situation))))
	(t (get instance (curr-situation-facet 'explanation situation)))))

;;; Allow suppression when running tester.
(defvar *report-explanation-clone-warnings* nil)

;;; [1] Note, it's critical that explanations for non-fluents are put in *Global, as get-explanation-data
;;; does not even look in local for non-fluent explanations. This was causing some explanations to be unseen
;;; by get-supports earlier.
(defun put-explanation-data (instance isv-explanations &key (situation (curr-situation)))
  (cond
   (*report-explanation-clone-warnings*
    (mapc #'(lambda (isv-explanation)
	    (let ((explanation (explanation-in isv-explanation)))
	      (cond ((and (eq (explanation-type explanation) '#$cloned-from)
			  (not (prototypep (second explanation))))
		     (report-error 'user-warning
	   "Attempt to explain a triple as cloned-from a non-prototype!~%    ~a~%   I'll assert it anyway (I'll assume the source prototype is to be loaded later, but if not this might be indicative of a KB error)~%"	isv-explanation)))))
	  isv-explanations)))
  (cond
   ((eq situation '#$*Global)
    (km-setf instance (curr-situation-facet 'explanation situation) isv-explanations))
   (t (let ((globals (remove-if #'(lambda (isv-explanation)			; [1]
				    (fluentp (second isv-explanation)))
				isv-explanations))
	    (locals (remove-if-not #'(lambda (isv-explanation)
				       (fluentp (second isv-explanation)))
				   isv-explanations)))
	(km-setf instance (curr-situation-facet 'explanation situation) locals)
	(km-setf instance (curr-situation-facet 'explanation '#$*Global) globals)))))

#|
======================================================================
	DELETING (cloned-from ....) EXPLANATIONS
======================================================================

Suppose (_MyPet breathes *yes) is cloned-from both (_Pet1 breathes *yes) and (_Fish1 breathes *yes).
This info will be stored in the explanation database.
Suppose then (_Fish1 breathes *yes) is deleted; we need to remove the support on _MyPet.
Can do this like this:
   (delete-support-by-prototypes-in-class '#$(_MyPet breathes *yes) '#$Fish)
or equivalently like this:
   (delete-support-by-prototypes '#$(_MyPet breathes *yes) '#$(_Fish1))

These functions do a simple update (removal) from the explanation database of the (cloned-from _Fish1 _MyPet)
   record.

See knowledge-revision/delete-triples/test-delete-triple2.lisp for full example.

RETURNED VALUE: (Irrelevant)
|#
(defun delete-support-by-prototypes-in-class (triple class &key (situation (curr-situation)) (explanation-types-to-delete '#$(cloned-from)))
  (delete-support-by-prototypes triple (get-vals class '#$prototypes) :situation situation :explanation-types-to-delete explanation-types-to-delete))

(defun delete-support-by-prototypes (triple prototype-roots &key (situation (curr-situation)) (explanation-types-to-delete '#$(cloned-from)))
  (cond
   ((or (not (listp explanation-types-to-delete))
	(set-difference explanation-types-to-delete '#$(cloned-from added-at)))
    (report-error 'user-error "delete-support-by-prototypes: :explanation-types-to-delete must be a list whose values are a subset of (cloned-from added-at).
	Instead was :explanation-types-to-delete '~a~%" explanation-types-to-delete))
   (t (let*
        ((prototype-classes (my-mapcan #'(lambda (protoroot) (get-vals protoroot '#$prototype-of)) prototype-roots))
	 (f (first triple))
	 (s (second triple))
	 (v (third triple))
	 (isv-multi-explanations (get-explanations f s v situation)) ; (i s v explanation*)
	 (isv-explanations-supported-by-prototypes	; list of (i s v (cloned-from <proto-root> <n>))
	  (mapcan #'(lambda (isv-multi-explanation) ; (i s v explanation*)
		      (let* ((triple0 (triple-in isv-multi-explanation))
			     (explanations (explanation-in isv-multi-explanation))
			     (explanations-supported-by-prototypes
			      (remove-if-not #'(lambda (explanation) ; (cloned-from <proto-root> <clone>)
						 (cond
						  ((member (explanation-type explanation) explanation-types-to-delete)
						   (case (explanation-type explanation)
						     (#$cloned-from (member (second explanation) prototype-roots))
						     (#$added-at (member (second explanation) prototype-classes))))))
					     explanations)))
;			(km-format t "triple0 = ~a, explanations = ~a~%" triple0 explanations)
			(mapcar #'(lambda (explanation-supported-by-prototypes)
				    `(,@triple0 ,explanation-supported-by-prototypes))
				explanations-supported-by-prototypes)))
		  isv-multi-explanations)))
	(delete-isv-explanations isv-explanations-supported-by-prototypes :situation situation)))))

(defun delete-isv-explanations (isv-explanations &key (situation (curr-situation)))
  (mapcar #'(lambda (isv-explanation) (delete-isv-explanation isv-explanation :situation situation)) isv-explanations))

(defun delete-isv-explanation (isv-explanation &key (situation (curr-situation)))
  (cond ((null isv-explanation)
	 (report-error 'program-error "NIL passed to delete-isv-explanation (not allowed!)"))
	(t (let ((f (first isv-explanation))
		 (s (second isv-explanation))
		 (v (third isv-explanation))
		 (explanation (explanation-in isv-explanation)))
	     (cond ((null explanation)
		    (report-error 'program-error "Null explanation passed to delete-isv-explanation (not allowed!)"))
		   (t (delete-explanation f s v :explanation-to-delete explanation :situation situation)))))))

;;; ----------
;;; explanation-to-delete = 'all -> delete ALL explanations for (f s v)
;;; NOTE: This assumes that explanation-to-delete is stored on (instance slot val), not (val invslot instance)
;;; val can be '* meaning ALL
(defun delete-explanation (instance0 slot val0 &key explanation-to-delete (situation (curr-situation)))
  (cond ((null explanation-to-delete)
	 (report-error 'program-error "Null explanation passed to (delete-explanation ~a ~a ~a :explanation-to-delete ~a) (not allowed!)" instance0 slot val0 explanation-to-delete))
	((kb-objectp instance0)
	 (let* ((instance (dereference instance0))
		(val (dereference val0))
		(explanation-to-delete0 (dereference explanation-to-delete))
		(target-situation (target-situation situation instance slot))
		(isv-explanations (get-explanation-data instance :situation target-situation :dereference t)))
	   (cond
	    ((and (neq explanation-to-delete 'all)
		  (not (member `(,instance ,slot ,val ,explanation-to-delete0) isv-explanations :test #'equal)))
	     (report-error 'user-error "Failed to delete explanation (doesn't seem to exist):~% ~a~%"
			   `(,instance ,slot ,val ,explanation-to-delete0)))
	    (t (let ((new-isv-explanations
		      (cond ((neq explanation-to-delete 'all)
			     (remove `(,instance ,slot ,val ,explanation-to-delete0) isv-explanations :test #'equal))
			    (t (remove-if #'(lambda (isv-explanation)
					      (or (equal (first-n isv-explanation 3) `(,instance ,slot ,val))
						  (and (eq val '*)
						       (equal (first-n isv-explanation 2) `(,instance ,slot)))))
					  isv-explanations)))))
		 (cond ((eq explanation-to-delete 'all)
			(make-comment "Deleting all explanations supporting (~a ~a ~a)..." instance0 slot val0))
		       (t (make-comment "Deleting explanation ~a supporting (~a ~a ~a)..."
					explanation-to-delete instance0 slot val0)))
		 (put-explanations instance slot new-isv-explanations :situation situation))))))))

(defun delete-all-supports-from-class (class)
  (mapc #'(lambda (instance) (delete-supports-from-class instance class)) (get-all-concepts))
  t)

;;; All explanations originating at a class are deleted
(defun delete-supports-from-class (instance0 class &key (situation 'all-situations))
  (let ((situations (cond ((eq situation 'all-situations) (all-situations))
			  (t (listify situation)))))
    (mapc #'(lambda (s) (delete-supports-from-class0 instance0 class :situation s)) situations)
    t))

(defun delete-supports-from-class0 (instance0 class &key (situation (curr-situation)))
  (let* ((instance (dereference instance0))
	 (isv-explanations (get-explanation-data instance :situation situation :dereference t)))
    (cond ((some #'(lambda (isv-explanation)
		     (member class (originated-from-classes (explanation-in isv-explanation))))
		 isv-explanations)
	   (let ((new-isv-explanations
		  (remove-if #'(lambda (isv-explanation)
				 (let ((origins (originated-from-classes (explanation-in isv-explanation))))
				   (cond ((member class origins)
					  (cond ((not (singletonp origins))
						 (report-error 'user-warning "delete-supports-from-class: Found an explanation with more than one originating class!?~%~a~%Continuing (will delete it anyway)...~%" isv-explanation)))
					  t))))
			     isv-explanations)))
	     (put-explanation-data instance new-isv-explanations :situation situation))))))


#|
Inverse to get-explanations:
	(get-explanations i s v) -> <structs>
	(delete-explanations i s v <structs>)
|#
(defun delete-explanations (i s v structs)
  (mapc #'(lambda (explanation)
	    (delete-explanation i s v :explanation-to-delete explanation)
	    (delete-explanation v (invert-slot s) i :explanation-to-delete explanation))
	(append-lists (mapcar #'fourth structs)))
  t)

;;; ======================================================================
;;;	UTILTIES - combine independently collected explanation structures
;;; ======================================================================

;;; Here we merge explanations for the SAME triple, but from DIFFERENT situations, into a single list.
;;; USER(11): (combine-explanations '( (i s v (e1 e2)) (i s2 v2 (e3)) (i s v (e4 e1)) (i s2 v3 (e5)) (i s2 v2 (e3 e4))))
;;; ((i s v (e2 e4 e1)) (i s2 v2 (e4 e3)) (i s2 v3 (e5)))
(defun combine-explanations (explanations)
  (cond ((endp explanations) nil)
	(t (let* ( (explanation (first explanations))
		   (instance (first explanation))
		   (slot (second explanation))
		   (value (third explanation))
		   (exprs (fourth explanation))
		   (additional-explanations (remove-if-not #'(lambda (additional-explanation)
							      (and (eq (first additional-explanation) instance)
								   (eq (second additional-explanation) slot)
								   (eql (third additional-explanation) value)))
							  (rest explanations))) )
	     (cond (additional-explanations
		    (cons (list instance slot value
				(remove-duplicates (append-lists (cons exprs (mapcar #'fourth additional-explanations))) :test #'equal))
			  (combine-explanations
			   (ordered-set-difference (rest explanations) additional-explanations :test #'equal))))
		   (t (cons explanation (combine-explanations (rest explanations)))))))))

;;; ======================================================================
;;;		MERGING EXPLANATIONS (AFTER UNIFICATION)
;;; ======================================================================
#|
When two instances get unified, we better unify their explanations too!
|#

;;; Done when (in fact, immediately after) i1 and i2 are bound together.
;;; NEW: modify (km-bind ...) to do it immediately before!
;;; This procedure is (only) called by (km-bind i1 i2) in frame-io.lisp, binding i1 to point to i2.
;;; Urgh - need to scan the entire space of situations. Could make this more efficient by some lazy method, but it'll do for now.
(defun merge-explanations (i1 i2)
  (cond ((and (kb-objectp i1) (kb-objectp i2))
; ???
;	 (let* ( (dominant-i (dereference i1))		; i.e., find the result of (i1 & i2)
;		 (recessive-i (first (remove dominant-i (list i1 i2)))) )
; Let's to merge-explanations BEFORE the binding is actually done
	 (let* ((dominant-i (dereference i2))
		(recessive-i i1))
	 (cond ((null recessive-i)
		  (report-error 'user-warning "Null recessive-i encountered in merge-explanations!~%"))
	       (t (mapc #'(lambda (situation)
			    (merge-explanations-in-situation dominant-i recessive-i :situation situation))
			(all-active-situations))))))))

#|
[1] Triple itself not be there if 2 explanations for same triple, e.g.,:
recessive-explanations = ((_Tangible-Entity4 instance-of Tangible-Entity (a Tangible-Entity (@ _Leave2 Move object)))
			  (_Tangible-Entity4 instance-of Tangible-Entity (a Tangible-Entity (@ _Leave2 Move-From object))))
|#
(defun merge-explanations-in-situation (dominant-i recessive-i &key situation)
  (let ((recessive-explns (get-all-explanations recessive-i nil :situation situation)))
;    (km-format t "recessive-explanations = ~a~%" recessive-explns)
    (cond (recessive-explns
	   (let* ((dominant-explns (get-all-explanations dominant-i nil :situation situation))
		  (lost-recessive-explns0 (ordered-set-difference recessive-explns dominant-explns :test #'equal))
		  (lost-recessive-explns
		   (cond ((neq situation '#$*Global) lost-recessive-explns0)
					; all built-in-remove-subsumer/ee-slots are in *Global
			 (t (remove-if #'(lambda (isv-expln) ; drop explanation if the triple it supports has vanished
					 (let ((slot (second isv-expln))
					       (val (third isv-expln)))
			;;; It's only for these slots that a value may magically vanish via unification
			;;; NOTE: We count on dominant-i necessarily being more specific than recessive-i,
			;;;       i.e., that a dominant-i explanation will need to be dropped. This should hold,
			;;;       as unification always prefers the more specific concept name as the dominant.
					   (cond ((or (and (member slot *built-in-remove-subsumers-slots*)
							   (some #'(lambda (class)
								     (is-subclass-of class val)) ; thus val will be dropped
								 (get-vals dominant-i slot)))
						      (and (member slot *built-in-remove-subsumees-slots*)
							   (some #'(lambda (class)
								     (is-subclass-of val class)) ; thus val will be dropped
								 (get-vals dominant-i slot))))
  						  ;;; forward direction of triple will disappear anyway through unification
;						  (km-format t "DEBUG: Dropping value + explanation for ~a (triple dropped from KB)~%"
;							     (triple-in isv-expln))
						  (cond ((member recessive-i (get-vals val (invert-slot slot)))  ; [1]
							 (delete-val val (invert-slot slot) recessive-i #| uninstall-inverses = |# nil)))
						  t))))
				     lost-recessive-explns0)))))
	     (cond (lost-recessive-explns
		    (put-explanations dominant-i nil (remove-duplicates (append dominant-explns lost-recessive-explns) :test #'equal :from-end t)
				      :situation situation))))))))

;;; ----------

(defun explain-all (&key (include-globalp t))
  (mapc #'(lambda (instance)
	    (mapc #'(lambda (situation)
		      (let* ( (explanations (get-all-explanations instance nil :situation situation))
			      (slots (remove-duplicates (mapcar #'second explanations))) )
			(mapc #'(lambda (slot)
				  (let* ( (slot-explanations (remove-if-not #'(lambda (x) (eq (second x) slot)) explanations))
					  (vals (remove-duplicates (mapcar #'third slot-explanations))) )
				    (mapc #'(lambda (val)
					      (km-format t "~%(:triple ~a ~a ~a [in ~a]) because:~%~{   ~a~%~}" instance slot val situation
#|NEW|#							 (mapcar #'build-rule
								 (mapcar #'fourth
									 (remove-if-not #'(lambda (x)
											    (eql (third x) val))
											slot-explanations)))))
					  vals)))
			      slots)))
		  (cond (include-globalp (all-active-situations))
			(t (remove *global-situation* (all-active-situations))))))
	(get-all-concepts))
  t)

#|
;;; [1] For Shaken, *leave* explanations on the prototypes. They should stay.
(defun clear-explanations ()
  (let ( (facets (cons 'explanation
		       (mapcar #'(lambda (situation)
				   (curr-situation-facet 'explanation situation))
			       (all-situations)))) )
    (mapc #'(lambda (frame)
	      (cond ((not (protoinstancep frame))		; [1]
		     (mapc #'(lambda (facet)
			       (remprop frame facet))
			   facets))))
	  (get-all-concepts))
    t))

;;; *Leave* the prototype-style explanations, and also for Shaken the ((@ SME entered))
;;; explanation flag. Everything else can be removed.
(defun clear-explanations ()
  (let ( (explanation-facets (cons 'explanation
				   (mapcar #'(lambda (situation)
					       (curr-situation-facet 'explanation situation))
					   (all-situations))) )
    (mapc #'(lambda (frame)
	      (mapc #'(lambda (explanation-facet)
			(let* ( (old-explanations (get frame explanation-facet))
			        (new-explanations nil) )		; NEW 12/29/07
;				(new-explanations
;				 (remove-if
;				  #'(lambda (explanation)
;				      (standard-explanation-expr (fourth explanation)))
;				  old-explanations)) )
			  (cond ((not new-explanations) (remprop frame explanation-facet))
				((not (equal old-explanations new-explanations))
				 (setf (get frame explanation-facet) new-explanations)))))
		    explanation-facets))
	  (get-all-concepts))
    t))
|#

;;; REVISED (AGAIN): Just leave the *GLOBAL* explanations untouched (conditionally)
;;; [1] For Shaken, *leave* explanations on the prototypes. They should stay.
(defun clear-explanations (&key clear-globalp)
  (let ( (facets (mapcar #'(lambda (situation)
			      (curr-situation-facet 'explanation situation))
			  (cond (clear-globalp (all-situations-and-theories))
				(t (remove *global-situation* (all-situations-and-theories)))))) )
    (mapc #'(lambda (frame)
	      (mapc #'(lambda (facet)
			(remprop frame facet))
		    facets))
	  (get-all-concepts))
    t))

(defun explanations (&optional slots)
  (cond ((and slots (listp slots)) (setq *record-explanations* slots))
	(t (setq *record-explanations* t))))
(defun no-explanations () (setq *record-explanations* nil))

;;; (a Engine (@ Car parts)) is standard, i.e. from a standard KB frame
;;; (every Car has (parts ((a Engine)))) is not (comes from Shaken), neither is ((@ SME entered))
;(defun standard-explanation-expr (expr)
;  (and (listp expr) (neq (first expr) '|every|) (not (sourcep (first expr)))))

;;; ----------

;;; New function (not used):
;;; [1] For Shaken, *leave* explanations on the prototypes. They should stay. But clober everything else.
(defun clear-all-explanations ()
  (let ( (facets (cons 'explanation
		       (mapcar #'(lambda (situation)
				   (curr-situation-facet 'explanation situation))
			       (all-situations-and-theories)))) )
    (mapc #'(lambda (frame)
	      (cond ((not (protoinstancep frame))		; [1]
		     (mapc #'(lambda (facet)
			       (remprop frame facet))
			   facets))))
	  (get-all-concepts))
    t))

;;; ======================================================================
;;;		OLD METHOD FOR CACHING EXPLANATIONS - remove this, ultimately
;;; ======================================================================

;;; Handle for clear-cached-explanations
;(defvar *instances-with-cached-explanations* nil)

;(defun cache-explanation-for (val expr0)
;  (declare (ignore val expr0))
;  nil)

(defun cache-explanation-for (val expr0)
  (cond ((and (kb-objectp val)
	      (existential-exprp expr0))		; Note: still works even if comment tags are in existential-exprp
	 (let ( (explanations (dereference (get val 'cached-explanations))) 		; TEMPORARY
		(expr (desource+decomment expr0)) )
;	   (cond ((not (member val *instances-with-cached-explanations*)) (push val *instances-with-cached-explanations*)))
	   (or (member expr explanations :test #'equal)
	       (km-setf val 'cached-explanations (cons expr explanations)))))))	; TEMPORARY TEST

;;; Disable for automatic system
; (defun clear-cached-explanations () '#$(t))
;  (mapc #'(lambda (instance)
;	    (km-setf instance 'cached-explanations nil))
;	*instances-with-cached-explanations*)
;  (setq *instances-with-cached-explanations* nil))

;;; Rename to avoid collisions.
;;; NOTE: Not used by KM (it's indirectly flushed by km-remprops during (reset-kb)
;(defun clear-evaluation-cache ()
;  (mapc #'(lambda (instance)
;	    (km-setf instance 'cached-explanations nil))
;	*instances-with-cached-explanations*)
;  (setq *instances-with-cached-explanations* nil)
;  '#$(t))

;;; Rewritten to avoid global variable. Only used now in test-suite/cache-problem.km
(defun clear-evaluation-cache ()
  (mapc #'(lambda (instance)
	    (km-setf instance 'cached-explanations nil))
	(get-all-objects))
  '#$(t))


;;; RETURNED VALUE IS IRRELEVANT (just NIL / some value)
(defun explained-by (instance expr &optional target)
  (declare (ignore target))
  (member (desource+decomment expr) (cached-explanations-for instance) :test #'equal))

(defun cached-explanations-for (instance &optional (situation (curr-situation)))
  (declare (ignore situation))
  (cond ((kb-objectp instance) (dereference (get instance 'cached-explanations)))))	; TEMPORARY

;;; Done when (in fact, immediately after) i1 and i2 are bound together
;;; NEW: Do before they are merged
(defun merge-cached-explanations (i1 i2)
  (cond ((and (kb-objectp i1) (kb-objectp i2))
	 (let ((merged-i (dereference i2))
	       (merged-cached-explanations
		 (remove-duplicates (append (dereference (get i1 'cached-explanations))
					    (dereference (get i2 'cached-explanations)))
				    :test #'equal)) )
	   (km-setf merged-i 'cached-explanations merged-cached-explanations)))))

;;; ======================================================================
;;;		ANNOTATE WITH SOURCES
;;; ======================================================================
#|
GIVEN
(annotate-every-expr '#$
    (every Car has
	(parts ((a Engine with
		   (parts ((a Wheel)))))
 	       ((a Seat)))
        (engine ((the Engine parts of Self))))))

RETURN
      (every Car has
	(parts ((a Engine with
		   (parts ((a Wheel [@Car]))) [@Car]))
 	       ((a Seat [@Car])))
	(engine ((the Engine parts of Self [@Car]))))

NOTE: must-be-a constraints get special processing, by wrapping the slot in a (<slot> must-be-a) structure:

	(every Car has
	    (parts ((must-be-a Engine (@ Self Car (parts must-be-a))))))

	(every Car has
	    (parts ((must-be-a Engine with
			(parts ((must-be-a Cylinder (@ Self Car (parts must-be-a) Engine (parts must-be-a)))))
			(@ Self Car (parts must-be-a))))))

This is because to evaluate the constraint, enforce-val-constraint replaces the (must-be-a Engine ...)
with (a Engine ...), thus losing the information that the class came from a constraint rather than
existential expression. By wrapping the must-be-a in the source info, we preserve this knowledge
for explanation purposes.

Note, the explanations affected are for (_Engine1 instance-of Engine), not (_Car1 parts _Engine1) triples.
|#

;;; [1] These slots are candidates for access via low-level get-vals, which doesn't filter out the
;;; source tags.
(defun annotate-slotsvals (slotsvals source)
  (cond
   ((endp slotsvals) nil)
   ((null *record-sources*) slotsvals)
   (t (let ( (slotvals (first slotsvals)) )
	(cond ((or (comment-tagp slotvals)
		   (member (slot-in slotvals) *built-in-atomic-vals-only-slots*))
;		   (combine-values-by-appending-slotp (slot-in slotvals)))	; NEW [1]
	       (cons slotvals (annotate-slotsvals (rest slotsvals) source)))
	      (t (let ( (slot (slot-in slotvals))
			(vals (vals-in slotvals)) )
		   `((,slot ,(annotate-vals vals (add-to-source source slot))) ,@(annotate-slotsvals (rest slotsvals) source)))))))))

(defun annotate-vals (vals source &key embedded-structurep)
  (mapcar #'(lambda (val) (annotate-val val source :embedded-structurep embedded-structurep)) vals))

#|
EXAMPLES:
[1] USER(14): (annotate-val '#$((a x) & (a y)) '(@))
((a x (@)) & (a y (@)))
[1] USER(15): (annotate-val '#$((a x) & (a y) & (a z)) '(@))
((a x (@)) & (a y (@)) & (a z (@)))
[1] USER(16): (annotate-val '#$(((a x)) && ((a y))) '(@))
(((a x (@))) && ((a y (@))))
[1] USER(17): (annotate-val '#$(((a x)) && ((a y)) && ((a z))) '(@))
(((a x (@))) && ((a y) (@)) && ((a z (@))))
[1] USER(18): (annotate-val '#$(a Car with (parts ((a Engine)))) '(@))
(a Car with (parts ((a Engine (@ Car parts)))) (@))


(annotate-val '#$(_Break19 &+
                  (a Break with
                   (next-event
                    ((the some-associated-break-contact of _Car-Accident8))))) '(@))
|#
;;; Note: for &, &+, and && we DON'T record these expressions as justifications, rather their components. So we break them up here
;;; also during annotation. For other expressions, we DO record them as justifications so DON'T break them up here.
;;; [1a] (a & b & c) -> (annotate-val 'a) (annotate-val '(b & c))
;;; [1b] (a & b) -> (annotate-val 'a) (annotate-vals '(b))
;;; [2a] ((a) && (b) && (c)) -> (annotate-vals '(a)) (annotate-val '((b) && (c)))
;;; [2b] ((a) && (b)) -> (annotate-vals '(a)) (annotate-vals '((b)))
;;; [2c] ((a) && (b) [Car1]) -> not allowed!!
;;; [3] It might be safe to put this back at some point, if we want to track where the constraints came from. But for now let's leave it.
;;; [1] A few exotic forms still exist which are quoted but not class descriptions, e.g.,:
;;;    (every Falling-Situation has
;;;        (assertions ('(the agent of Self) has (feelings (*Scared)))))
;;; :embedded-structurep t => We are NOT annotating a top-level val, but some embedded substructure. In this case,
;;; we do NOT annotate atoms (e.g., DON'T do *black -> (*black (@ _Car1 Car color))) as atoms *may* be keywords.
(defun annotate-val (val source &key embedded-structurep)
 (prog1
  (cond ((or
	   ; (not (listp val))  - No, we *do* want to annotate single values like *down. Numbers too? Let's just do
	   ;			  KB objects so far
	     (and (not (listp val))
		  (or embedded-structurep
		      (and (not (kb-objectp val)) ; e.g., number, string. But *do* annotate constants, e.g., *cat, say
			   (not (numberp val))    ; New: *DO* annotate numbers and strings
			   (not (stringp val))
			   )))
	     (comment-tagp val)
	     (km-varp val)
	     (descriptionp val)			; otherwise (quote foo) becomes (quote foo (@ Source)) which isn't a quotep any more!
	     (quoted-expressionp val)
; #|NEW|#    (and (km-structured-list-valp val) (not (km-triplep val)))
;;; 9/15/08 - No, we DO want structured list vals annotated.
;;; e.g., (every Car has (age ((:pair (a Number) *year)))) records a source for (:pair _Number23 *year) and
;;; (_Number23 instance-of Number). See the test at the end of test-suite/explanations.km

	     (and (constraint-exprp val)  ; now DON'T source-comment constraints, or else we get duplicates [3]. Hmmm.
		  (or (eq val '#$:incomplete)
		      (and (listp val)
;			   (not (eq (first val) '#$must-be-a)))))	; EXCEPT let's annotate must-be-a now
			   (not (member (first val) *annotated-constraints*))))) ; EXCEPT lets annotate must-be-a etc
	     )
	 val)
;	((and (singletonp val)
;	      (listp (first val))
;	      (report-error 'user-warning "Bad syntax: Unnecessary use of double parentheses around an expression ~a~%Could just be ~a instead (?)"
;			    val (first val))
;	      nil))			; just warning
	((and (or (kb-objectp val)
		  (numberp val)
		  (stringp val)
		  )
	      (not embedded-structurep))
	 (attach-source-to-expr val source))
	((and (listp (desource+decomment-top-level val))
	      (member (first (desource+decomment-top-level val)) '#$(a every must-be-a)))
	 (let* ((class-to-add (second (desource+decomment-top-level val)))
		(wrapper (cond ((eq (first (desource+decomment-top-level val)) '#$must-be-a) '#$must-be-a)))
;		(annotated-every-expr (annotate-every-expr val (add-to-source source
;									      (cond (wrapper (list wrapper class-to-add))
;										    (t class-to-add)))))
		(source0 (cond (wrapper `(,@(butlast source) (,(last-el source) ,wrapper)))
			       (t source)))
		(annotated-every-expr (annotate-every-expr val (add-to-source source0 class-to-add)))
		(every-expr-with-source (attach-source-to-expr annotated-every-expr source0)))
;	   (km-format t "class-to-add = ~a~%" class-to-add)
;	   (km-format t "wrapper = ~a~%" wrapper)
;	   (km-format t "annotated-every-expr = ~a~%" annotated-every-expr)
;	   (km-format t "every-expr-with-source = ~a~%" every-expr-with-source)
	   every-expr-with-source))
	((and (listp val)
	      (member (second val) '(& &+)))
	 (cond ((member (fourth val) '(& &+))
		`(,(annotate-val (first val) source :embedded-structurep embedded-structurep)
		  ,(second val)
		  ,@(annotate-val (rest (rest val)) source :embedded-structurep embedded-structurep))) ; [1a]
	       (t `(,(annotate-val (first val) source :embedded-structurep embedded-structurep)
		    ,(second val)
		    ,@(annotate-vals (rest (rest val)) source :embedded-structurep embedded-structurep))))) ; [1b]
	((and (listp val)
	      (eq (second val) '&&))
	 (cond ((eq (fourth val) '&&)
		`(,(annotate-vals (first val) source :embedded-structurep embedded-structurep)
		  ,(second val)
		  ,@(annotate-val (rest (rest val)) source :embedded-structurep embedded-structurep))) ; [2a]
	       ((not (= (length val) 3))
		(report-error 'user-error "Badly formed && expr - should be (exprs && exprs) [no comments allowed!]~%   ~a~%" val)
		val)
	       (t `(,(annotate-vals (first val) source :embedded-structurep embedded-structurep)
		    ,(second val)
		    ,(annotate-vals (third val) source :embedded-structurep embedded-structurep))))) ; [2b]
	((intersection val '(& && &+)) val) ; e.g. ([Car1] _Car1 & (a Car))	 - actually shouldn't be allowed

;;; Certain expressions, starting with a *decomment-top-level-only-headwords* should have their subexpresssions
;;; also annotated.
	((and (listp val)
	      (member (first val) *decomment-top-level-only-headwords*))
	 (let* ((dotted-source (dot-source source)) ; (Car part) -> (Car part...)
		(annotated-expr (annotate-vals val dotted-source :embedded-structurep t))) ; atoms might be keywords
	   (attach-source-to-expr annotated-expr source)))
;	(t (attach-source-to-expr val source)))))
	(t (let* ((dotted-source (dot-source source))) ; (Car part) -> (Car part...)
	     (cond
; [1] DON'T annotate top-level if not done above, as it may be a keyword e.g. (LAMBDA () (KM0 (QUOTE ...)))
	      ((null val) nil)
	      (embedded-structurep (annotate-embedded-structures val dotted-source)) ; [1]
; [2] Otherwise, DO attach source to the top level constant or expression.
; e.g. (every Foo has (parts ((:pair (a Car) Self))
;     val = (:pair (a Car) Self)  --annotated--> (:pair (a Car (@ Self Foo parts...)) Self (@ Self Foo parts))
; also    = (the1 of ...)
;	    (make-phase ...)
;           (?x == (...))    etc.
	      (t			; (km-format t "val = ~a~%" val)
	         (attach-source-to-expr
		  (annotate-embedded-structures val dotted-source) source))))) ; [2] keep looking inside
	)))

;;; Forall embedded (a ...) expressions, annotate them and it's subexpressions. Leave everything else.
(defun annotate-embedded-structures (expr source)
  (cond ((listp expr)
	 (mapcar #'(lambda (elt)
		     (cond ((and (listp elt) (eq (first elt) '#$a)) (annotate-val elt source))
			   (t (annotate-embedded-structures elt source))))
		 expr))
	(t expr)))

;;; (dot-source '(a b)) -> (a b...)
(defun dot-source (source)
  (cond ((and (listp source)
	      (kb-objectp (last-el source))
	      (not (ends-with (symbol-name (last-el source)) "...")))
	 (append (butlast source) (list (intern (concat (symbol-name (last-el source)) "...") *km-package*))))
	(t source)))

(defun dotted-slot (slot)
  (and (symbolp slot) (ends-with (symbol-name slot) "...")))

(defun attach-source-to-expr (expr source)
  (cond ((and (listp expr) (not (some #'sourcep expr))) 	; not already commented
	 (append expr (list source)))
;	(t expr)
	(t ; (km-format t "DEBUG: Annotating non-list expr ~a (source ~a)~%" expr source)
	 (list expr source))))	; new, we DO annotate atomic values (for Halo)


;;; expr = '#$(a ...) or '#$(every ...)
;;; OR   ((a ...) [tag])
(defun annotate-every-expr (every-expr &optional source (search-for 'every))
  (cond ((and (pairp every-expr)
	     (comment-tagp (second every-expr)))
	 (list (annotate-every-expr (first every-expr) source search-for) (second every-expr)))
	(t (or (annotate-every-expr0 every-expr source search-for)
	       (report-error 'user-error "annotate-every-expr: Badly structured every/a expression ~a!~%" every-expr)))))

(defun annotate-every-expr0 (every-expr &optional source (search-for 'every))
 (let ( (first-el (first every-expr)) )
  (cond
   ((null every-expr) nil)
   ((comment-tagp first-el)
    (cons first-el (annotate-every-expr0 (rest every-expr) source search-for)))
   ((and (eq search-for 'every)
	 (member first-el '#$(a every must-be-a)))
    (cons first-el (annotate-every-expr0 (rest every-expr) source 'class)))
   ((eq search-for 'class)
    (let ( (source0 (or source (make-source first-el))) )
      (cons first-el (annotate-every-expr0 (rest every-expr) source0 'has))))
   ((and (eq search-for 'has)
	 (member first-el '#$(called uniquely-called)))
    (cons first-el (cons (second every-expr) (annotate-every-expr0 (rest (rest every-expr)) source 'has))))
   ((and (eq search-for 'has)
	 (member first-el '#$(has with)))
    (cons first-el (annotate-slotsvals (rest every-expr) source)))
   (t (report-error 'user-error "Syntax error! Encountered at ~a~%  doing:~%  ~a~%"
		    (append '(|...|) every-expr '(|...|)) (stacked-expr (last-el (goal-stack))))))))

;;; ======================================================================
;;;		JUSTIFICATIONS
;;; ======================================================================

;;; justify:
;;; GIVEN a triple
;;; PRINT the explanation to :stream, and return (t)
;;; This wrapper simply makes sure that the *last-question* and *last-answer* variables
;;; don't get changed by the justification process itself!
;;; e.g., (justify (:triple _Value1 value (:pair 0.45 *molar)))
(defun justify (&optional triple-expr &key (situation (curr-situation)) (depth 0) (stream t))
  (mapc #'(lambda (string)
	    (format stream string)
            ;; RVA 21Aug2006 fix km rep loop input output problem
            ;; using format instead or terpri because format and terpri interpret the stream argument differently
            (format stream "~%"))
	(get-justification :triple triple-expr :situation situation :depth depth :format 'ascii))
  '#$(t))

;;; GIVEN a :triple
;;; RETURN: a list of strings, one per line, explaining :triple
;;; :format is either 'xml or 'ascii
(defun get-justification (&key triple (situation (curr-situation)) (depth 0) (format 'xml) (tab 0))
  (let ((last-question *last-question*)		; make a note of last-qa, as it might get reset during reasoning
	(last-answer *last-answer*))
    (prog1
	(flatten (list
		  (cond ((eq format 'xml) (list (format nil "<explanation-structure>"))))
		  (get-justification0 :triple triple :situation situation :depth depth :format format :tab tab)
		  (cond ((eq format 'xml) (list (format nil "</explanation-structure>"))))))
      (setq *last-question* last-question)	; put it back to how it was
      (setq *last-answer* last-answer))))

;;; Same as above, except without the XML wrapper. Here the returned strings might be nested.
;;; Input (:triple f s v)
(defun get-justification0 (&key triple (situation (curr-situation)) (tab 0) done-triples (depth 0) (format 'xml))
  (cond
   ((and triple (not (km-triplep triple)))
    (report-error 'user-error "(justify ~a): Argument should be a triple (justify (:triple <f> <s> <v>))!" triple))
   ((> depth 20)
    (km-format t "(depth limit for justification reached...no further details below this)~%"))
   (t (let ((triples (compute-triples triple))) ; (:triple f x *) -> find *, and return list of (:triple f x v) forall v
	(mapcar #'(lambda (triple0)
		    (cond ((member triple0 done-triples :test #'equal) nil)
			  (t (get-justification1 triple0 :situation situation :tab tab
						 :done-triples (append triples done-triples)
						 :depth depth :format format))))
		triples)))))

;;; Look for comments about triple in either direction, and then failing that resort to the explanation database
(defun get-justification1 (triple &key (situation (curr-situation)) (tab 0) done-triples (depth 0) (format 'xml))
  (let ((instance (arg1of triple))
	(slot (arg2of triple))
	(value (arg3of triple)))
    (or (get-justification2 instance slot value :situation situation :tab tab
			    :done-triples done-triples :depth depth :format format)
	(get-justification2 value (invert-slot slot) instance :situation situation :tab tab
			    :done-triples done-triples :depth depth :format format)
	(justify-leaf triple :situation situation :tab tab :done-triples done-triples :depth depth :format format))))

(defvar *start-justifications-with-because* t)

(defun get-justification2 (instance slot value &key (situation (curr-situation)) (tab 0) done-triples (depth 0)
						    (format 'xml))
  (let* ((isv-multi-explanations (get-explanations0 instance slot value situation)) ; returns (i s v explanations)
	 (explanations (explanations-in isv-multi-explanations))
	 (comment-tags (remove-duplicates (my-mapcan #'get-comment-tags-recursive explanations)
					  :test #'equal :from-end t)))
;	 (subslot-explanations (remove-if-not #'(lambda (explanation)
;						  (and (minimatch explanation '#$(the ?subslot of ?instance))
;						       (is-subslot-of (second explanation) slot)))
;					      explanations)))
    (cond ((or comment-tags #|subslot-explanations|#)
	   (list (cond (*start-justifications-with-because*
			(concat (spaces tab) (format nil "The ~a of ~a = ~a because:" slot
						     (make-phrase (expand-text instance))
						     (make-phrase (expand-text value))))))
		 (mapcar #'(lambda (comment-tag)
			     (get-comment-justification comment-tag `(#$:triple ,instance ,slot ,value)
							:situation situation
							:tab tab :done-triples done-triples :depth depth :format format))
			 comment-tags)
;		 (concat (spaces tab) (format nil "Therefore, the ~a of ~a = ~a." (arg2of atriple)
;					      (make-phrase (expand-text (arg1of atriple)))
;					      (make-phrase (expand-text (arg3of atriple)))))
;		 (mapcar #'(lambda (subslot-explanation)
;			     (get-comment-justification *subslot-comment-tag*
;							`(#$:triple ,instance ,slot ,value)
;							:situation situation
;							:tab tab :done-triples done-triples :depth depth :format format
;							:subslot (second subslot-explanation)))	; special, for subslots
;			 subslot-explanations)
		 )))))

;;; --------------------

;;; INPUT: A comment tag and :triple
;;; RETURNS: A list of strings, expressing that comment in English
;;; NOTE: This function will recurse using subgoals in the comment tag, passed to get-justification0
(defun get-comment-justification (comment-tag triple &key (situation (curr-situation)) (tab 0) done-triples
							  (depth 0) (format 'xml))
;  (km-format t "triple = ~a~%" triple)
  (let* ((frame (arg1of triple))
	 (slot (arg2of triple))
	 (value (arg3of triple))
	 (subslot (fourth comment-tag))	; special case to squirrel away the subslot
	 (bindings `((#$Value1 . ,frame) (#$TheSlot . ,slot) (#$Value2 . ,value) (#$TheSubslot . ,subslot)))
	 (caller   (sublis bindings (get-comment2 comment-tag 'call)))
	 (exiter   (sublis bindings (get-comment2 comment-tag 'exit)))
	 (subgoals (sublis bindings (get-comment2 comment-tag 'subgoals))))
;	 (caller   (cond ((eq comment-tag *subslot-comment-tag*) nil)
;		         (t (sublis bindings (get-comment2 comment-tag 'call)))))
;	 (exiter   (cond ((eq comment-tag *subslot-comment-tag*) `#$(:seq "and" ,SUBSLOT "is a subslot of" ,SLOT))
;			 (t (sublis bindings (get-comment2 comment-tag 'exit)))))
;	 (subgoals (cond ((eq comment-tag *subslot-comment-tag*) `#$((:triple ,FRAME ,SUBSLOT ,VALUE)))
;			 (t (sublis bindings (get-comment2 comment-tag 'subgoals))))))
    (list
     (cond (*developer-mode*
	    (case format
	      (ascii (list
		      (concat (spaces tab)
			      (km-format nil "(Doing triple: ~a)~%Entry text for ~a:" triple (desource1 comment-tag))))))))
     (case format
       (ascii (cond (caller (concat (spaces tab)
				    (make-phrase (km-int caller :fail-mode 'fail))))))
       (xml (cond (caller (concat (format nil "<explanation><call>")
				  (xmlify (make-phrase (km-int caller :fail-mode 'fail)))
				  "</call>")))))
					; recurse on subgoals
;     (km-format t "subgoals = ~a~%" subgoals)
;     (km-format t "sublis = ~a~%" `((#$Value1 . ,frame) (#$Value2 . ,value)))

     (mapcar #'(lambda (subgoal)
		 (get-justification0 :triple subgoal
				     :situation situation :tab (+ tab 2)
				     :done-triples done-triples
				     :depth (1+ depth)
				     :format format))
	     (km-int subgoals))
     (cond (*developer-mode*
	    (case format
		  (ascii (list (concat (spaces tab) (km-format nil "(Doing triple: ~a)~%Exit text for ~a:" triple (desource1 comment-tag))))))))
     (case format
       (ascii (cond (exiter (concat (spaces tab)
				    (cond ((eq comment-tag *subslot-comment-tag*) "  ")(t ""))
				    (km-format nil (make-phrase (km-int exiter)))) ; was (km ...)?
			    )))
       (xml (cond (exiter (concat (format nil "<exit>")
				  (xmlify (make-phrase (km-int exiter))) ; was (km ...)?
				  "</exit></explanation>"))))))))

;;; If this is t, then a justification for leaf facts of the form <x> = <y> will be generated.
(defvar *justify-leaves* nil)

#|
justify-leaf <triple>. Used when <triple> does NOT have a comment tag.
NOTE: By default, we don't bother explaining things without a comment-tag. However, if *justify-leaves* is t,
      then we *do*.
INPUT: a <triple>
RETURNS: A list of string(s) explaining <triple>

What is a good explanation for (:triple _Cell has-part _Nucleus)? Do we print out the rule(s) that were used,
  or just say (the has-part of Cell) = Nucleus?
I've chosen just to present the source class(es) for the triple, but NOT the whole rule(s).

The rules were pulled from the explanation database, and are of the usual 4 types:
	#$added-at, #$cloned-from, #$projected-from, or the first element of a KM expr.
In *addition*, for prototypes, we can trace the cloned-from links back to the source class(es).
     Tracing the cloned-from links, and looking at the recordings in the explanation database, are
     essentially redundant. However, if we have *record-explanations-for-clones* set to NIL, which
     is a sensible setting, then we can still find where the clones came from.

Note that we look at sources for BOTH directions of the triple (f s v) and (v invs f).
|#
;;; [1] only show rule(s) in developer mode and for ascii output
(defun justify-leaf (triple &key (situation (curr-situation)) (tab 0) done-triples (depth 0) (format 'xml))
  (declare (ignore depth done-triples))
; (format t "*justify-leaves* = ~a~%" *justify-leaves*)
  (let* ((instance (arg1of triple))
	 (slot (arg2of triple))
	 (value (arg3of triple)))
    (cond (*developer-mode*		; [1]
	   (let ((rules (mapcar #'build-rule
				(my-mapcan #'explanation-in (get-explanations instance slot value situation)))))
	    (case format
	     (ascii
	      (cond (rules (concat-list
			    `(,*newline-str* ,(spaces tab) ,(km-format nil "subgoal ~a: Computed from:~%" triple)
					     ,@(mapcan #'(lambda (rule)
							   (list (spaces (+ tab 2)) (km-format nil "~a~%" rule)))
						       rules))))
		    (t (concat-list `(,*newline-str* ,(spaces tab)
				     ,(km-format nil "subgoal ~a: Computed from: (unrecorded!)" triple)))))))))
	  ((and *justify-leaves*
		(neq slot '#$instance-of)) ; else "the instance-of of nucleus = nucleus"
	   (let* ((forward-source-classes (source-classes-for-triple instance slot value situation))
		  (reverse-source-classes (source-classes-for-triple value (invert-slot slot) instance situation))
		  (source-classes (remove-duplicates (append forward-source-classes reverse-source-classes)))
		  (instance-classes (remove-subsumers (immediate-classes instance))) ; ug, AURA keeps subsumers sometimes
		  (value-classes (remove-subsumers (immediate-classes value)))
		  (instance-to-show
		   (cond ((intersection instance-classes source-classes) instance)
			 ((intersection value-classes source-classes) value)
			 (t instance)))
		  (value-to-show
		   (cond ((intersection instance-classes source-classes) value)
			 ((intersection value-classes source-classes) instance)
			 (t value)))
		  (slot-to-show
		   (cond ((intersection instance-classes source-classes) slot)
			 ((intersection value-classes source-classes) (invert-slot slot))
			 (t slot)))
		  )
	     (case format
		(ascii (concat (spaces tab)
			       (format nil "The ~a of ~a = ~a."
				       slot-to-show
				       (make-phrase (expand-text instance-to-show))
				       (make-phrase (expand-text value-to-show)))
			       (cond (source-classes (format nil " (from ~a)"
							     (concat-list (commaify source-classes))))
				     (t ""))))
		(xml (concat "<explanation><leaf>"
			     (xmlify (format nil "The ~a of ~a = ~a."
					     slot-to-show
					     (make-phrase (expand-text instance-to-show))
					     (make-phrase (expand-text value-to-show))))
			     (cond (source-classes
				    (format nil " (from ~a)" (concat-list (commaify source-classes))))
				   (t ""))
			     "</leaf></explanation>"))))))))

(defun source-classes-for-triple (instance slot value &optional (situation (curr-situation)))
  (let* ((explanations (get-explanations1 instance slot value situation))	; explanations1 - just get in the FORWARD
	 (rules (mapcar #'build-rule explanations))) ;    direction
    (remove-subsumers (my-mapcan #'originated-from-classes rules))))

#|
======================================================================
  TRACING SOURCE CLASSES VIA CLONED-FROM LINKS DOESN'T WORK
======================================================================
Q. Is the uracil complement of adenine?
A. Yes!
    For all Uracil:
       an adenine is the complement of an uracil.
Explanation
    The complement of uracil = adenine. (from Thymine, Uracil)

The problem here is Thymine is mentioned as a source. This is because
node-cloned-from traced the Uracil protoinstance as cloned from Thymine --
it appears that the user created Uracil by copy-and-edit of Thymine,
thus leaving a tracability pointer back to Thymine although Thymine is
no longer a valid superclass :-(

The bottom line is we can't rely on the cloned-from links for
tracing inference dependence.
======================================================================

Prototypes: Cell has-part Cytoplasm
	    Euk-Cell has-part Big-Cytoplasm
	    BigEuk-Cell has-part                 Ribosome
	    Human-Cell has-part Big-Cytoplasm
Triple: _Human-Cell1 has-part _Big-Cytoplasm1

(source-classes ...) returns the protoroot's class for ONLY protoroots supplying the most SPECIFIC information
source-classes-i = Human-Cell, Euk-Cell, BigEuk-Cell, Human-Cell
source-classes-v = Cell, Euk-Cell, Human-Cell


;;; RETURNS: A list of classes contributing to (i s v) in that direction only (e.g., classes of i),
;;; but NOT the reverse direction (v invs i)		    val

(defun source-classes-for-triple (instance slot value &optional (situation (curr-situation)))
  (let* ((explanations (get-explanations1 instance slot value situation))	; explanations1 - just get in the FORWARD
	 (rules (mapcar #'build-rule explanations)) ;    direction
	 (source-protoroots-i (cond ((anonymous-instancep instance) (source-protoroots-for-instance instance))))
	 (source-protoroots-v 	; only care about the ones supplying the most specific info on value
	  (cond ((anonymous-instancep value) (source-protoroots-for-most-specific-classes-of-instance value))))

	 (source-protoroots-iv		; THESE are the protoroots where the triple came from
	  (cond ((and (anonymous-instancep instance) (anonymous-instancep value))
		 (intersection source-protoroots-i source-protoroots-v))
		((anonymous-instancep instance) source-protoroots-i)
		((anonymous-instancep    value) source-protoroots-v)))

	 (source-classes-iv (my-mapcan #'(lambda (protoroot)
					   (remove-subsumers (immediate-classes protoroot)))
				       source-protoroots-iv))
	 (nonredundant-source-classes-iv (remove-subsumers source-classes-iv)) ; [1]
	 (source-classes
	  (or nonredundant-source-classes-iv		; don't care about rules, if prototypes already supplied the data
	      (remove-duplicates (my-mapcan #'originated-from-classes rules))))) ; sources from explanations

    source-classes))

;;; ALL source protoroots
(defun source-protoroots-for-instance (instance)
  (remove-duplicates
   (my-mapcan #'(lambda (protoinstance)
		  (get-vals protoinstance '#$prototype-participant-of))
	      (node-cloned-from* instance))))

;;; We're only interested in protoroots that supplied the most SPECIFIC information to instance
(defun source-protoroots-for-most-specific-classes-of-instance (instance)
  (let* ((classes (remove-subsumers (immediate-classes instance)))
	 (protoinstances (node-cloned-from* instance))
	 (protoinstances-of-interest (remove-if-not #'(lambda (protoinstance)	; [1]
							(intersection (immediate-classes protoinstance) classes))
						    protoinstances))
	 (protoroots-of-interest (my-mapcan #'(lambda (protoinstance)
						(get-vals protoinstance '#$prototype-participant-of))
					    protoinstances-of-interest)))
    protoroots-of-interest))
|#

;;; ======================================================================

(defun compute-triples (&optional triple0)
  (cond
   (triple0
    (let* ( (triple (km-unique-int triple0))
	    (instance (arg1of triple))
	    (slot (arg2of triple))
	    (value0 (arg3of triple))
	    (values (cond ((eq value0 '*) (km-int `#$(the ,SLOT of ,INSTANCE)))	; was (km ...)?
			  (t (val-to-vals value0)))) )
      (mapcar #'(lambda (value) (list '#$:triple instance slot value)) values)))
   ((null *last-answer*)
    (km-format t "There's no recorded last answer, so I'm not sure what you're asking me to justify!~%"))
   (t (let* ( (slot+frameadd (minimatch *last-question* '#$(the ?slot of ?frameadd)))
	      (slot (first slot+frameadd))
	      (frameadd (second slot+frameadd)) )
	(cond
	 ((not slot+frameadd)
	  (km-format t "Which conclusion are you asking about? (Here, I can't guess). Enter in the form
               (justify (:triple <instance> <slot> <value>))~%"))
	 (t (let ( (instances (km-int frameadd)) 	 	; if *last-answer*, then frames necc. not null
		   (values *last-answer*) )
	      (km-format t "I'll assume you're asking me to justify:~%   ~a = ~a...~%~%" *last-question* values)
	      (mapcan #'(lambda (instance)
			  (mapcar #'(lambda (value)
				      (list '#$:triple instance slot value))
				  values))
		      instances))))))))

;;; Space-intensive version - see comments below on space-conscious version.
;;; [ideally should be in html.lisp]
;;; INPUT: A string, OUTPUT a string
;;; BEHAVIOR: Change <>& to &gt; &lt; &amp;
;;; (xmlify "<enter>") -> "&lt;enter&gt;"
(defun xmlify (string)
  (let ( (chars (explode string)) )
    (cond ((intersection chars '(#\< #\> #\&))
	   (concat-list (mapcar #'(lambda (char)
				    (case char
					  (#\< "&lt;")
					  (#\> "&gt;")
					  (#\& "&amp;")
					  (#\' "&apos;")
					  (#\" "&quot;")
					  (t (string char))))
				chars)))
	  (t string))))

#|
======================================================================
Feb 2008: Reini Urban reported that the space-conscious version below by Carl Shapiro does
not work under CLisp. (http://article.gmane.org/gmane.lisp.clisp.devel:17562).
Sam Steingold [sds@gnu.org] reports that his investigation shows that it creates
circular code which does not work in clisp, sbcl and cmucl.
As a result, I'm restoring the old space-intensive version above.
======================================================================
;; Rewrite by Carl Shapiro:
;; A space-conscious implementation of XMLIFY.  This recasting of
;; XMLIFY should, in the worst case, have the same asymptotic
;; complexity as the previous definition.  However, this version will
;; only allocate memory when it must introduce escape sequences into
;; the output string.  The overwhelming majority of strings pass
;; through XMLIFY without quoting so this is worth special casing.

(defun xml-length (string)
  (do ((i 0 (1+ i))
       (<-count  0)
       (>-count  0)
       (&-count  0)
       (\'-count 0)
       (\"-count 0)
       (length (length string)))
      ((= i length) (+ length
		       (* 3  <-count)
		       (* 3  >-count)
		       (* 4  &-count)
		       (* 5 \'-count)
		       (* 5 \"-count)))
    (case (char string i)
      (#\< (incf  <-count))
      (#\> (incf  >-count))
      (#\& (incf  &-count))
      (#\' (incf \'-count))
      (#\" (incf \"-count)))))

(defun xmlify-internal (string length new-string)
; (macrolet ((push-string (in-string out-string)
;               `(progn
;                  ,@(my-mapcan
;                           (mapcar #'(lambda (char)
;;                                       `((setf (char ,out-string j) ,char)
;;                                         (incf j)))
;; Modified so that this will compile under Lispworks (by Francis Leboutte)
;				       (list `(setf (char ,out-string j) ,char)
;					     `(incf j)))
;                                   (coerce in-string 'list))))))

  (macrolet ((push-string (in-string out-string)
		`(progn ,@(mapcan #'(lambda (char)
				      (list `(setf (char ,out-string j) ,char)
					    `(incf j)))
				  (coerce in-string 'list)))))

    (do ((i 0 (1+ i))
         (j 0))
        ((= i length) new-string)
      (let ((char (char string i)))
        (case char
          (#\<
           (push-string "&lt;"   new-string))
          (#\>
           (push-string "&gt;"   new-string))
          (#\&
           (push-string "&amp;"  new-string))
          (#\'
           (push-string "&apos;" new-string))
          (#\"
           (push-string "&quot;" new-string))
          (t
           (setf (char new-string j) char) (incf j)))))))

(defun xmlify (string)
  (let ((length (length string))
	(new-length (xml-length string)))
    (if (= length new-length)
	string
	(xmlify-internal string length (make-string new-length)))))
|#

;;; ======================================================================
;;; NOT part of KM's inference engine, but a utility for finding the supporting CLASSES for a triple
;;; ======================================================================

;;; [1] If the node leading to triple is deleted, remove its source class as a source of triple
;;; NOTE: triple-expanded-from removes non-existent instances
;;; Returns just the ORIGINAL supports
;(defun get-supports (triple)
;  (let ((f (first triple))
;	(s (second triple))
;	(v (third triple)))
;    (remove-duplicates
;     (append (intersection (my-mapcan #'prototype-classes (triple-cloned-from-originally triple)) ; prototypes
;			   (my-mapcan #'all-classes (triple-expanded-from triple)))	; [1]
;      	     (my-mapcan #'originated-from-classes
;			(remove-cloned-from-explns (get-explanations1 f s v))) ; traditional
;	     (my-mapcan #'originated-from-classes
;			(remove-cloned-from-explns (get-explanations1 v (invert-slot s) f)))))))

#|
(defun get-supports (triple)
  (let ((f (first triple))
	(s (second triple))
	(v (third triple)))
    (remove-duplicates
     (append (my-mapcan #'originated-from-classes (get-explanations1 f s v))
	     (my-mapcan #'originated-from-classes (get-explanations1 v (invert-slot s) f))))))
|#

#|
GIVEN: a triple
RETURNS: A list of classes where support for triple originated.
	Note: If prototype for C is cloned to SubC is cloned to SubSubC, then supports for triple
in SubSubC will be just C, not the intermediate class SubC also.

ALGORITHM OVERVIEW:
(get-supports <triple>) is essentially* the intersection of triple-cloned-from-originally** and the explanation database: any
   supporting triple must be both a triple-cloned-from-originally and part of a valid explanation of <triple>.
   Thus get-supports is necessarily a subset* of the originating classes that triple-cloned-from-originally would offer.
   * get-supports additionally returns supports from CLib axioms, and will compute supports where <triple> is a constraint.
     triple-cloned-from-originally does neither of these.
 ** (triple-cloned-from-originally <triple>): We find the triples Ts that <triple> was triple-cloned-from, and remove
     all the "pass through" triples PT in classes PC that:
	a. themselves rely on another triple in Ts
	b. have no added-at supports themselves, i.e., does NOT have (explanation PT ((added-at PC "User defined"))), although
		it can still have (explanation PT ((added-at GenC "User defined"))) and remain a pass-through triple

ALGORITHM for (get-supports <triple>):
 1. Find all explanations for <triple>.
    For each explanation, collect the supporting class:
         a. cloned-from explanations tell us that <triple> was cloned from <triple'> in <prototype>, thus collect <prototype-class>.
	 b. added-at explanations directly tell us which <class> the triple was added at
	 c. (every <class> has ...) explanations tell us which traditional KM <class> (CLib) was used to create <triple>

 2. As a refinement: There is a special case where some cloned-from supports may no longer be valid, as follows:
    Suppose (y r3 z) was cloned-from (origy r3 origz) in a prototype rooted at protoroot:

                                    [protoroot] -r2-> [origy] -r3-> [origz]     <== origin (support) of a triple in new-protoroot
    was cloned to		            |             |           |
                     [new-protoroot] -r1-> [x]     -r2-> [y]  -r3-> [z]		<== prototype being worked on

    get-supports checks that [x] still exists in the new protoroot, otherwise the inheritance is no longer valid.
    This is done by finding all the (origy r3 origz) using triple-cloned-from-originally, hence protoroot for each,
    hence [x] for each, and making sure that at least one of those [x]s still exists.
|#
(defvar *default-ignore-added-at-explanations* nil)

(defun get-supports (triple &key ignore-constraintsp (ignore-added-at-explanations *default-ignore-added-at-explanations*))
  (remove-duplicates
   (my-mapcan #'(lambda (support-detail)		; eg., a triple, or (added-at C "User defined") structure
		  (classes-in-support-detail support-detail :triple triple))
	      (get-support-details triple :ignore-constraintsp ignore-constraintsp :ignore-added-at-explanations ignore-added-at-explanations))))

(defun classes-in-support-detail (support-detail &key triple)
  (cond ((not (listp support-detail))
	 (report-error 'program-error
		       "get-supports: (get-support-details ~a) returned a non-list element ~a~%"
		       triple support-detail))
	((eq (first support-detail) '#$every) (list (second support-detail)))
	((eq (first support-detail) '|<location unknown>|) nil)
	((eq (first support-detail) '#$added-at) (list (second support-detail)))
	((triplep support-detail)
	 (let ((prototype-root (in-prototype support-detail)))
	   (cond (prototype-root (prototype-classes prototype-root))
		 (t (report-error 'program-error
				  "get-supports: support ~a for ~a returned by get-support-details doesn't seem to be part of a prototype!~%"
				  support-detail triple)))))
	(t (report-error 'program-error
			 "get-supports: Unrecognized structure ~a returned by (get-support-details ~a)~%"
			 support-detail triple))))

#|
RETURNS: three types of explanation:
	(i) a triple (for prototypes)
	(ii) a (every ...) expression (for original KM)
	     In principle, might also return (|<location unknown>| <expr>) if can't work out the originating class
	(iii) a (added-at <class> <comment) expression (for manually added links)
  eg: ((_Drive3 object _Car4) (every Control has (object ((a Device)))))
[1] Returns just the ORIGINAL supports: Suppose triple t1 is cloned to t2 is cloned to t3. Now we want to delete t1 and
     its deletable dependents. So when checking deletability, we need to see that t3 is supported by just t1 (rather
     than t1 and t2) in order to confirm that t3 is indeed deletable.
[2] If all nodes leading to triple are deleted, remove it.
     Method: find all the (cloned-from PN N) supports for triple. If the originating triple is in PN, ensure N exists.

[3] Sometimes a prototype C will have an "orphan" triple T which doesn't point back
    to anything. Thus (get-supports T) -> NIL, but (get-supports (clone T)) -> C, = bad.
    Either we need to add C as a support in (get-supports T), or remove C as a support in (get-supports (clone T))

[4] In principle, if a triple T in P traces back to T' in P', then there *must* be an explanation E = (T cloned-from P')
    We rely on this explanation to find where the root RP' in P' was cloned onto in P (i.e., RP), and then make sure it sill exists (which is probably overkill, but anyway...)
    BUT: If E is missing, we can't find the identity of RP, and hence can't check its existence.
|#
(defun get-support-details (triple &key ignore-constraintsp 		; e.g., (_Drive1 object _Car2), from get-supports/get-supports.km example
					(ignore-added-at-explanations *default-ignore-added-at-explanations*))
  (let* ((f (first triple))
	 (s (second triple))
	 (v (third triple))
	 (explanations (append (get-explanations1 f s v) (get-explanations1 v (invert-slot s) f)))
	 (originating-triples (triple-cloned-from-originally triple ; [1]  See kr/get-supports/test-get-supports3.lisp
							     :ignore-added-at-explanations ignore-added-at-explanations))
	 (originating-triples+prototypes (mapcar #'(lambda (originating-triple)
						    (list originating-triple (in-prototype originating-triple)))
						 originating-triples))
	 (still-valid-originating-triples ; [2]
	  (my-mapcan #'(lambda (originating-triple+prototype)
		       (let*
			((originating-triple (first originating-triple+prototype)) ; (_Drive3 object _Car4)
			 (prototype (second originating-triple+prototype)) ; _Drive3
			 (expanded-from (remove nil			   ; = another node in the prototype containing triple. (typically an element of triple, but not always)
					 (mapcar #'(lambda (explanation) ; (cloned-from _Drive3 _Drive1) -> _Drive1
						    (cond ((and (eq (explanation-type explanation) '#$cloned-from)
								(eq (second explanation) prototype)) ; protoroot node
							   (third explanation))))	; corresponding node in clone
						 explanations)))
			 (originating-triple-isv-explanations (get-explanations (first originating-triple) (second originating-triple) (third originating-triple)))
			 (originating-triple-explanations (my-mapcan #'explanations-in originating-triple-isv-explanations))
			 (originating-triple-added-ats (remove-if-not #'(lambda (explanation)
									  (eq (explanation-type explanation) '#$added-at))
								      originating-triple-explanations)))
			(cond ((or (null expanded-from)		; failed to find which sibling node in triple's prototype is the recipient (explanation missing), hence not able to check it's existence [4]
				   (some #'known-frame expanded-from)) ; probably necessarily succeeds now
			       (or originating-triple-added-ats ; if the ORIGINATING triple in C1 is flagged as (added-at C2), then C2 should be considered the source, not C1
				   (list originating-triple))))))
		     originating-triples+prototypes)) ;    (_Drive3 object _Car4)

;;; Note: copied constraints in (every X has (slot ((a Y with ((must-be-a Z)))))) WILL be collected by the
;;; normal access to the explanation database, just like normal values.
;;; The below ADDITIONALLY captures non-copied constraints
	 (constraints-on-classes ; special case for constraints on "every" expressions: These are NOT copied, so look up
	  (cond ((constraint-exprp v)
		 (let* ((inherited-rule-sets (inherited-rule-sets f s :retain-commentsp t))
			(constraints (remove nil (mapcan #'find-constraints-in-exprs inherited-rule-sets))))
;		   (km-format t "constraints = ~a~%" constraints)
		   (remove nil
		    (mapcar #'(lambda (constraint)
			(cond ((equal v (desource+decomment constraint))
			       (build-rule constraint))))
			    constraints))))))
	 (extra-support-details
	  (remove nil
	      (mapcar #'(lambda (expln)
;			  (cond ((or (not ignore-added-at-explanations)
;				     (neq (explanation-type expln) '#$added-at))
			  (cond ((and (eq (explanation-type expln) '#$added-at) ignore-added-at-explanations) nil)	; always fails now, we don't ignore added-ats
				(t (build-rule expln :ignore-constraintsp ignore-constraintsp))))
		      (remove-cloned-from-explns explanations)))) ; leaving traditional (every X has ...) supports
	 )
;    (km-format t "explanations = ~a~%" explanations)
    (remove-duplicates
     (append still-valid-originating-triples
	     extra-support-details
	     constraints-on-classes)
     :test #'equal)))			; AND (added-at <class> <comment>) supports

(defun add-support (triple support &key (situation (curr-situation)))
  (let ((f (dereference (first triple)))
	(s (second triple))
	(v (dereference (third triple))))
    (cond
     ((minimatch support '#$(added-at ?x ?y))
      (record-explanation-for `#$(the ,S of ,F) V support :situation situation)) ; which situation should we use?
     (t (report-error 'user-error
	      "add-support: Bad support structure ~a!~%Support structure must be of the form (added-at <class> <string>)~%"
	      support)))))

;;; Essentially a synonym for delete-explanation
(defun remove-support (triple support &key (situation (curr-situation)))
  (cond ((null support)
	 (report-error 'user-error "remove-support: Support to remove cannot be NIL!~%"))
	(t (let ((f (first triple))
		 (s (second triple))
		 (v (third triple)))
	     (delete-explanation f s v :explanation-to-delete support :situation situation)))))

(defun remove-supports (triple &key (situation (curr-situation)))
  (let ((f (first triple))
	(s (second triple))
	(v (third triple)))
    (delete-explanation f s v :explanation-to-delete 'all :situation situation))) ; keyword 'all means all explanations

(defun remove-cloned-from-explns (explanations)
  (remove-if #'(lambda (x) (and (listp x) (eq (explanation-type x) '#$cloned-from))) explanations))

;;; Copy explanations for (i s v) to a new triple (i' s v'), where renaming-alist
;;; provides bindings for renaming i, v, and all variables in the explanations.
(defun copy-explanations-for (triple &key (from-situation (curr-situation)) (to-situation *global-situation*)
					  renaming-alist)
  (let* ((instance (first triple))
	 (slot (second triple))
	 (val (third triple))
	 (invslot (invert-slot slot))
	 (r-instance (sublis renaming-alist instance))
	 (r-val (sublis renaming-alist val)))
    (mapc #'(lambda (r-explanation)
	      (record-explanation-for `#$(the ,SLOT of ,R-INSTANCE) r-val r-explanation :situation to-situation))
	  (sublis renaming-alist (get-explanations1 instance slot val from-situation)))
    (mapc #'(lambda (r-explanation)
	      (record-explanation-for `#$(the ,INVSLOT of ,R-VAL) r-instance r-explanation :situation to-situation))
	  (sublis renaming-alist (get-explanations1 val invslot instance from-situation)))
    t))

;;; ======================================================================

;;; Remove all explanations saying a triple was cloned from <protoroot>
(defun remove-cloned-from-explanations (isv-explanations protoroot)
  (remove-if #'(lambda (isv-explanation)
		 (let ((explanation (explanation-in isv-explanation)))
		   (and (eq (explanation-type explanation) '#$cloned-from)
			(eq (second explanation) protoroot))))
	     isv-explanations))

;;; ======================================================================
#|
(class-inferred-by-classificationp <instance> <class>) -> non-NIL / NIL
(class-inferred-by-classificationp '#$_Animal-Plasma-Membrane22951 '#$Semipermeable-Entity)

<class> must be a class of <instance>. Returns a non-NIL value if <class> was
inferred by automatic classification (use of a has-definition expression),
NIL otherwise.
NOTES:
 - This function only finds classes inferred through automatic classification.
   If will NOT detect cases where <class> was inferred through unification.
 - The function uses the explanation database, thus if *record-explanations*
   = NIL during inference time, it will not find any records of automatic
   classification having been applied.

Example Usage:

KM(13): (ask "What is the relationship between cholesterol and animal plasma membrane?")
 -> _Animal-Plasma-Membrane22951 ("semipermeable entity and animal plasma membrane")

;;; All immediate classes of an instance. In this case, one was given in the question, one
;;; was inferred through automatic classification
KM(16): (immediate-classes '#$_Animal-Plasma-Membrane22951)
(|Semipermeable-Entity| |Animal-Plasma-Membrane|)

;;; Find the subset that were NOT inferred through automatic classification
KM(19): (remove-if #'(lambda (class)
	          	    (class-inferred-by-classificationp '#$_Animal-Plasma-Membrane22951 class))
   	               (immediate-classes '#$_Animal-Plasma-Membrane22951))
(|Animal-Plasma-Membrane|)
|#

(defun class-inferred-by-classificationp (instance class)
  (cond
   ((not (isa instance class))
    (km-format t "(inferred-classp ~a ~a): ~a must be an instance of ~a (but isn't)!~%" instance class instance class))
   (t (let ((explanations (get-explanations1 instance '#$instance-of class)))
	(some #'(lambda (explanation)
		  (or (eq (second explanation) '#$has-definition)		; (X has-definition ...)	  - own-definition
		      (eq (third explanation) '#$has-definition))) 		; (every X has-definition ...)    - member-definition
	      explanations)))))




