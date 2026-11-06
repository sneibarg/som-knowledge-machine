
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: anglify.lisp
;;; Author: Peter Clark
;;; Date: Separated out Aug 1994
;;; Purpose: Concatenation and customisation of text-fragments

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

; If nil then 3 -> "3". If t then 3 -> "the value 3"
(defparameter *verbose-number-to-text* nil)

(defparameter *default-km-behavior-for-expand-text* t)

;;; ======================================================================
;;;		CONCATENATING TEXT FRAGMENTS TOGETHER NICELY
;;; ======================================================================

#|
make-phrase/make-sentence:
INPUT: Can be either a single KM expression, or a :set / :seq of KM expressions -- make-sentence will
flatten them out and doesn't care. :set and :seq flags are ignored, and sequence is preserved.
RETURNS: A string built from these fragments, possibly capitalized and with a terminator added.

If a KM instance is included in the input, then this function will recursively replace it by (the name of <instance>)
until (the name of <instance>) just returns <instance>. This typically happens when <instance> is a class name:
	-> (the name of _Dog3) constructs (:seq "a" Dog), then calls itself again for instances in this expression
  	  -> (the name of Dog) -> Dog			; fixed point
	  <- Dog
	<- (:seq "a" Dog)

NOTE: :htmlify flag isn't used by KM, but might be by the user if (i) he/she makes a top-level call to
	make-phrase/make-sentence, and (ii) he/she redefines (make-name ...) to respond to a :htmlify t flag.
|#
(defun make-phrase (text &key htmlify)
  (make-sentence text :capitalize nil :terminator "" :htmlify htmlify))

(defun make-sentence (text &key (capitalize t) (terminator ".") htmlify)
  (let ( (new-string
	            (trim-whitespace
		     (concat-list
		      (spacify
		       (remove nil
			(mapcar #'(lambda (i)
				    (cond
				     ((null i) nil)
				     ((stringp i) i)
				     ((numberp i) (princ-to-string i))
				     ((member i '#$(:seq :set :triple)) nil)
				     ((symbolp i) (string-downcase i))
				     (t (report-error 'user-error "make-sentence/phrase: Don't know how to convert ~a to a string!~%" i))))
				(flatten (listify (expand-text text :htmlify htmlify))))))))) )
    (cond ((string= new-string "") "")
	  (t (let ( (terminated-string (cond ((not (ends-with new-string terminator)) (concat new-string terminator))
					     (t new-string))) )
	       (cond (capitalize (capitalize terminated-string))
		     (t terminated-string)))))))

#|
expand-text: This function takes a KM structure or atom, eg. a (:seq ...) structure, and recursively expands
it to more primitive fragments using calls to (km-name ...). It eventually bottoms out when (km-name X) returns X. An
example of the expansion might be:
   (:seq _Engine23 "has purpose" _Purpose24)
-> (:seq (:seq "a" Engine) "has purpose" ("a" Propelling "whose object is" _Airplane25))
-> (:seq (:seq "a" Engine) "has purpose" ("a" Propelling "whose object is" (:seq "a" Airplane)))   [<= final result]

where (km-name _Engine23) -> (:seq "a" Engine)
      (km-name _Purpose24) -> ("a" Propelling "whose object is" _Airplane24)
      (km-name _Airplane25) -> (:seq "a" Airplane)
|#
(defun expand-text (item &key htmlify (depth 0))
  (let ( (expanded (remove '#$:seq (flatten (expand-text0 item :htmlify htmlify :depth depth)))) )
    (cond ((null expanded) nil)
	  ((singletonp expanded) (first expanded))
	  (t (cons '#$:seq expanded)))))

(defun expand-text0 (item &key htmlify (depth 0))
  (cond ((> depth 100)
	 (report-error 'user-error "make-sentence/phrase: Infinite recursion when generating name for ~a!~%" item))
	((stringp item) item)
	((numberp item)
	 (cond (*verbose-number-to-text* (list "the value" item))
	       ((integerp item) item)
	       (*output-precision*
		(cond ((>= item 1.0) (format nil (concat "~," (princ-to-string *output-precision*) "f") item))
		      ((>= item (expt 10 (- *output-precision*)))
		       (let ((number
			      (format nil (concat "~," (princ-to-string (- *output-precision* (floor (log item 10)))) "f")
				      item)))
			 (cond ((search "." number) (string-right-trim '(#\0) number))
			       (t number))))
		      (t (format nil (concat "~," (princ-to-string *output-precision*) "e") item))))
	       (t item)))
;	((null item) (list "??"))		; why did I put this in? Add developer-mode flag
	((and (null item) *developer-mode*) (list "??"))

; Modified by Sririam:
	((listp item)
	 (cond
	  (*default-km-behavior-for-expand-text*
	   (mapcar #'(lambda (i) (expand-text0 i :htmlify htmlify :depth (1+ depth))) item))
	  ;;; If NIL, switch to Sririam's alternative
	  (t (mapcar #'(lambda (i) (if (and (symbolp i)  (not (member i '(:|seq| :|set| NIL))) (not (or (kb-objectp i) (km-triplep i))))
				       (expand-text0 (string i) :htmlify htmlify :depth (1+ depth))
				     (expand-text0 i :htmlify htmlify :depth (1+ depth)))) item))))
	((member item '#$(:seq :set :bag :pair)) item)
	;((member item '#$(:seq :set :bag :pair)) "")
	((or (kb-objectp item)
	     (km-triplep item))
	 (let ( (name (km-name item)) )
	   (cond ((equal name item) item)
		 (t (expand-text0 name :depth (1+ depth))))))
	(t (report-error 'user-error "make-sentence/phrase: Bad element `~a' encountered!!~%" item))))

#|
;;; The htmlify flag is passed here in case the user wants to redefine make-name to actually do something with the flag!
(defun make-name (item &key htmlify)
  (declare (ignore htmlify))
  (let ( (names (km-int `#$(the name of ,ITEM))) )
    (cond ((singletonp names)
	   (cond ((stringp (first names)) (first names))
		 (t (report-error 'user-error "make-sentence/phrase: (the name of ~a) should return a string,~%but it returned ~a instead!~%"
				  item (first names)))))
	  ((null names) "???")
	  (t (report-error 'user-error "make-sentence/phrase: (the name of ~a) should return a single string,~%but it returned ~a instead!~%"
			   item names)))))
|#

(defparameter *nospace-string* "nospace")

;;; This could be written a million times better!
;;; words = A flattened list of strings.
;;; Periods must be a separate string (".") for capitalization to work
;;; properly.
(defun spacify (words)
  (cond ((null words) nil)
	((singletonp words) words)
	((white-space-p (second words) :whitespace-chars '(#\Space #\Tab))	; (but not #\Newline)
	 (spacify (cons (first words) (rest (rest words)))))
	((string= (first words) ".")
	 (cond ((and (string= (second words) (string #\Newline))
		     (not (null (third words))))
		(cons (first words)
		      (cons (second words)
			    (spacify (cons (capitalize (third words)) (rest (rest (rest words))))))))
	       (t (cons ". " (spacify (cons (capitalize (second words))
					    (rest (rest words))))))))
;	((char= (first-char (second words)) #\-)	;; Special character, which forces no space
;	 (cons (first words)
;	       (spacify (cons (butfirst-char (second words))
;				    (rest (rest words))))))
	((string= (first words) *nospace-string*)	; handle multiple "nospace"s in a line
	 (spacify (rest words)))
	((string= (second words) *nospace-string*)
	 (cons (first words)
	       (spacify (rest (rest words)))))
	(t (cons (first words)
		 (cons (a-space (first words) (second words))
		       (spacify (rest words)))))))

;;; "dog" -> "Dog"
(defun capitalize (string)
  (concat (string-upcase (first-char string)) (butfirst-char string)))

;;; Crude!
;;; (a-space "cat" "dog") -> " "
;;; (a-space "cat" " dog") -> ""
;;; (a-space "cat " "dog") -> ""
(defun a-space (word1 word2)
  (cond ((no-following-spaces  (last-char word1)) "")
	((no-preceeding-spaces (first-char word2)) "")
	(t " ")))

(defun no-following-spaces (char)
  (member char '( #\( #\  )))

(defun no-preceeding-spaces (char)
  (member char '( #\' #\) #\. #\, #\ )))

;;; ======================================================================
;;;			NAMES OF FRAMES
;;; ======================================================================
#|
Name returns a (possibly nested) list of fragments, which together produce a top-level name
for an object. name *doesn't* call itself recursively.

To recursively expand the name for objects, use make-phrase or make-sentence. These two functions
recursively convert symbols to their name structures, and then flatten, stringify, and concatenate
the result.
|#

;(defun km-name (concept &key htmlify)
;  (cond ((tracep) (prog2 (suspend-trace) (name0 concept :htmlify htmlify) (unsuspend-trace)))
;	(t (name0 concept :htmlify htmlify))))

;;; [1] to prevent situation-specific instances all inheriting name "the thing" from the global situation!
;;;     9/18/02 - this is no longer applicable, as KM no longer evaluates situation-specific stuff globally
;;; [2] Ken Barker doesn't want this.
(defun km-name (concept &key htmlify)
  (let ((*trace* nil))
    (cond
        ((stringp concept) concept)
	((numberp concept) (princ-to-string concept))
;[2]	((protoinstancep concept) (prototype-name concept :htmlify htmlify))			; <== new
	((km-triplep concept) (triple-name concept))
	((let ( (name (km-int `#$(the name of ,CONCEPT))) )
	   (cond
	    ((singletonp name) (first name))
	    ((not (null name))
	     (make-comment "Warning! ~a has multiple name expressions ~a!~%     Continuing just using the first (~a)..."
				      concept name (first name))
	     (first name)))))
	((km-unique-int `#$(the name of ,CONCEPT)))
	((symbol-starts-with concept #\*)		; "*pete" -> "pete"
	 (butfirst-char (string-downcase concept)))
	((anonymous-instancep concept)
	 (cond (t ;(not (equal (immediate-classes concept) '#$(Thing)))	; else return NIL [1]
		(anonymous-instance-name concept :htmlify htmlify))))
;	((atom concept) (string-downcase concept))
	((atom concept)
	 (if (not *default-km-behavior-for-expand-text*)
	     (string concept)
	   (string-downcase concept)))
	(t concept))))

(defun anonymous-instance-name (concept &key htmlify)
  (declare (ignore htmlify))
;  (concat "the " (km-name (first (immediate-classes concept)))))
  `(#$:seq "the" ,(km-name (first (immediate-classes concept)))))

;;; ----------

#|
Not used any more
(defun prototype-name (concept &key htmlify)
  (declare (ignore htmlify))
  (cond ((not (protoinstancep concept))
	 (report-error 'user-error "Trying to generate prototype name of non-prototype ~a!~%" concept))
	((prototypep concept)
	 (or (km-unique-int `#$(the name of ,CONCEPT))
	     (let ( (parent (first (immediate-classes concept))) )
	       `(#$:seq "a" ,(km-name parent)))))
	(t `(#$:seq "the" ,(km-name (first (immediate-classes concept)))
		  "of" ,(prototype-name (km-unique-int `#$(the prototype-participant-of of ,CONCEPT) :fail-mode 'error))))))
|#

;;; ----------

#|
CL-USER> (triple-name '#$(:triple *pete owns (:set *money *goods *food)))
(:|seq| "pete" |owns| (:|seq| "money" ", " "goods" ", and " "food"))
CL-USER> (triple-name '#$(:triple *pete believes (:triple *joe owns *goods)))
(:|seq| "pete" |believes| (:|seq| "joe" |owns| "goods"))
|#
(defun triple-name (triple &key htmlify)
  (let ( (vals (val-to-vals (fourth triple))) )
    (list '#$:seq
	  (km-name (second triple) :htmlify htmlify) ; ("pete")
	  (km-name (third triple) :htmlify htmlify)  ; ("owns")
	  (cond ((null vals) nil)
		((singletonp vals) (km-name (first vals) :htmlify htmlify))
		(t (cons '#$:seq
			 (andify (mapcar #'(lambda (v) (km-name v :htmlify htmlify)) vals))))))))




