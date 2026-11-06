
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: minimatch.lisp
;;; Author: Peter Clark
;;; Date: August 1994
;;; Purpose: Simplistic pattern-matching (see examples below)
;;; The system matches items with variables, returning a list of the
;;; matched items. All variables are anonymous.

#|
======================================================================
		(1) MINIMATCH
======================================================================

	(minimatch <s-expr> <pattern>) -> (<matching-value>*) | t

In minimatch, there is no explicit binding list returned, just the matched values, in order.

***IMPORTANT*** The variable names in minimatch are IGNORED, they just denote "some value".
  Thus repeated variables in the pattern may match different elements.

Minimatch is faster than full-match (see later).

Variables: Begin with a "?"
	?any: The item matching the variable ?any is ignored (not returned)
	?*: Can match multiple, consecutive items in a list. The matching values are ignored
		(not returned). If the overall pattern uses this and can match in more than
		one way, just the result of the first match is returned.
	&rest: This variable matches the rest of the list.

    (minimatch 'x 'y) => nil
    (minimatch '(a b c) '(a ?x ?y)) => (b c)
    (minimatch '(a b c) '(a ?x ?x)) => (b c)
    (minimatch '(a b) '(a b)) => t
    (minimatch '(a b c (d e)) '(a b ?x (?y ?z))) => (c d e)
    (minimatch '(a b c (d e)) '(a b ?x ?y)) => (c (d e))
    (minimatch '(a b c (d e)) '(a b &rest) => ((c (d e)))
    (minimatch '(a b c) '(a b ?any)) => t
    (minimatch '(a b c) '(a ?x ?any)) => (b)
    (minimatch '(1 2 3 4 5 6 7 8) '(?* 3 ?x ?* 6 ?y ?z ?*)) -> (4 7 8)

VARIANTS:
=========
minimatch1: Only valid when there's one variable in the pattern.
      Returns the item matching the variable, rather than a list of items.
        (minimatch  '(a b c) '(?x b c)) -> (a)
      	(minimatch1 '(a b c) '(?x b c)) -> a

mv-minimatch: Returns answers as multiple values, rather than a list:
      KM: (multiple-value-bind
		(x y)
	        (mv-minimatch '(a b c) '(a ?x ?y))
	     (format t "x=~a, y=~a~%" x y))
      x=B, y=C
   NOTE: The fact the Lisp variables are called x,y, and the pattern ?x,?y, is purely coincidental.

(minimatch-pattern <expr-list> <pattern-list>) -> (<matching-value>*) | t
(minimatch-pattern '((a 1) (b 2) (c 3)) '((b ?x) (a ?y))) -> (2 1)
   Match each pattern in <pattern-list> in turn against elements of <expr-list>, and
   return the concatenation of the bindings (if the whole <pattern-list> matches). Note
   an expr in <expr-list> can only match one pattern in <pattern-list>.

======================================================================
		(2) FULL-MATCH
======================================================================

   (full-match <s-expr> <pattern>) -> (<binding>*)
		where <binding> is (<var> . <value>)

This returns a binding list. Unlike minimatch, if a variable is used multiple times in
the pattern, it must bind to the same values. If there are no variables, or all
variables are ?any, the "null binding list" ((t . t)) is returned for a successful match.

   (full-match '(a b (c)) '(?a ?b ?c)) -> ((?a . a) (?b . b) (?c . (c)))
   (full-match '(a b c d) '(?any ?b &rest)) -> ((?b . b) (&rest . (c d)))
   (full-match '(a b (c)) '(?any ?b &rest)) -> ((?b . b) (&rest . ((c))))
   (full-match 1 1) -> ((t . t))
   (full-match 1 '?any) -> ((t . t))

Accessor for the returned binding list:
   (val-of '?b '((?b . b))) -> b

======================================================================
		(3) STRING-MATCH
======================================================================

   (string-match <string> <pattern>) -> (<matching-value>*) | t

Match a string against a pattern of string fragments. The pattern must consist
of alternating values of variable / string elements:

   (string-match "the cat sat" '("the" ?cat "sat")) --> (" cat ")
   (string-match "the cat sat" '(?var "the" ?cat "sat")) --> ("" " cat ")
   (string-match "the cat sat" '(?any " " ?word " " ?any)) --> ("cat")

string-match1: When there's just 1 variable, return is match rather than a list of matches.
mv-string-match: Return the matches as multiple values (for use with multiple-value-bind),
	rather than a list.
|#


(defun mv-minimatch-pattern (list patterns) (values-list (minimatch-pattern list patterns)))
(defun minimatch-pattern1 (list patterns) (first (minimatch-pattern list patterns)))

#||
(minimatch-pattern '((a 1) (b 2) (c 3)) '((b ?x) (a ?y))) -> (2 1)
Note: &rest can be used at the END of the patterns to bind with "everything else"
||#
(defun minimatch-pattern (list patterns)
  (cond
   ((endp patterns) 't)
   ((equal patterns '(&rest)) (list list))
   (t (let* ((pattern (first patterns)))
	(some #'(lambda (element)
		  (let* ((first-match (minimatch element pattern))
			 (rest-match (cond (first-match (minimatch-pattern (remove element list :test #'equal) (rest patterns))))))
		    (join-binds first-match rest-match)))		; returns NIL if either first-match or rest-match is NIL
	      list)))))

;;; ----------------------------------------

 ;;; Here where we know there's just ONE item
(defun minimatch1 (item pattern) (first (minimatch item pattern)))

;;; (find-pattern1 '((a r b) (a r c)) '(a r ?x)) -> b
;;; (find-pattern '((a r b) (a r c)) '(?x r ?y)) -> (a b)
(defun find-pattern1 (list pattern) (first (find-pattern list pattern)))

;;; Mini-matching -- doesn't keep an explicit binding list, but just the
;;; values which matched with variables, in order.
;;; (minimatch 'x 'y) => nil
;;; (minimatch '(a b c) '(a ?x ?y)) => (b c)
;;; (minimatch '(a b c) '(a ?x ?x)) => (b c)
;;; (minimatch '(a b) '(a b)) => t
;;; (minimatch '(a b c (d e)) '(a b ?x (?y ?z))) => (c d e)
;;; (minimatch '(a b c (d e)) '(a b ?x ?y)) => (c (d e))
;;; (minimatch '(a b c (d e)) '(a b &rest) => ((c (d e)))

(defun mv-minimatch (item pattern)
  (values-list (minimatch item pattern)))

(defun anonymous-minimatch-varp (var) (member var '(|?ANY| |?any| |?*|)))
(defun wildcard-varp (var) (eq var '?*))

;;; Must distinguish failure (nil) and no bindings (t)
;;; Mar'04 - use of wildcard variable ?*
;;; CL-USER(28): (minimatch '(1 2 3 4 5 6 7 8) '(?* 3 ?x ?* 6 ?y ?z ?*))
;;; (4 7 8)
(defun minimatch (item pattern)
   (cond
      ((anonymous-minimatch-varp pattern) 't)
      ((var-p pattern) (list item))
      ((and (singletonp pattern) (restvar-p (first pattern))) (list item))
      ((atom pattern)
       (cond ((equal item pattern) 't)))
      ((listp item)
       (cond ((wildcard-varp (first pattern))		; '(1 2 3) '(?* 3)
	      (or (minimatch item (rest pattern))			; ?* = no elements
		  (and item (minimatch (rest item) (rest pattern)))	; ?* = 1 element
		  (and item (minimatch (rest item) pattern))))		; ?* = 2 or more elements
	     (item
	      (let ( (carmatch (minimatch (car item) (car pattern))) )
		(cond (carmatch
		       (join-binds carmatch
				   (minimatch (cdr item) (cdr pattern)))))))))))

(defun join-binds (binds1 binds2)
   (cond ((null binds1) nil)
	 ((null binds2) nil)
         ((equal binds1 't) binds2)
	 ((equal binds2 't) binds1)
	 (t (append binds1 binds2))))

;;; Modified faster version thanks to Adam Farquhar!
;;; Renamed from varp to avoid name clash with Novak's code
;;; Synonymous with km-varp
(defun var-p (var)
  (and (symbolp var)
       (symbol-starts-with var #\?)))

(defun restvar-p (x)
; (and (symbolp x) (starts-with (string-downcase x) "&rest")) - less efficient
  (member x '(&rest &rest1 &rest2 &rest3 &rest4 &rest5 |&rest| |&rest1| |&rest2| |&rest3| |&rest4| |&rest5|)))

(defun find-pattern (list pattern)
  (cond ((endp list) nil)
	((minimatch (first list) pattern))
	(t (find-pattern (rest list) pattern))))

;;; ======================================================================
;;;	USE OF THE MINIMATCHER TO SELECT A LAMBDA EXPRESSION
;;; ======================================================================

#|
find-handler -- finds a (pattern function) pair where pattern matches the input
expr, and returns a LIST of THREE things:
  - function
  - a list of values in expr which matched the variables in pattern
  - the entire pattern which the input expr matched

e.g.,
(find-handler '(the house of john) *km-handler-alist*) =>
    (#'(lambda (slot path) (getval slot path))
     (house john)
     (the ?slot of ?expr))
|#
(defun find-handler (expr handler-alist &key (fail-mode 'fail))
  (cond ((endp handler-alist)
	 (cond ((eq fail-mode 'error)
		(format t "ERROR! Can't find handler for expression ~a!~%"
			expr) nil)))
	(t (let* ( (pattern+handler (first handler-alist))
		   (pattern (first  pattern+handler))
		   (handler (second pattern+handler))
		   (bindings (minimatch expr pattern)) )
	     (cond ((eq bindings 't) (list handler nil pattern))
		   (bindings (list handler bindings pattern))
		   (t (find-handler expr (rest handler-alist) :fail-mode fail-mode)))))))

;;; Default method of applying
;;; Or could apply with extra args, eg.
;;; 	(apply (first handler) (cons depth (second handler)))
(defun apply-handler (handler)
  (apply (first handler) (second handler)))

(defun find-and-apply-handler (expr handler-alist &key (fail-mode 'fail))
  (let ( (handler (find-handler expr handler-alist :fail-mode fail-mode)) )
    (cond (handler (apply-handler handler)))))

;;; ======================================================================
;;;		SAME, EXCEPT FOR STRINGS
;;; ======================================================================

;;; If :case-sensitivep = nil, then string matches are case-insensitive
(defun string-match1 (item pattern &key case-sensitivep)
  (first (string-match item pattern :case-sensitivep case-sensitivep)))

(defun mv-string-match (string pattern &key case-sensitivep)
  (values-list (string-match string pattern :case-sensitivep case-sensitivep)))

;;; ADD: Allow (or ...) structure: (string-match "cat" '("c" (or "x" "a") "t")) -> T
;;; (string-match "the cat sat" '("the" ?cat "sat")) --> (" cat ")
;;; (string-match "the cat sat" '(?var "the" ?cat "sat")) --> ("" " cat ")
;;; Expand to allow ?any as a variable
;;; (string-match "the cat sat" '(?any " " ?word " " ?any)) --> ("cat")
;;; **NOTE** A variable CANNOT be followed by a "", e.g., This will fail:   (string-match "cat" '(?x (or "?" ""))).   There must be a non-null anchor string directly *after* a variable
(defun string-match (string pattern &key case-sensitivep)
  (let ( (pattern-el (first pattern)) )
    (cond ((null pattern)
	   (cond ((string= string "") t)))
;	  ((member pattern '((&rest) (|&rest|)) :test #'equal) (list string))
	  ((and (singletonp pattern) (restvar-p (first pattern))) (list string))
	  ((and (listp (first pattern))
		(member (first (first pattern)) '(or |or|)))
	   (some #'(lambda (first-pattern)
		     (string-match string (cons first-pattern (rest pattern)) :case-sensitivep case-sensitivep))
		 (rest (first pattern)))) ; strip "or"
	  ((stringp pattern-el)
	   (cond
	    ((and (>= (length string) (length pattern-el))
		  (or (string= string pattern-el :end1 (length pattern-el))
		      (and (not case-sensitivep)
			   (string= (string-downcase string) (string-downcase pattern-el) :end1 (length pattern-el)))))
	     (string-match (subseq string (length pattern-el))
			   (cdr pattern)
			   :case-sensitivep case-sensitivep))))
	  ((and (anonymous-minimatch-varp pattern-el)
		(singletonp pattern)) t)
	  ((and (var-p pattern-el)
		(singletonp pattern)) (list string))
	  ((var-p pattern-el)
	   (let* ((pattern-el2 (second pattern))
		  (pattern-els2 (cond ((stringp pattern-el2) (list pattern-el2))
				      ((and (listp pattern-el2) (member (first pattern-el2) '(or |or|)) (every #'stringp (rest pattern-el2))) (rest pattern-el2)))))
	     (some #'(lambda (pattern-el2)
		       (let ((end-string-posn (cond (case-sensitivep (search pattern-el2 string))
						    (t (search (string-downcase pattern-el2) (string-downcase string))))))
			 (cond (end-string-posn
				(let ((rest-matches (string-match (subseq string
									  (+ end-string-posn
									     (length pattern-el2)))
								  (cddr pattern)
								  :case-sensitivep case-sensitivep)))
				  (cond ((anonymous-minimatch-varp pattern-el) rest-matches)
					(t (cons-binding (subseq string 0 end-string-posn) rest-matches))))))))
		   pattern-els2)))
	  ((singletonp pattern)		; (or ("the " (or "man" "woman")) "a kid")  -> (("the " (or "man" "woman"))
	   (string-match string (first pattern) :case-sensitivep case-sensitivep))
	  (t (format t "ERROR! (string-match ~s ~s) bad syntax!~%"
		     string pattern) nil))))

;;; binding or bindings = nil imply match-failure
(defun cons-binding (binding bindings)
  (cond ((null bindings) nil)
	((null binding) nil)
	((equal bindings 't) (list binding))
	(t (cons binding bindings))))

;;; ======================================================================

;;; (full-match '(a b (c)) '(?a ?b ?c)) -> ((?a . a) (?b . b) (?c . (c)))
;;; (full-match '(a b c d) '(?any ?b &rest)) -> ((?b . b) (&rest . (c d)))
;;; (full-match '(a b (c)) '(?any ?b &rest)) -> ((?b . b) (&rest . ((c))))
;;; (full-match 1 1) -> ((t . t))
;;; (val-of '?b '((?b . b))) -> b
(defun full-match (item pattern &key (bindings *null-bindings*))
   (cond
      ((anonymous-minimatch-varp pattern) bindings)
      ((var-p pattern) (add-binding pattern item bindings))
;     ((member pattern '((&rest) (|&rest|)) :test #'equal) bindings)
      ((and (singletonp pattern) (restvar-p (first pattern))) (add-binding (first pattern) item bindings))
      ((atom pattern)
       (cond ((equal item pattern) bindings)))
      ((listp item)
       (cond ;((wildcard-varp (first pattern))		; '(1 2 3) '(?* 3)
	     ; (or (full-match item (rest pattern))			; ?* = no elements
	     ;	  (and item (full-match (rest item) (rest pattern)))	; ?* = 1 element
	     ;	  (and item (full-match (rest item) pattern))))		; ?* = 2 or more elements
	     (item
	      (let ((new-bindings (full-match (car item) (car pattern) :bindings bindings)) )
		(cond (new-bindings (full-match (cdr item) (cdr pattern) :bindings new-bindings)))))))))

