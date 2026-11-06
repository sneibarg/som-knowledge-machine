
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: utils.lisp
;;; Author: Peter Clark
;;; Date: 1994
;;; Purpose: General Lisp utilities

;;; (flatten '((a b) (c (d e))))  ->  (a b c d e)
;;; (flatten 'a) -> (a)
;(defun flatten (list)
;  (cond ((null list) nil)
;	((atom list) (list list))
;	((aconsp list) (list (first list) (rest list)))	; won't handle '(a b . c)
;	(t (my-mapcan #'flatten list))))

;;; optimized version from Francis Leboutte
(defun flatten (l)
  (cond ((atomic-aconsp l)
         (list (car l) (cdr l)))
        (t (flatten-aux l))))

;;; avoid consing
(defun flatten-aux (l &optional (acc nil))
  (cond ((null l) acc)
        ((atom l) (cons l acc))
        ((atomic-aconsp l)
         (cons (car l)
               (cons (cdr l)
                     acc)))
        (t (flatten-aux (first l)
                        (flatten-aux (rest l) acc)))))

;;; No :from-end keyword on (member ...), so create this!
;;; (last-member 'a '(a b a c a d)) -> (A D)
(defun last-member (item list &key (test #'eql))
  (cond ((endp list) nil)
	(t (let ((rest-list (member item list :test test)))
	     (or (last-member item (rest rest-list) :test test)
		 rest-list)))))

;;; see km function aconsp
;;; T if a cons and both elements of cons are atomic
;;; error if a cons and first element is a list
(defun atomic-aconsp (x)
  (cond ((aconsp x)
         ;; should remove this test?
         (when (listp (car x))
           (error "flatten: not a KM atomic cons: ~s"  x))
         t)
        (t nil)))

;;; ----------
;;; (aconsp '(a . b)) -> t
(defun aconsp (obj) (and (listp obj) (not (listp (rest obj)))))

;;; ======================================================================

(defun listify (atom)
   (cond ((listp atom) atom)
	 (t (list atom))))

;;; (append-list '((1 2) (3 4))) => (1 2 3 4)
(defun append-list (list)
  (format t "append-list has been renamed as append-lists! Please change your code! Continuing...~%")
  (append-lists list))

(defun listify-if-there (x) (cond (x (list x))))

;;; ----------------------------------------

#|
;;; (my-split-if '(1 2 3 4) #'evenp) => ((2 4) (1 3))
;;; (mapcar #'append-list (transpose (mapcar #'(lambda (seq) (my-split-if seq #'evenp)) '((1 2 3 4) (5 6 7 8) ...))))
;;; [PEC: ?? but why not just do (my-split-if (append '((1 2 3 4) (5 6 7 8) ...)) #'evenp) ?
;;; ((2 4 6 8) (1 3 5 7))
(defun my-split-if (sequence function)
  (cond ((endp sequence) nil)
	(t (let ( (pass+fail (my-split-if (rest sequence) function)) )
	     (cond ((funcall function (first sequence))
		    (list (cons (first sequence) (first pass+fail)) (second pass+fail)))
		   (t (list (first pass+fail) (cons (first sequence) (second pass+fail)))))))))
|#

;;; Rewrite and rename. This time, returns multiple values (i) those passing the text (ii) those failing
;;; (partition '(1 2 3 4) #'evenp) => (2 4) (1 3)
;;; ((2 4 6 8) (1 3 5 7))
(defun partition (sequence function)
  (cond ((endp sequence) nil)
	(t (multiple-value-bind
	    (pass fail)
	    (partition (rest sequence) function)
	    (cond ((funcall function (first sequence))
		   (values (cons (first sequence) pass) fail))
		  (t (values pass (cons (first sequence) fail))))))))

;;; ======================================================================
;;;			SOME *-EQUAL FUNCTIONS
;;; ======================================================================

;;; unlike assoc, item can be a structure
;;; > (assoc-equal '(a b) '(((a b) c) (d e)))
(defun assoc-equal (item alist)
  (cond ((endp alist) nil)
	((equal item (first (first alist))) (first alist))
	(t (assoc-equal item (rest alist)))))

(defun member-equal (item list)
  (cond ((endp list) nil)
	((equal item (first list)) list)
	(t (member-equal item (rest list)))))

;;; ======================================================================
;;;		MAPPING FUNCTIONS
;;; ======================================================================

;;; my-mapcan: non-destructive version of mapcan
;;; [1] (my-mapcan ...) fails in some Lisp implementations if you exceed
;;; the maximum number of arguments allowed a Lisp function (here #'append)
;#+allegro
;(defun my-mapcan (function args)
;  (apply #'append (mapcar function args)))

;#-allegro
;(defun my-mapcan (function args)
;  (mapcan #'copy-list (mapcar function args)))

;;; Let's do it the safe way all the time (ug - too memory intensive?)
;(defun my-mapcan (function args)
;  (mapcan #'copy-list (mapcar function args)))

;;; This version is more space-efficient, thanks to Roger Corman
(defun my-mapcan (function args)
    (do* ((result '())
          (arglist args (cdr arglist)))
         ((null arglist) (nreverse result))
      (let ((res (funcall function (car arglist))))
        (dolist (x res)
          (push x result)))))

;;; This implementation is better than (apply #'append lists) or (reduce #'append lists)
;;; Could also implement this as (apply #'concatentate (cons 'list lists)) - would that be any better?
(defun append-lists (lists)
  (mapcan #'copy-list lists))

;; eg. (map-recursive #'string-upcase '("as" ("asd" ("df" "df") "ff")))
;;     ("AS" ("ASD" ("DF" "DF") "FF"))
(defun map-recursive (function tree)
  (cond ((null tree) nil)
	((not (listp tree)) (funcall function tree))
	(t (cons (map-recursive function (car tree))
		 (map-recursive function (cdr tree))))))

;;; (recursive-find 'a '(1 2 (c 3) (a)))
(defun recursive-find (item tree)
  (cond ((eql item tree))
	((null tree) nil)
	((listp tree)
	 (some #'(lambda (subtree) (recursive-find item subtree)) tree))))

;;; ----------------------------------------

#|
KM> (defun demo (x) (cond ((> x 0) (values x (* x x)))))
KM> (some #'demo '(-1 3 2))
3
KM> (multiple-value-some #'demo '(-1 3 2))
3
9
|#
;;; This just written for two-valued arguments
(defun multiple-value-some (fn arg-list)
  (cond ((endp arg-list) nil)
	(t (multiple-value-bind
	       (x y)
	       (apply fn (list (first arg-list)))
	     (cond (x (values x y))
		   (t (multiple-value-some fn (rest arg-list))))))))

;;; ======================================================================
;;;		GENERAL UTILITIES
;;; ======================================================================

(defvar *tell-stream* t)
(defvar *see-stream* t)
(defvar *append-stream* t)

(defun file-exists (file) (open file :direction :probe))

;;; Check you don't close the stream "t"
(defun close-stream (stream) (cond ((streamp stream) (close stream))))

;;; (see) and (tell) open files with my standard default modes.
;;; They also cache the stream, just in case an error occurs during
;;; interpretation (otherwise you've lost the handle on the stream).
;;; t will send to std output, nil will output to nothing.
(defun tell (file)
  (cond ((null file) nil)
	((eq file t) (format t "(Sending output to standard output)~%") t)
	(t (setq *tell-stream* (open file
			    :direction :output
			    :if-exists :supersede
			    :if-does-not-exist :create)))))

(defun told () (close-stream *tell-stream*) (setq *tell-stream* t))

(defun see (file)
  (cond ((eq file t) t)		; read from standard input
	(t (setq *see-stream* (open file :direction :input)))))

(defun seen () (close-stream *see-stream*) (setq *see-stream* t))

(defun tell-append (file)
  (cond ((null file) nil)
	((eq file t) (format t "(Sending output to standard output)~%") t)
	(t (setq *append-stream* (open file
				    :direction :output
				    :if-exists :append
				    :if-does-not-exist :create)))))

(defun told-append () (close-stream *append-stream*) (setq *append-stream* t))

;;; Useful for finding mis-matching parentheses
(defun read-and-print (file)
  (let ( (stream (see file)) )
    (read-and-print2 stream)
    (close stream)))

(defun read-and-print2 (stream)
  (let ( (sexpr (read stream nil nil)) )
    (cond (sexpr (print sexpr) (read-and-print2 stream)))))

;;; Bug(?) in CL: (read-string <string> nil nil) should return nil if <string> is an incomplete s-expr (e.g. "\""cat")
;;; but in practice generates an eof error regardless. (What I wanted to do was a read-string followed by integerp test).
(defun my-parse-integer (string)
  (multiple-value-bind
   (integer n-chars)
   (parse-integer string :junk-allowed t)
   (cond ((= (length (princ-to-string integer)) n-chars) integer))))

;;; ======================================================================
;;;		BLOWFISH ENCRYPTION (Allegro utility only)
;;; ======================================================================

#+allegro
(defun encrypt-to-file (file string &key key)
  (write-file-array file (user::blowfish-encrypt string :key key) :element-type '(unsigned-byte 8)))

#+allegro
(defun decrypt-from-file (file &key key)
  (user::blowfish-decrypt (read-file-array file :element-type '(unsigned-byte 8)) :key key :string t))

;;; ======================================================================
;;;	Reading and writing arrays, strings, bytes, and chars to/from files
;;; ======================================================================

;;; byte-file -> array
(defun read-file-array (file &key element-type)
  (let ((data (read-file-bytes file :element-type element-type)))
    (make-array (length data) :element-type element-type :initial-contents data)))

;;; array -> byte-file
(defun write-file-array (file array &key element-type)
  (let ((stream (open file :element-type element-type :direction :output
		      :if-does-not-exist :create :if-exists :supersede)))
    (loop for i from 0 to (1- (length array)) do
	  (write-byte (aref array i) stream))
    (cond ((streamp stream) (close stream)))))

;;; read byte-file
(defun read-file-bytes (file &key element-type)
  (let ((stream (open file :element-type element-type :direction :input)))
    (prog1
	(loop for item = (read-byte stream nil 'eof-marker) until (eql item 'eof-marker) collect item)
      (cond ((streamp stream) (close stream))))))

;;; read txt file as a single gigantic string
(defun read-file-string (file) (implode (read-file-chars file)))

(defun read-file-chars (file)
  (let ((stream (open file :direction :input)))
    (prog1
	(loop for item = (read-char stream nil 'eof-marker) until (eql item 'eof-marker) collect item)
      (cond ((streamp stream) (close stream))))))

;;; ----------------------------------------
;;; 	READ AN ENTIRE FILE INTO A LIST:
;;; ----------------------------------------
;;; Returns a list of strings
(defun read-file-lines (file) (read-file file))
(defun read-file-exprs (file) (read-file file 'sexpr))
(defun case-sensitive-read-file-exprs (file) (read-file file 'case-sensitive-sexpr))

(defun read-file (file &optional (type 'string))
  (cond
   ((not (member type '(string sexpr case-sensitive-sexpr)))
    (format t "ERROR! Unrecognized unit-type ~s in read-file!~%" type))
   (t (let ((stream (see file)))
	(prog1
	    (loop for item = (case type
			       (string (read-line stream nil 'eof-marker))
			       (sexpr  (read      stream nil 'eof-marker))
			       (case-sensitive-sexpr (case-sensitive-read stream nil 'eof-marker))) ; defined in case.lisp
		until (eq item 'eof-marker) collect item)
	  (cond ((streamp stream) (close stream))))))))

;;; ------------------------------

(defun write-file (file lines)
  (let ( (stream (tell file)) )
    (write-lines lines stream)
    (close-stream stream)))

#|
;;; Works, but apply-recursive can be *very* slow as it's interpreted
(defun write-lines (lines &optional (stream t))
  (apply-recursive #'(lambda (line)
		       (format stream "~a~%" line))
		   lines))
|#

(defun write-lines (structure &optional (stream t))
  (cond
   ((null structure) nil)
   ((atom structure) (format stream "~a~%" structure))
   ((and (listp structure)
	 (null (first structure)))
    (write-lines (rest structure) stream))
   ((listp structure)
    (cons (write-lines (first structure) stream)
	  (write-lines (rest structure) stream)))
   (t (format t "ERROR! Don't know how to do write-lines on structure:~%")
      (format t "ERROR! ~s~%" structure))))

; ----------

(defun apply-recursive (function structure)
  (cond
   ((null structure) nil)
   ((atom structure) (funcall function structure))
   ((listp structure)
    (cons (apply-recursive function (first structure))
	  (apply-recursive function (rest structure))))
   (t (format t "ERROR! Don't know how to apply-recursive on structure:~%")
      (format t "ERROR! ~s~%" structure))))

;;; ======================================================================

(defun print-list (list) (mapcar #'print list) t)

;;; Below command means DON'T define neq in Mac CommonLisp (as it's a built-in)
;;; but it is NOT defined in openmcl
;;; #-(and MCL (not openmcl))
;;; REVISED: NEQ is now apparently defined in openmcl, so change the defn.
#-MCL
(defun neq (a b) (not (eq a b)))

;;; (nlist 3) --> (1 2 3)
(defun nlist (nmax &optional (n 1))
  (cond ((<= nmax 0) nil)
	((>= n nmax) (list n))
	(t (cons n (nlist nmax (1+ n))))))

;;; (duplicate 'hi 2) ==> (hi hi)
(defun duplicate (item length)
  (make-sequence 'list length :initial-element item))

; Better: use ~vT directive in format
; BUT!! Bug under Harlequin - column counter doesn't get reset by a <nl> from
; user (as a result of a read-line or read).
(defun spaces (n)
  (make-sequence 'string n :initial-element #\ ))
;
; (defun tab (n &optional (stream t))
;    (cond ((<= n 0) t)
;          ( t (format stream " ") (tab (- n 1) stream))))

;;; ======================================================================

(defun transpose (list)
  (cond ((every #'null list) nil)
	(t (cons (mapcar #'first list)
		 (transpose (mapcar #'rest list))))))

;;; (atranspose '((a b c) (c d e)))
;;; ((A . C) (B . D) (C . E))
;;; NOTE: must have at most two input lists (extra lists are ignored)
(defun atranspose (list)
  (cond ((every #'null list) nil)
	(t (cons (cons (first (first list)) (first (second list)))
		 (atranspose (mapcar #'rest list))))))

;;; ======================================================================

#|
;;; 22nd Aug: had to rewrite this. Checking the cadr is non-null doesn't
;;; reliably test there's a second element (eg. if the 2nd el is nil).
(defun singletonp (list) (and (proper-listp list) (= (length list) 1)))
; (defun    pairp (list) (and (proper-listp list) (= (length list) 2))) ; ; See below for more efficient implementation
(defun    triplep (list) (and (proper-listp list) (= (length list) 3)))
(defun quadruplep (list) (and (proper-listp list) (= (length list) 4)))
|#

;;; true for all lists except simple apairs '(a . b)
#+unused
(defun proper-listp (list)
  (and (listp list) (listp (rest list))))

;;; (apairp '(a . b)) -> t
;;; NOTE: (apairp '(a . (b))) -> NIL, because (a . (b)) = (a b). Thus there's some undefinedness as
;;; to whether '(a . (b)) is an apair or not.

(locally (declare (optimize (speed 3) (safety 0))) ; smh 2012-06-18

  (macrolet ((proper-listp (list)	; true for all lists except simple apairs '(a . b)
	       (let ((g (gensym)))
		 `(let ((,g ,list))
		    (and (consp ,g) (listp (rest ,g)))))))

    (defun singletonp (list) (and (proper-listp list) (eql (length (the cons list)) 1)))
    (defun    triplep (list) (and (proper-listp list) (eql (length (the cons list)) 3)))
    (defun quadruplep (list) (and (proper-listp list) (eql (length (the cons list)) 4)))

))					;locally

#|
(defun apairp (list)	OLD
  (declare (optimize (speed 3) (safety 0)))
  (and (listp list) list (not (listp (rest list)))))
|#
;;; NEW smh 2012-06-18
(defun apairp (list)
  (declare (optimize (speed 3) (safety 0)))
  (and (consp list) (not (listp (rest list)))))

; -----Original Message-----
;  From: Francis Leboutte [mailto:f.leboutte@algo.be]
; Sent: Thursday, June 26, 2008 8:41 AM
; Here is a version of the optimized pairp function that should work for any Lisp (I also get a bug with LispWorks 5.1):
; - the declaration is now correct.
; - the function works exactly like the original one.
;;; thing: should be anything but a dotted list
;;; return T if thing is 2 elements proper list (defun pairp (thing)
(defun pairp (thing)
  (declare (optimize (speed 3) (safety 0)))
  (and (consp thing)
       (let ((thing-cdr (cdr thing)))
         (and (consp thing-cdr)
	 (null (cdr thing-cdr))))))

#|
#+SBCL 	; Also see below for more efficient implementation of pairp
(defun pairp (list)(and (listp list) (= (length list) 2))) ; <- buggy, generates error for dotted pairs
;;; More efficient implementation from Sunil
;;; Tim Menzies: Causes problems under SBCL, so retain simpler version also above
#-SBCL
(defun pairp (list)
  (declare (optimize (speed 3) (safety 0))
	   (type list list))
  (and (listp list)
       list
       (let ((list (cdr list)))
	 (declare (type list list))
	 (and (listp list)
	      list
	      (null (cdr list))))))
|#
;;; ======================================================================

;;; (a) -> a
(defun delistify (list)
   (cond ((singletonp list)(car list))
	 (t list)))

(defun last-el (list) (car (last list)))

(defun last-but-one-el (list) (car (last (butlast list))))

;;; ======================================================================

;;; (quotep ''hi) --> t
(defun quotep (expr)
  (cond ((and (listp expr) (= (length expr) 2) (eq (car expr) 'quote)))))

;;; ======================================================================

;;; Preserve order of list
;;; (The basic Lisp function is set-difference)
(defun ordered-set-difference (list set &key (test #'eql))
  (cond ((null set) list)
	((not (intersection list set :test test)) list)
	(t (remove-if #'(lambda (el) (member el set :test test)) list))))

;(defun ordered-set-difference (list set &key (test #'eql))
;  (remove-if #'(lambda (el) (member el set :test test)) list))

;;; Preserve order of first list
(defun ordered-intersection (list set &key (test #'eql))
  (remove-if-not #'(lambda (el) (member el set :test test)) list))

;;; Returns the first element of set1 which is in set2, or nil otherwise.
(defun intersects (set1 set2)
  (first (some #'(lambda (el) (member el set2)) set1)))

;;; (intersections '((a b) (a) (c a b))) -> (a)
;;; (intersections '(("a" "b") ("a") ("c" "a" "b")) :test #'string=) -> ("a")
(defun intersections (list &key (test #'eql))
  (cond (list (reduce #'(lambda (x y) (intersection x y :test test)) list)))) ; better implementation!

;;; (nreplace '(a b c d e) 2 'new)  -> (a b new d e)
(defun nreplace (list n new)
  (cond ((endp list) nil)
	((= n 0) (cons new (rest list)))
	(t (cons (first list) (nreplace (rest list) (1- n) new)))))

;;; ======================================================================
;;;		DICTIONARY FUNCTIONS
;;; ======================================================================

;;; 6/5/11 - add :test argument

;;; Inefficient but non-destructive! Updated definition to preserve ordering as best possible
;;; KM> (gather-by-key '((a 1) (b 2) (a 3) (b 4))) -> ((a (1 3) (b (2 4))))
;;; KM> (gather-by-key '((a 1) (b 2) (a 3) (b 4) (c) (b))) -> ((a (1 3) (b (2 4))))
(defun gather-by-key (pairs &key dict (test #'equalp))
  (cond ((endp pairs) dict)
	(t (let* ((pair (first pairs))
		  (key (first pair))
		  (val (second pair))
		  (new-dict (cond (val (update-dict dict key val :test test))
				  (t dict))))
	     (gather-by-key (rest pairs) :dict new-dict :test test)))))

;;; Modified from KM's library: (gather-by-key '((a) (b))) -> NIL, (gather-by-key-inc-nils '((a) (b))) -> ((A) (B))
(defun gather-by-key-inc-nils (pairs &key dict (test #'equalp))
  (cond ((endp pairs) dict)
	(t (let* ((pair (first pairs))
		  (key (first pair))
		  (val (second pair))
		  (new-dict (cond (val (update-dict dict key val :test test))
				  ((assoc key dict :test test) dict)
				  (t `((,key) ,@dict)))))
	     (gather-by-key-inc-nils (rest pairs) :dict new-dict :test test)))))

(defun update-dict (dict key val &key (test #'equalp))
  (cond ((endp dict) `((,key (,val))))
	((apply test (list (first (first dict)) key))
	 `((,key (,@(second (first dict)) ,val)) ,@(rest dict)))
	(t (cons (first dict) (update-dict (rest dict) key val :test test)))))

;;; Inefficient but non-destructive!
;;; KM> (gather-by-akey '((a . 1) (b . 2) (a . 3) (b . 4)))
;;; ((b . (4 2)) (a . (3 1)))
(defun gather-by-akey (pairs &optional dict)
  (cond ((endp pairs) dict)
	(t (let* ((pair (first pairs))
		  (key (first pair))
		  (val (rest pair)))
	     (cond (val
		    (let ((vals (rest (assoc key dict :test #'equalp)))
			  (restdict (remove-if #'(lambda (pair) (equalp (first pair) key)) dict)) )
		      (gather-by-akey (rest pairs)
				      (cons (cons key (cons val vals)) restdict))))
		   (t (gather-by-akey (rest pairs) dict)))))))

;;; ----------
;;; Inefficient but non-destructive!
;;; [1c] USER(31): (gathers-by-key '((a 1 2) (b 3 4) (a 5 6)))
;;; ((a ((5 6) (1 2))) (b ((3 4))))
(defun gathers-by-key (tuples &key dict (test #'equalp))
  (cond ((endp tuples) dict)
	(t (let* ((tuple (first tuples))
		  (key (first tuple))
		  (val (rest tuple))
		  (vals (first (rest (assoc key dict :test test))))
		  (restdict (remove-if #'(lambda (tuple) (equalp (first tuple) key)) dict)))
	     (cond (val (gathers-by-key (rest tuples)
					:dict (cons (list key (cons val vals)) restdict)
					:test test))
		   (t (gathers-by-key (rest tuples)
				      :dict (cons (list key vals) restdict)
				      :test test)))))))

;;; (ordered-gather-by-key '((a 1) (a 2) (a 2) (b 4) (b 5))) -> ((A (1 2 2)) (B (4 5)))
;;; (ordered-gather-by-key '((a 1) (a 2) (a 2) (b 4) (b 5)) :remove-duplicates t) -> ((A (1 2)) (B (4 5)))
;;; NOTE Assumes ordered keys. If unordered, behavior is:
;;; (ordered-gather-by-key '((a 1) (a 2) (a 2) (b 4) (b 5) (a 1))) -> ((A (1 2 2)) (B (4 5)) (A (1)))
(defun ordered-gather-by-key (pairs &key remove-duplicates)
  (cond ((endp pairs) nil)
	(t (let ( (pair (first pairs)) )
	     (cond ((equalp (first pair) (first (second pairs)))	  ; (a 1) (a 2) (a 3) (b 1) ...
		    (let* ((gathered-rest (ordered-gather-by-key (rest pairs) 	; ((a (2 3)) (b ...) ...)
								  :remove-duplicates remove-duplicates))
			   (next-gathered-pair (first gathered-rest)) ) ; (a (2 3))
		      (cond ((and remove-duplicates (member (second pair) (second next-gathered-pair) :test #'equalp))
			     gathered-rest)
			    (t (cons (list (first next-gathered-pair) ; a
					   (cons (second pair) (second next-gathered-pair))) ; (cons 1 (2 3))
				     (rest gathered-rest)))))) ; ((b ...) ...)
		   (t (cons (list (first pair) (rest pair))		; (a b) -> (a (b))
			    (ordered-gather-by-key (rest pairs) :remove-duplicates remove-duplicates))))))))

;;; More space-efficient reimplementation
;;; (ordered-gathers-by-key '((a 1 x) (a 2 x) (a 2 x) (b 4 x) (b 5 x))) -> ((A ((1 X) (2 X) (2 X))) (B ((4 X) (5 X))))
;;; (ordered-gathers-by-key '((a) (b))) -> ((A (NIL)) (B (NIL)))
;;; ALSO: See large-ordered-gathers-by-key in AURA application (system/utils.lisp) for dealing with vast data using file i/o
(defun ordered-gathers-by-key (pairs &key remove-duplicates)
  (cond
   ((null pairs) nil)
   (t (let* ((pair (first pairs))
	     (key (first pair))
	     (data (rest pair)))
	(ordered-gathers-by-key0 (rest pairs) :current-key key :current-data (list data) :remove-duplicates remove-duplicates)))))

(defun ordered-gathers-by-key0 (pairs &key current-key current-data remove-duplicates)
  (cond ((endp pairs)
	 (list (list current-key (reverse current-data))))
	(t (let* ((pair (first pairs))
		  (key (first pair))
		  (data (rest pair)))
	     (cond
	      ((not (equal key current-key))
	       (cons (list current-key (reverse current-data))
		     (ordered-gathers-by-key0 (rest pairs) :current-key key :current-data (list data) :remove-duplicates remove-duplicates)))
	      ((and remove-duplicates (member data current-data :test #'equal))
	       (ordered-gathers-by-key0 (rest pairs) :current-key current-key :current-data current-data :remove-duplicates remove-duplicates))
	      (t (ordered-gathers-by-key0 (rest pairs) :current-key current-key :current-data (cons data current-data) :remove-duplicates remove-duplicates)))))))

(defun ordered-count (list)
  (count-elements list))

#|
;;; Use count-elements for more efficient implementation
;;; Takes an *ordered* list of items, and counts occurences of each one.
;;; (ordered-count '("a" "a" "b" "c")) -> (("a" 2) ("b" 1) ("c" 1))
(defun ordered-count (list)
  (cond ((null list) nil)
	(t (ordered-count0 list :target (first list) :n 1))))

(defun ordered-count0 (list &key target n)
  (cond ((endp list) `((,target ,n)))
	((equal (first list) target)
	 (ordered-count0 (rest list) :target target :n (1+ n)))
	(t `((,target ,n) ,@(ordered-count0 (rest list) :target (first list) :n 1)))))
|#
; Old version: Horribly space-inefficient!
;(defun ordered-count (list &optional counts-so-far)
;  (cond ((endp list) (reverse counts-so-far))
;	((equal (first list) (first (first counts-so-far)))
;	 (ordered-count (rest list) (cons (list (first list) (1+ (second (first counts-so-far))))
;					  (rest counts-so-far))))
;	(t (ordered-count (rest list) (cons (list (first list) 1) counts-so-far)))))

;;; ----------

(defun count-elements (list)
  (let ((hash-table (make-hash-table :test #'equal)))
    (mapc #'(lambda (entry)
	      (let ((old-entry (or (gethash entry hash-table) 0)))
		(setf (gethash entry hash-table) (1+ old-entry))))
	  list)
    (let ((results nil))
      (maphash #'(lambda (entry count)
		   (push (list entry count) results))
	       hash-table)
      results)))

#|
;;; Still horribly space inefficient
;;; (count-elements '(a b c b a)) -> ((C 1) (B 2) (A 2))
;;; [1] keep old counts in list to avoid updating the list, then remove out-of-date counts [2] later
(defun count-elements (list &optional counts)
  (cond ((endp list) (gather-counts counts))	 ; [2]
	(t (let* ((item (first list))
		  (count (or (second (assoc item counts :test #'equal)) 0)))
	     (count-elements (rest list) `((,item ,(1+ count)) ,@counts))))))	; [1]

;;; (GATHER-COUNTS ((A 2) (B 2) (C 1) (B 1) (A 1))) -> ((C 1) (B 2) (A 2))
(defun gather-counts (counts &optional done)
  (cond ((endp counts) done)
	((assoc (first (first counts)) done :test #'equal)
	 (gather-counts (rest counts) done))
	(t (gather-counts (rest counts) (cons (first counts) done)))))
|#

;;; ----------

;;; merge att-val lists, padding with null-values if no entry
;;; (combine-attvals '((a 1) (b 3)) '((a 2) (c 4))) -> ((A 2 1) (B 0 3) (C 4 0))
;;; (combine-attvals '((a 4) (b 3) (e 3)) '((A 2 1) (B 0 3) (C 4 0))) -> ((A 2 1 4) (B 0 3 3) (E 0 0 3) (C 4 0 0))
(defun combine-attvals (list dict &key (n-entries (1- (length (first dict)))) (null-entry '0))
  (cond ((endp list)
	 (mapcar #'(lambda (dictentry) (append dictentry `(,null-entry))) dict))
	(t (let* ((entry (first list))
		  (key (first entry))
		  (val (second entry))
		  (dictentry (assoc key dict)))
	     (cond (dictentry `((,@dictentry ,val)
				,@(combine-attvals (rest list)
						   (remove dictentry dict :test #'equal)
						   :n-entries n-entries :null-entry null-entry)))
		   (t `((,key ,@(duplicate null-entry n-entries) ,val)
			,@(combine-attvals (rest list) dict :n-entries n-entries :null-entry null-entry))))))))

;;; ----------

(defun number-eq (n1 n2 &key (tolerance 0.00001))
  (and (numberp n1)
       (numberp n2)
       (< (abs (- n1 n2)) tolerance)))

;;; handle rounding errors
;;; NOTE: Now should use zerop, with a numberp check first!
(defun zero (n)
  (and (numberp n)
       (<= n  0.0000001)
       (>= n -0.0000001)))

;;; Note: added parameter test to facilitate intersection of string lists. The defualt value eql corresponds to the common lisp default for intersection.
;;; Modified by Rahul Katragadda
(defun list-intersection (list &key (test 'user::eql))
  (format t "WARNING: The function (list-intersection ...) has been renamed (intersections ...). Please update your code!~%")
  (intersections list :test test))

;;; ----------

;;; (rank-sort list rank-function)
;;; rank-function generates a rank (a number) for each element in list, and then list is returned sorted,
;;; lowest rank first. This constrasts with Lisp's sort, where function is a *two* argument
;;; predicate for comparing two elements in list.
;;; rank-sort is non-destructive on list.
;;; CL-USER> (rank-sort '("cat" "the" "elephant" "a") #'length)
;;; ("a" "cat" "the" "elephant")
(defun rank-sort (list function)
  (mapcar #'second (assoc-sort (transpose (list (mapcar function list) list)))))

(defun assoc-sort (list) (sort list #'pair-less-than))

(defun pair-less-than (pair1 pair2) (< (first pair1) (first pair2)))

(defun symbol-less-than (pair1 pair2) (string< (symbol-name pair1) (symbol-name pair2)))

;;; ----------

(defvar *tmp-counter* 0)

(defun reset-trace-at-iteration () (setq *tmp-counter* 0))

(defun trace-at-iteration (n)
  (setq *tmp-counter* (1+ *tmp-counter*))
  (cond ((= (mod *tmp-counter* n) 0)
	 (format t "~a..." *tmp-counter*))))

(defun curr-iteration () *tmp-counter*)

;;; ======================================================================
;;;		       PROPERTY LISTS
;;; ======================================================================

;;; Remove *all* properties on the property list
(defun remprops (symbol)
  (mapc #'(lambda (indicator)
	    (remprop symbol indicator))
	(odd-elements (symbol-plist symbol))))

;;; (odd-elements '(1 2 3 4 5)) -> (1 3 5)
(defun odd-elements (list)
  (cond ((endp list) nil)
	(t (cons (first list) (odd-elements (rest (rest list)))))))

;;; (even-elements '(1 2 3 4 5)) -> (2 4)
(defun even-elements (list) (odd-elements (rest list)))

;;; ======================================================================

;;; (Could also define set-eq if I need it)
;;; CL-USER> (set-equal '("a" b) '(b "a")) -> t
;;; CL-USER> (set-equal '(a b) '(b a b))   -> nil
;(defun set-equal (set1 set2)
;  (cond ((and (endp set1) (endp set2)) t)
;	((member (first set1) set2 :test #'equal)
;	 (set-equal (rest set1) (remove (first set1) set2 :test #'equal :count 1)))))

;;; (set-equal '(a b) '(b a)) -> t
;;; (set-equal '("a" "b") '("b" "a")) -> t
;;; (set-equal '("a" "b") '("b" "a" "a")) -> t
(defun set-equal (set1 set2) (not (set-exclusive-or set1 set2 :test #'equal)))

(defun multiple-value-mapcar (function list)
  (cond ((endp list) nil)
	(t (multiple-value-bind
	    (x y)
	    (funcall function (first list))
	    (multiple-value-bind
	     (xs ys)
	     (multiple-value-mapcar function (rest list))
	     (values (cons x xs) (cons y ys)))))))

(defun unquote (expr)
  (cond ((quotep expr) (second expr))
	(t (format t "Warning! Unquote received an already unquoted expression!~%") expr)))

(defun quotify (item) (list 'quote item))

(defun bag-equal (bag1 bag2)
  (and (= (length bag1) (length bag2))
       (bag-equal0 bag1 bag2)))

(defun bag-equal0 (bag1 bag2)
  (cond ((equal bag1 bag2))
	((member (first bag1) bag2 :test #'equal)
	 (bag-equal0 (rest bag1) (remove (first bag1) bag2 :test #'equal :count 1)))))

;;; (bag-difference '(a b a d) '(d a)) -> (b a)
;;; If (bag-difference bag1 bag2) = nil, then all members of bag2 are in bag1 (with at least the same frequency)
(defun bag-difference (bag1 bag2 &key (test #'eql))
  (cond
   ((endp bag2) bag1)
   (t (bag-difference (remove (first bag2) bag1 :count 1 :test test) (rest bag2) :test test))))

;;; ----------

(defun update-assoc-list (assoc-list new-pair)
  (cond ((endp assoc-list) (list new-pair))
;	((string= (first (first assoc-list)) (first new-pair))
	((equal (first (first assoc-list)) (first new-pair))	; revised 12.16.99
	 (cons new-pair (rest assoc-list)))
	(t (cons (first assoc-list) (update-assoc-list (rest assoc-list) new-pair)))))

;;; Same, but matches with *second* argument
;;; (assoc 'a '((a b) (c e))) -> (a b)
;;; (inv-assoc 'b '((a b) (c e))) -> (a b)
;;; NOTE!! Common Lisp rassoc might be a better choice, doing the same thing but with dotted pairs
;;; (rassoc 'b '((a . b) (c . e))) -> (a . b)
(defun inv-assoc (key assoc-list &key (test #'eql))
  (cond ((endp assoc-list) nil)
	((apply test (list (second (first assoc-list)) key)) (first assoc-list))
	(t (inv-assoc key (rest assoc-list) :test test))))

;;; ----------

;;; removes ALL the assoc-list entries with key.
(defun remove-assoc-entry (key assoc-list)
  (remove-if #'(lambda (entry) (eql (first entry) key)) assoc-list))

;;; ----------

;;; (insert-delimeter '(a b c) 'cat) -> (a cat b cat c)
(defun insert-delimeter (list delimeter)
  (cond ((endp list) list)
	((singletonp list) list)
	((cons (first list) (cons delimeter (insert-delimeter (rest list) delimeter))))))

;;; ----------

;;; Returns non-nil if expr contains (at least) one of symbols.
;;; (contains-some '(a b (c d)) '(d e))  -> true
(defun contains-some (expr symbols)
  (or (member expr symbols)
      (and (listp expr)
	   (some #'(lambda (el) (contains-some el symbols)) expr))))

;;; ----------

#|
xor clashes with CLISP
NOTE:: These have different side-effects to Lisp's or macro: Here ALL the arguments are evaluated THEN the results tested.
  - (nor (setq *w* t) (setq *z* t)) and (not (or (setq *w* t) (setq *z* t))) both return NIL,
    BUT the nor will setq *z* t, while (not (or...)) will not.
|#
(defun x-or (a b) (and (or a b) (not (and a b))))
(defun nor (a b) (not (or a b)))	; = (and (not a) (not b))

;;; ----------

;;; USER(60): (subbagp '(1 2 2) '(1 2 2 3)) -> t
;;; USER(61): (subbagp '(1 2 2 2) '(1 2 2 3)) -> NIL
(defun subbagp (subbag bag &key (test #'eql))
  (cond
   ((null subbag))
   ((member (first subbag) bag :test test)
    (subbagp (rest subbag) (remove (first subbag) bag :test test :count 1)))))

;;; ----------
;;; RETURNS THREE VALUES: shorterlist1 shorterlist2 shared
;;; USER(63): (remove-shared-elements '(1 2 1 2 3) '(1 2 3 4 5))
;;; (1 2)
;;; (4 5)
;;; (1 2 3)
;;; USER(64): (remove-shared-elements '(1 2 1 2 1 3) '(1 2 3 1 4 5))
;;; (2 1)
;;; (4 5)
;;; (1 2 1 3)
(defun remove-shared-elements (list1 list2 &key (test #'eql))
  (cond ((null list1) (values nil list2 nil))
	((member (first list1) list2 :test test)
	 (multiple-value-bind
	  (shorterlist1 shorterlist2 shared)
	  (remove-shared-elements (rest list1) (remove (first list1) list2 :test test :count 1))
	  (values shorterlist1 shorterlist2 (cons (first list1) shared))))
	(t (multiple-value-bind
	    (shorterlist1 shorterlist2 shared)
	    (remove-shared-elements (rest list1) list2)
	    (values (cons (first list1) shorterlist1) shorterlist2 shared)))))

;;; Remove element number n (first position = 0)
;;; USER(58): (remove-element-n '(a b c) 1) -> (A C)
(defun remove-element-n (list n)
  (cond ((or (null list) (< n 0)) list)
	((= n 0) (rest list))
	(t (cons (first list) (remove-element-n (rest list) (1- n))))))

;;; ----------------------------------------------------------------------

;;; Move symbols from one package to another. Fairly crude implementation!
;;; e.g. (port-to-package ... :old-package :sapir :new-package :user)
;;; REVISED: Dec 2003 - don't care what the old package was
(defun port-to-package (tree &key package)
  (cond
   ((null tree) nil)
   ((listp tree) (cons (port-to-package (first tree) :package package)
		       (port-to-package (rest tree) :package package)))
   ((symbolp tree)
    (intern (symbol-name tree) package))
   (t tree)))

;;; ======================================================================

;;; CL-USER(30): (permute '((a b) (1 2) (X Y)))
;;; ((A 1 X) (A 1 Y) (A 2 X) (A 2 Y) (B 1 X) (B 1 Y) (B 2 X) (B 2 Y))
(defun permute (list-of-lists)
  (cond
   ((endp list-of-lists) (list nil))
   (t (let ( (permutes (permute (rest list-of-lists))) )
	(mapcan #'(lambda (e)
		    (mapcar #'(lambda (permute)
				(cons e permute))
			    permutes))
		(first list-of-lists))))))


;;; (all-pairs '(a b c d))
;;; ((A B) (A C) (A D) (B C) (B D) (C D))
(defun all-pairs (list)
  (cond ((endp list) nil)
	(t (append
	    (mapcar #'(lambda (e)
			(list (first list) e))
		    (rest list))
	    (all-pairs (rest list))))))

;;; (all-adjacent-pairs '(a b c d e f)) -> ((a b) (b c) (c d) (d e) (e f))
(defun all-adjacent-pairs (list)
  (cond ((endp list) nil)
	((singletonp list) nil)
	(t `((,(first list) ,(second list)) ,@(all-adjacent-pairs (rest list))))))

;;; (first-n '(a b c) 2) -> (a b)
(defun first-n (list n) (cond ((> (length list) n) (subseq list 0 n)) (t list)))

;;; (is-subset-of '(a b) '(a b c)) -> t
(defun is-subset-of (list1 list2 &key (test #'eql))
  (not (set-difference list1 list2 :test test)))

;; (replace-element 2 '(a b c) 'x) -> (A X C)
;; (replace-element 4 '(a b c) 'x) -> (A B C X)
;; (replace-element 5 '(a b c) 'x) -> (A B C NIL X)
(defun replace-element (n list el)
  (cond ((endp list)
	 (append (duplicate nil (1- n)) (list el)))
	((= n 1) (cons el (rest list)))
	(t (cons (first list) (replace-element (1- n) (rest list) el)))))

;(defun numeric-char-p (char) (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9) :test #'char=))
(defun numeric-char-p (char)
  (format t "WARNING: Call to numeric-char-p should be replaced by call to built-in digit-char-p; please update your code! Continuing for now...~%")
  (digit-char-p char))

;;; (permutations '(a b c)) -> ((A B C) (A C B) (B A C) (B C A) (C A B) (C B A))
;;; (permutations '(a b a)) -> ((B A) (A B))
(defun permutations (list)
  (permutations0 (remove-duplicates list :test #'equal)))

(defun permutations0 (list)
  (cond ((endp list) nil)
	((singletonp list) (list list))
	(t (mapcan #'(lambda (element)
		       (mapcar #'(lambda (permutation)
				   (cons element permutation))
			       (permutations0 (remove element list :test #'equal))))
		   list))))

;;; ======================================================================

;;; Utilities for handling binding alists
;;; Really these should be defconstants, but for some reason defconstant causes an error under
;;; SBCL (Tim Menzies, March 2008), so replace with defvar.
(defvar *null-binding* '(t . t))	; note, not NIL, so we can distinguish no bindings from failure
(defvar *null-bindings* '((t . t)))

(defun combine-bindings (bindings1 bindings2)
   (or (remove *null-binding* (remove-duplicates (append bindings1 bindings2) :test #'equal :from-end t) :test #'equal)
       *null-bindings*))		; if bindings1 AND bindings2 are all *null-bindings*)

(defun add-binding (x y bindings)
  (cond ((eql x y) bindings)
	((member `(,x . ,y) bindings :test #'equal) bindings)
	(t (combine-bindings bindings (list (bind x y))))))

(defun val-of (var bindings) (rest (assoc var bindings)))

(defun bind (x y) `(,x . ,y))

(defun var-boundp (var bindings) (assoc var bindings))

;;; (remove-singletons '(a b c b a b b)) -> (a b)
(defun remove-singletons (list) (remove-if #'(lambda (x) (uniquep x list)) (remove-duplicates list)))

(defun uniquep (x list) (not (member x (remove x list :count 1))))

; (areverse '(a . b)) -> (b . a)
(defun areverse (a-dot-b) `(,(rest a-dot-b) . ,(first a-dot-b)))

;;; (counts-to 3) -> (1 2 3)
;;; Note: keyword is :start-at, not :start, as symbol start conflicts with net.aserve :-(
(defun counts-to (nmax &key (start-at 1)) (counts-to0 start-at nmax))
(defun counts-to0 (n nmax)
  (cond ((> n nmax) nil)
	(t (cons n (counts-to0 (1+ n) nmax)))))

;;; (break-list <list> :test <test>)
;;; Break <list> into sublists, breaking at (and removing) each element that passes <test>
;;; RETURNS: A list of sublists.
;;; NOTE: If the first element passes <test>, then the first sublist will be NIL
;;; (break-list '("http" "a" "b" "http" "c" "d")
;;;			:test #'(lambda (line) (starts-with (trim-whitespace line) "http"))))))
;;;  -> '(nil ("a" "b") ("c" "d"))
(defun break-list (list &key test)
  (let ((element (first list)))
    (cond ((endp list) nil)
	  ((apply test (list element))
	   (cons nil (break-list (rest list) :test test)))	; nil becomes the terminator of the prev para
	  (t (let ((sublists (break-list (rest list) :test test)))
	       `((,element ,@(first sublists)) ,@(rest sublists)))))))

;;; ======================================================================

#+unused
(defun recons (x car cdr)		; smh 2012-06-19
  (if (or (not (eq (car x) car))
	  (not (eq (cdr x) cdr)))
      (cons car cdr)
    x))

(defun sublis* (alist tree &key (test #'eql))
  ;; A faster, less capable version of subst, when alist might be long. smh 2012-06-19
  ;; Caution: alist cannot contain any keys or vals that are nil, or dup keys
  (declare (optimize (speed 3) (safety 0)))
  (if (loop for x on alist
	  repeat 12			; guesstimate
	  finally (when x (return t)))
      ;; A long alist, so use ht version.
      (let ((ht (make-hash-table :test test)))
	(loop for (k . v) in alist
	    when k do (setf (gethash k ht) v))
	(labels ((s (s)
		   (or (gethash s ht)
		       (if (consp s)
			   (let* ((oa (car s))
				  (od (cdr s))
				  (na (s oa))
				  (nd (s od)))
			     (if (and (eq oa na)
				      (eq od nd))
				 s
			       (cons na nd)))
			 s))))
	  (s tree)))
    ;; Short alist, defer to the usual way.
    (sublis alist tree :test test)))
