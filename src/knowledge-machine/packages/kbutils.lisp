
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: kbutils.lisp
;;; Author: Peter Clark
;;; Date: Separated out Mar 1995
;;; Purpose: Basic utilities for KM

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

;;; ======================================================================
;;; 		RECOGNITION OF INSTANCES
;;; ======================================================================

(defun km-null (km-nil)
  (or (null km-nil) (eq km-nil '#$nil)))

;;; Only recognizes slots whose immediate class is Slot. I don't use this, the
;;; second is better.
(defun simple-slotp (slot)
  (and (symbolp slot)
       (member slot (get-vals '#$Slot '#$instances :situation *global-situation*))))

;;; (instance-of x '#$Slot) would climb up the whole taxonomy from x. I think I used the method
;;; below instead as it's more efficient to work down from Slot, given Slot typically has only one or two subclasses.
(defun slotp (slot)
  (and (symbolp slot)
       (or (intersection (cons '#$Slot (all-subclasses '#$Slot))
			 (get-vals slot '#$instance-of :situation *global-situation*))
	   (built-in-slot slot))))

;;; Check is' a valid slot
(defun slot-objectp (slot) (and (symbolp slot) (not (null slot))))

;;; Rather crude approximation of a test...
(defun pathp (path) (listp path))

;;; Anything which is considered to be fully evaluated in KM.
;;; EXCEPT it ALSO includes constraints. Argh!
;;; 345, "a", pete, #'print, '(every Dog), (:triple Sue loves John), (<> 23)
(defun is-km-term (concept)
  (or (atom concept)		; includes: 1 'a "12" nil
      (descriptionp concept)
      (quoted-expressionp concept)
      (km-structured-list-valp concept)
      (km-setp concept)
      (functionp concept)
      (constraint-exprp concept)))

(defun is-simple-km-term (concept)
  (or (and (atom concept)		; includes: 1 'a "12" nil
	   (not (member concept *reserved-keywords*)))
      (descriptionp concept)
      (functionp concept)))

;;; Anything which is considered to be fully evaluated in KM.
;;; Eventually, should get rid of is-km-term above
(defun fully-evaluatedp (concept &key in-structured-exprp)
  (or (and (atom concept) (neq concept '*))		; includes: 1 'a "12" nil
      (and (quoted-expressionp concept)
	   (not (recursive-find 'unquote concept)))
      (the-class-exprp concept)				; (the-class ...)
      (and (km-setp concept)				; (:seq (:set 1 2)) is fully evaluated!
	   in-structured-exprp				; (:seq (:set (:set 1 2) 3)) is not!
	   (every #'(lambda (el) (fully-evaluatedp el :in-structured-exprp nil)) (val-to-vals concept)))
      (and (km-structured-list-valp concept)
	   (every #'(lambda (el) (fully-evaluatedp el :in-structured-exprp t)) (seq-to-list concept)))))
; No!!! if a function and/or constraint has been fully evaluated, then it will be NIL!
;      (functionp concept)
;      (constraint-exprp concept)))

;; Proves that it's *definitely* a class; however, some other objects may also
;; be classes too (eg. if they haven't been declared).
;;; [1] This is optional, and here purely for efficiency. If we do find instance-of link, then it isn't
;;;     a class [ignoring metaclasses for now], so we don't need to bother doing the tests for classp.
;;;	If we don't find one, or we miss one because instance-of is a fluent and we don't look for
;;;     situation-specific instance-of links, then that's okay, we just proceed on anyway to do the class
;;;     tests. Non-classes will fail these tests.
(defun classp (class)
  (or (member class *built-in-classes*)
      (and (kb-objectp class)
	   (or (get-vals class '#$superclasses)
	       (and (not (get-vals class '#$instance-of))
		    (or (get-vals class '#$instances)
			(get class 'member-properties)
			(get class 'member-definition)
			(get-vals class '#$subclasses)))))))


;;; Proves (just about) it's definitely an instance, though there may
;;; be other instances which fail this test.
(defun is-an-instance (instance)
  (or (anonymous-instancep instance)
      (numberp instance)
      (stringp instance)
      (functionp instance)
      (descriptionp instance)
      (km-structured-list-valp instance)
      (and ; (is-km-term instance) bug!
           (kb-objectp instance)
	   (or (get-vals instance '#$instance-of :facet 'own-properties)
	       (get-vals instance '#$instance-of :facet 'own-definition)))))
;; Time consuming!
;	   (not (classp instance)))))   ; just in case #$instance-of is a class-metaclass relation

;;; No taxonomic info declared, but IS some other info declared
(defun orphanp (concept)
  (and (kb-objectp concept)
       (not (get-vals concept '#$superclasses))
       (not (get-vals concept '#$subclasses))
       (not (get-vals concept '#$instances))
       (not (get-vals concept '#$instance-of))
; No, these won't put the thing in the taxonomy - the slots are for indexing purposes only
;      (not (get-vals concept '#$instance-of :facet 'member-definition))
;      (not (get-vals concept '#$instance-of :facet 'own-definition))
       (not (built-in-concept concept))))

;;; _car12
(defun anonymous-instancep (instance0)
  (let ( (instance (dereference instance0)) )
    (and (symbolp instance)
	 (char= (first-char (symbol-name instance)) *var-marker-char*))))

;;; This function's really badly named, as it really means not an instance. Will phase this out.
;;; *pete, 32, "234", #'print
(defun named-instancep (instance) (not (anonymous-instancep instance)))

;;; Not used any more
(defun fluent-instancep (instance) (declare (ignore instance)) nil)
;(defun fluent-instancep (instance)
;  (and (symbolp instance)
;       (starts-with (symbol-name instance) *fluent-instance-marker-string*)))

; Not used any more
;(defun remove-fluent-instances (instances) (remove-if #'fluent-instancep instances))

;;; (recursive-remove-fluent-instances '#$((_SomePerson813) && ((some Person))))
;;; -> ((nil) && ((|some| |Person|)))
;;; Dec00 Revised to be -> (() && ((|some| |Person|))) - yikes, but becomes (&& ((some Person)))!
;;; Patched Jan01 - we simply splice out these things.
;;; BUT still a bug: (_Some23 & (a Car)) -> (& (a Car)), but should be just (a Car). Need to be more sophisticated.
;;; Fixed Feb01
;;; Apr02: Still bug: (:args nil _Car1) -> (:args _Car1)
;(defun recursive-remove-fluent-instances (instances)
;  (cond ((&-exprp instances)
;	 (vals-to-&-expr (recursive-remove-fluent-instances (&-expr-to-vals instances))))
;	((&&-exprp instances)
;	 (vals-to-val (valsets-to-&&-exprs (recursive-remove-fluent-instances (&&-exprs-to-valsets (val-to-vals instances))))))
;	((listp instances)
;	 (remove nil (mapcar #'recursive-remove-fluent-instances instances)))
;	((fluent-instancep instances) nil)
;	(t instances)))

;;; Objects which will have frames in the KB about them, e.g., *Pete, _Car12
;; Rewrite by Carl Shapiro:
;; An optimized KB-OBJECTP definition.  Profiling has shown that the
;; out-of-line call to MEMBER is a huge performance drain on this
;; frequently invoked predicate.  Since the list of test subjects is
;; small, we can inline the comparisons by rewriting MEMBER in terms
;; of CASE.
(defun kb-objectp (instance)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))	; optimization from Francis Leboutte
  (and instance
       (symbolp instance)
       (not (user-commentp instance))
;OLD   (not (member instance '#$(nil NIL :seq :bag :args :triple :pair :function)))))	; later: allow stuff on 't'!
       (case instance
	 (#$(nil :set :seq :bag :args :triple :pair :function :incomplete) nil) ; later: allow stuff on 't'!
	 (t t))))

;;; A *structured value* is a CONTAINER of values, collected together. It *doesn't*
;;; include quoted expressions.
;;; NOTE a SET isn't a structured value, it's a set of values!!
(defun km-structured-list-valp (val)
  (and (listp val) (member (first val) *structured-list-val-keywords*))) ; defined in interpreter.lisp

(defun km-functionp (val) (and (listp val) (eq (first val) '#$:function)))

(defun km-triplep (triple)
  (and (listp triple) (eq (first triple) #$:triple) (= (length (desource+decomment triple)) 4)))

;;; recognize sequences eg. (:seq a b c)
(defun km-seqp (seq)  (and (listp seq) (eq (first seq) '#$:seq)))
(defun km-bagp (bag)  (and (listp bag) (eq (first bag) '#$:bag)))
(defun km-pairp (seq) (and (listp seq) (eq (first seq) '#$:pair)))
(defun km-setp (expr) (and (listp expr) (eq (first expr) '#$:set)))

;;; '(:seq a b) -> (a b)
(defun bag-to-list (bag) (rest bag))
(defun seq-to-list (seq) (rest seq))
(defun set-to-list (set) (rest set))
(defun pair-to-list (pair) (rest pair))

;;; ----------
;;; NOTE: doesn't remove dups
;;; Input: a LIST of values. Returns a LIST of values.
;;; NOTE: (flatten-sets '((:set a b))) is OK
;;; 	  (flatten-sets '(a b)) is OK
;;;       (flatten-sets '(:set a b)) is NOT OK
;;;       (flatten-sets 'b) is NOT OK
;;; (flatten-sets '#$((:set a b (:set c (:set d e)) f (:set g h)))) -> (a b c d e f g h)
(defun flatten-sets (vals)
  (my-mapcan #'flatten-set vals))

;;; Given a SINGLE value, which might be a set, return either
;;;	(1) a singleton list of that one value, if that value is NOT a set.
;;;	(2) a list of the values in that set, if that value IS a set.
(defun flatten-set (set)
  (cond ((km-setp set) (my-mapcan #'flatten-set (set-to-list set)))
	(t (list set))))

;;; ----------

;;; (km-varp ?x) -> t
(defun km-varp (var)
  (and (symbolp var)
       (char= (first-char (symbol-name var)) #\?)))

;;; e.g. (a Cat called "fido")
(defun km-tagp (tag)
  (or (and (atom tag) (not (null tag)))
      (constraint-exprp tag)
      (and (km-setp tag) (every #'km-tagp (set-to-list tag)))))

;;; Optimized version from Francis Leboutte
;;; (defun km-argsp (args) (and (listp args) (eq (first args) '#$:args)))
(defun km-argsp (args)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (and (listp args)
       (eq (first args) '#$:args)))

(defun km-defaultp (expr)
  (and (listp expr) (eq (first expr) '#$:default)))

;;; ----------------------------------------

(defun comparison-operator (slot)
  (or (member slot *inequality-relations*)
      (member slot *equality-relations*)
      (assoc slot *user-defined-infix-operators*)))

;;; ----------------------------------------

(defun &-exprp (expr) (and (listp expr) (member (second expr) '(& &! &+ ==))))	; but not &? &+?
(defun &&-exprp (expr) (and (listp expr) (member (second expr) '(&& &&! ===))))

;;; ----------------------------------------

;;; Accessing (:args ...) structures:
;(defun arg1of (arg-structure) (second arg-structure))		; (:args a b) -> a
(defun arg1of (arg-structure)	; optimized by Francis Leboutte
  (declare (type list arg-structure))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (second arg-structure))

(defun arg2of (arg-structure) (third arg-structure))		; (:args a b) -> b
(defun arg3of (arg-structure) (fourth arg-structure))
(defun arg4of (arg-structure) (fifth arg-structure))

;;; [1] NOTE: avoids numeric and set testing
;;; 7/28/04: At some risk, replaced remove-duplicates with (destructive) delete-duplicates (which is 50% faster).
;;; This change relies on the fact that (dereference ...) will create a copy of instances, which is necessarily a list.
;;; 1/30/07: Need to modify to check dereference is actually applied, and if not copy the list.
;(defun remove-dup-instances (instances)
;  (delete-duplicates (dereference instances) :test #'km-equal :from-end t))
#-allegro
(defun remove-dup-instances (instances)
  (let ((copied-dereferenced-instances (cond ((needs-dereferencing instances) (dereference0 instances))
					     (t (copy-tree instances)))))
    (delete-duplicates copied-dereferenced-instances :test #'km-equal :from-end t)))

#+allegro					;smh 2012-07-10
(defun remove-dup-instances (instances)
  (let ((copied-dereferenced-instances (cond ((needs-dereferencing instances) (dereference0 instances))
					     (t (copy-tree instances)))))
    ;; This was an O^2 time hog, so use the hashtable version.  XXX Should write a delete-duplicates-from-end
    ;; to avoid the additional consing.
    (locally				;(declare (optimize (speed 3) (safety 0)))
      (if (and (loop for x on copied-dereferenced-instances
		   repeat 20
		   finally (when x (return t)))
	       (every #'symbolp copied-dereferenced-instances))
	  ;; An eq ht will suffice,
	  (loop with ht = (make-hash-table :test #'eq :values nil)
	      for x in copied-dereferenced-instances
	      if (null x)
	      unless (gethash '#$nil ht)
	      collect x and do (excl:puthash-key '#$nil ht)
	      end
	      else unless (gethash x ht)
	      collect x
	      and do (excl:puthash-key x ht))
	;; Fall back to km-equal.
	(delete-duplicates copied-dereferenced-instances :test #'km-equal :from-end t)))))

#|
7/28/04 - playing with fire!! Let's not do this.
;;; delete-duplicates is twice as fast as remove-duplicates.
;;; It relies on the fact that (dereference ...) will create a copy of instances, which is necessarily a list... dangerous!!
(defun remove-dup-atomic-instances (instances)
 (delete-duplicates (dereference instances) :test #'km-equal :from-end t))
|#
(defun remove-dup-atomic-instances (instances) (remove-dup-instances instances))

;;; ======================================================================
;;;		DEFINITION OF EQUALITY
;;; ======================================================================

;;; "equal" isn't quite what we want, as we *don't* remove duplicate numeric entries. Is this a bad idea??
;;; yes, use a bag if you want duplicate numbers
;;; I suspect in other places in the code, duplicate numbers are removed as I've used equal not km-equal (eg. during lazy unify).
;;; This compares SINGLE VALUES. Note: We DON'T expect to be given the test (:set 1) = 1,  (:set (:seq 1)) = (:seq 1)
;(defun km-equal (i1 i2)
;  (and (equal i1 i2) (not (numberp i1)) (not (existential-exprp i1))))
;  (and (equal i1 i2) (not (existential-exprp i1))))

;;; ----------------------------------------
#|
[1] TOLERANCE:
Desired behavior:
 0.00001 /= 0.00002
 4.99999  = 5.00000
 499999  /= 500000

For large numbers, it is absolute, i.e., +/- 0.0001.
For small numbers, it is fractional, i.e., +/- 0.01%
Behavior: x = y if x = y +/- (0.0001 or 0.01% of max(x,y), whichever is smaller)
|#
;; Rewrite by Carl Shapiro:
;; An optimized KM-EQUAL definition.  The comparisons against atomic
;; types now occupy the beginning of the COND clause.  This saves us
;; the out-of-line call to EQUAL and its expensive general equality
;; test.  Profiling has shown that most comparisons are done against
;; variables of an atomic type (symbols, mostly).  The added cost of
;; explicity codifying the EQ tests done interally by EQUAL should be
;; lost in the noise during aggregate (list) comparisons.
;; [2] 11/1/04 - moved [2] up, as (km-equal NIL NIL) was incorrectly failing
;; [3] we short-circuit the call to the compound structure tests.
;;     Thanks to Sunil Mishra for this!
(defun km-equal (i1 i2)
  (declare (optimize (safety 1) (speed 3)))
  (cond ;; Fast, atomic type comparisons are done first.
	((eq i1 i2))   				; [2]
	((null i1) (eq i2 '#$nil))
	((null i2) (eq i1 '#$nil))
;	((or (symbolp i1) (symbolp i2)) (eq i1 i2))	; [2]
	((or (symbolp i1) (symbolp i2)) nil) ; [3]
	((and (numberp i1) (numberp i2) *tolerance*)
	 (<= (abs (- i1 i2)) (min *tolerance*
				  (* (max (abs i1) (abs i2)) *tolerance*))))	; [1]
	((or (numberp i1) (numberp i2)) nil) ; [3]
	((and (equal i1 i2)
	      (not (existential-exprp i1))
	      (not (km-structured-list-valp i1))))  ; (:pair (a Move) 1) (:pair (a Move) 1) are NOT equal
	((or (atom i1) (atom i2)) nil) ; [3]
	((and (km-setp i1) (km-setp i2)) (km-set-equal i1 i2))
	((and (km-bagp i1) (km-bagp i2)) (km-bag-equal i1 i2))
	((and (km-argsp i1) (km-argsp i2)) (km-seq-equal i1 i2))
	((and (km-seqp i1) (km-seqp i2)) (km-seq-equal i1 i2))
	((and (km-pairp i1) (km-pairp i2)) (km-seq-equal i1 i2))
	((and (km-triplep i1) (km-triplep i2)) (km-seq-equal i1 i2))))


; OLD  VERSION
;(defun km-equal (i1 i2)
;  (cond ;; Fast, atomic type comparisons are done first.
;	((eq i1 i2))   				; [2]
;	((null i1) (eq i2 '#$nil))
;	((null i2) (eq i1 '#$nil))
;	((and (numberp i1) (numberp i2) *tolerance*)
;	 (<= (abs (- i1 i2)) (min *tolerance*
;				  (* (max (abs i1) (abs i2)) *tolerance*))))	; [1]
	;; The slow, aggregate type comparisons follow.
;	((and (equal i1 i2) (not (existential-exprp i1))))
;	((and (km-setp i1) (km-setp i2)) (km-set-equal i1 i2))
;	((and (km-bagp i1) (km-bagp i2)) (km-bag-equal i1 i2))
;	((and (km-seqp i1) (km-seqp i2)) (km-seq-equal i1 i2))
;	((and (km-pairp i1) (km-pairp i2)) (km-seq-equal i1 i2))))

(defun km-set-equal (set1 set2) (not (set-exclusive-or set1 set2 :test #'km-equal)))

;;; ----------

(defun km-bag-equal (bag1 bag2)
  (and (= (length bag1) (length bag2))
       (km-bag-equal0 bag1 bag2)))

(defun km-bag-equal0 (bag1 bag2)
  (cond ((equal bag1 bag2))				; equal is subset of km-equal
	((member (first bag1) bag2 :test #'km-equal)
	 (km-bag-equal0 (rest bag1) (remove (first bag1) bag2 :test #'km-equal :count 1)))))

;;; ----------

(defun km-seq-equal (seq1 seq2)
  (and (= (length seq1) (length seq2))
       (km-seq-equal0 seq1 seq2)))

(defun km-seq-equal0 (seq1 seq2)
  (cond ((and (null seq1) (null seq2)))		; NOTE: (a Move) (a Move) are NOT equal
	((and (km-equal (first seq1) (first seq2))
	      (km-seq-equal0 (rest seq1) (rest seq2))))))

;;; ======================================================================

; Old def -- definition??
;(defun km-equal (i1 i2)
;  (and (equal i1 i2)
;       (or (symbolp i1)		; (kb-objectp i1)	ERROR! should remove dups for non-kb-objects t f!
;	   (km-structured-list-valp i1))))

;;; Only expressions of the form (a ... [with ...]) return a situation-invariant answer.
;;; This is used to block passing these *expressions* between situations, to avoid redundant computation
;;;     of identities. The result of their evaluation *will* be passed between situations, still, of course.
(defun situation-invariant-exprp (expr)
  (and (listp expr) (eq (first expr) '#$a)))

(defun constraint-exprp (expr)
  (or (val-constraint-exprp expr)
      (set-constraint-exprp expr)))

(defun retain-exprp (expr) (and (listp expr) (eq (first expr) '#$retain-expr)))

(defun non-constraint-exprp (expr) (not (constraint-exprp expr)))

(defun val-constraint-exprp (expr)
  (and (listp expr)
       (member (first expr) *val-constraint-keywords*)))

(defun set-constraint-exprp (expr)
  (or (eq expr '#$:incomplete)
      (and (listp expr)
	   (member (first expr) *set-constraint-keywords*))))

(defun km-boolean-exprp (expr)
  (and (listp expr)
       (or (member (first expr) '#$(is-true all-true some-true theoneof theoneof2 exists has-value))
	   (member (second expr) '#$(&? &+? = /= > < >= <= and or not numberp is-subsumed-by subsumes
					covers isa is includes is-superset-of))
	   (member (third expr) '#$(must))
	   (member (fifth expr) '#$(must)))))

;;; Experimental
(defun sometimes-exprp (expr)
  (and (listp expr) (eq (first expr) '#$sometimes)))

;;; Returns non-nil if expr contains (at least) one of symbols.
(defun contains-some-existential-exprs (exprs)
  (contains-some exprs '#$(a an some)))

;(defun existential-exprp (expr)
;  (and (listp expr) (member (first expr) '#$(a some))))

;;; NB "an" is NOT considered an existential structure, it needs preprocessing by the interpreter.
(defun existential-exprp (expr)
  (and (listp expr)
       (or (member (first expr) '#$(a some))
	   (and (comment-tagp (first expr)) 		; allow ([Car1] a Big Engine)
		(existential-exprp (rest expr))))))

;;; (some <x>)
(defun fluent-instance-exprp (expr)
  (and (listp expr) (eq (first expr) '#$some)))

;;; ======================================================================

(defun val-to-vals (val)
  (cond ((null val) nil)
	((eq val '#$nil) nil)
	((km-setp val) (set-to-list val))
	(t (list val))))  ; val must be an atom (eg. _Car23) or a single expression, eg. (a Car)
			  ; so we simply wrap it in a list (_Car23), or ((a Car))

(defun vals-to-val (vals)
  (cond ((null vals) nil)
	((singletonp vals) (first vals))
	((listp vals) (cons '#$:set vals))
	(t (report-error 'user-error "Expecting a set of values, but just found a single value ~a!~%" vals))))

;;; ======================================================================
;;; 		val-sets-to-expr
;;; ======================================================================
;;;     GIVEN a LIST of SETS of VALS (ie. some val-sets)
;;;     RETURNS a *SINGLE* expression which KM can evaluate, denoting the combination.
;;; single-valuedp = *:   (val-sets-to-expr '((a)) ) -> a
;;; single-valuedp = *:   (val-sets-to-expr '((a b)) ) -> (:set a b)
;;; single-valuedp = T:   (val-sets-to-expr '((a) (b) (c)) :single-valuedp t)  -> (a & b & c)
;;; single-valuedp = T:   (val-sets-to-expr '((a b) (c)) :single-valuedp t) -> ERROR! and (a & c)
;;; single-valuedp = NIL: (val-sets-to-expr '((a b) (b) (c d))) -> ((a b) && (b) && (c d))
;;; combine-values-by-appendingp = T: (val-sets-to-expr '((a b) (b) (c d))) -> (:set a b c d)
(defun val-sets-to-expr (exprs0 &key single-valuedp combine-values-by-appendingp
				     (joiner (cond (single-valuedp '&) (t '&&))))
  (let* ((exprs1 (remove-duplicates (remove nil exprs0) :test #'equal :from-end t))
	 (exprs (cond ((some #'(lambda (x)
				 (cond ((not (listp x))
					(report-error 'user-error "val-sets-to-expr: Single value ~a found where list of values expected! Listifying it...~%" x) t)))
			     exprs1)
		       (mapcar #'listify exprs1))
		      (t exprs1))))
    (cond ((null exprs) nil)
	  ((singletonp exprs) (vals-to-val (first exprs)))
	  (combine-values-by-appendingp (vals-to-val (remove-dup-instances (append-lists exprs))))
	  (t (val-sets-to-expr0 exprs :single-valuedp single-valuedp :joiner joiner)))))

(defun val-sets-to-expr0 (exprs &key single-valuedp (joiner (cond (single-valuedp '&) (t '&&))))
  (cond
   ((endp exprs) nil)
   ((null (first exprs)) (val-sets-to-expr0 (rest exprs) :single-valuedp single-valuedp :joiner joiner))
; Now tested earlier in val-sets-to-expr
;   ((not (listp (first exprs)))
;    (report-error 'user-error "val-sets-to-expr0: Single value ~a found where list of values expected! Listifying it...~%" (first exprs))
;    (val-sets-to-expr0 (cons (list (first exprs)) (rest exprs)) :single-valuedp single-valuedp :joiner joiner))
   (t (let ( (first-item (cond (single-valuedp
				(cond ((not (singletonp (first exprs)))		; error! (a b) found
				       (km-trace 'comment
						 "Multiple values ~a found for single-valued slot!~%Assuming they should be unified...~%"
						 (first exprs))
				       (vals-to-&-expr (first exprs) :joiner joiner)) ; (a b) -> (a & b) (sing-val slot)
				      (t (first (first exprs))))) ; (a)   -> a		(single-valued slot)
			       (t (first exprs))))				; (a b c) -> (a b c)	(multivalued slot)
	     (linked-rest (val-sets-to-expr0 (rest exprs) :single-valuedp single-valuedp :joiner joiner)))
	(cond ((null linked-rest) (list first-item))
	      (t (cons first-item (cons joiner linked-rest))))))))

;;; ======================================================================
;;;		FLATTENING '&' AND '&&' EXPRESSIONS
;;; ======================================================================

;;; vals should be either nil, or a SINGLETON list of one KM expression eg. (a), ((a & b)).
;;; RETURNS the component values as a list, eg. (a), (a b)
(defun un-andify (vals)
  (cond ((null vals) nil)
	((singletonp vals) (&-expr-to-vals (first vals)))
	(t (km-trace 'comment "Multiple values ~a found for single-valued slot!~%Assuming they should be unified...~%" vals)
	   (my-mapcan #'&-expr-to-vals vals))))

;;; (&-expr-to-vals '(x & y & z)) -> (x y z)
;;; (&-expr-to-vals '((a Car) & (a Dog))) -> ((a Car) (a Dog)))
;;; (&-expr-to-vals '(a Car)) -> ((a Car))	<- NB listify
;;; (&-expr-to-vals 'x) -> (x)			<- NB listify
;;; (&-expr-to-vals '((a & (b & d)) & (e & (f & g)))) -> (a b c d e f g)    <- NB nested
;;; (&-expr-to-vals '(x & y z))			<- ERROR!
(defun &-expr-to-vals (expr)
  (cond ((null expr) nil)
	((&-exprp expr)
	 (cond (;(eq (fourth expr) '&)				; (x & y & ...)
		(val-unification-operator (fourth expr))
		(&-expr-to-vals `(,(first expr) ,(fourth expr) ,(rest (rest expr)))))
	       (t (cond ((not (= (length expr) 3))
			 (report-error 'user-error "Illegally formed expression ~a encountered!~%Continuing with just ~a...~%"
				       expr (subseq expr 0 3))))
		  (append (&-expr-to-vals (first expr)) (&-expr-to-vals (third expr))))))
	(t (list expr))))

;;; nil -> nil, (a) -> a, (a b c) -> (a & b & c)
(defun vals-to-&-expr (vals &key (joiner '&) (first-time-through t))
  (cond ((null vals) nil)
	((singletonp vals)
	 (cond (first-time-through (first vals))
	       (t vals)))
	(t `(,(first vals) ,joiner ,@(vals-to-&-expr (rest vals) :joiner joiner :first-time-through nil)))))

;;; (valsets-to-&&-exprs '((a b) (c d) (e f))) -> (((a b) && (c d) && (e f)))
;;; NOTE! (valsets-to-&&-exprs '((a b)) -> (a b)
(defun valsets-to-&&-exprs (valsets)
  (cond ((null valsets) nil)
	((singletonp valsets) (first valsets))
	(t (val-to-vals (vals-to-&-expr valsets :joiner '&&)))))

;;; (&&-exprs-to-valsets '(a b)) -> ((a b))
;;; (&&-exprs-to-valsets '(((a b) && (c d)))) -> ((a b) (c d))
;;; (&&-exprs-to-valsets '(((a b) && (c d) && (e f)))) -> ((a b) (c d) (e f))
;;; (&&-exprs-to-valsets '(((a b) && (((c d) && (e f)))))) -> ((a b) (c d) (e f))
;;; (&&-exprs-to-valsets '(((((a b) && (c d))) && (e f)))) -> ((a b) (c d) (e f))
;;; (&&-exprs-to-valsets '(a ((a b) && (c d)))) -> ((a ((a b) && (c d))))
(defun &&-exprs-to-valsets (exprs)
  (cond ((singletonp exprs)
	 (let ( (expr (first exprs)) )
	   (cond ((and (listp expr)
		       (set-unification-operator (second expr)))
		  (append (&&-exprs-to-valsets (first expr))
			  (cond ((triplep expr)
				 (&&-exprs-to-valsets (third expr)))
				(t (&&-exprs-to-valsets (list (rest (rest expr))))))))
		 (t (list exprs)))))
	(t (list exprs))))

;;; ----------------------------------------
;;;	Digging out the constraints...
;;; ----------------------------------------

#|
Call with a SINGLE EXPRESSION. It will further call itself with either with
          (a) a single value, with :joiner = &
   or     (b) a list of values, with :joiner = &&
RETURNS the constraints embedded in the expression.

Shown below, where numbers denote things passing constraint-exprp test.
A test procedure is in find-constraints.lisp, a multivalued version of the below.

	EXPRESSION				==>	CONSTRAINTS
	(a & 1 & 2)					(1 2)
	(a & 1 & 2 & (3 & d))				(1 2 3)
	(a & 1 & 2 & (3 & (d & 4)))			(1 2 3 4)
	((a 1) && (b 2))				(1 2)
	((a 1 b) && (c 2 d))				(1 2)
	((a 1 b) && (c 2 d) && (e f))			(1 2)
	((a 1 b) && (((c 2 d) && (e f))))		(1 2)
	((a 1 b) && (((c 2 d) && (e f 3))))		(1 2 3)
	((a 1 b) && (((c 2 d) && (e f 3) && (4))))	(1 2 3 4)
	a						nil
	((((a 1) && (b 2)) d e) && (c 3))		(3)
	((((a 1) && (b 2)) d 4) && (c 3))		(4 3)
	((((a 1) && (b 2))) && (c 3))			(1 2 3)
|#

;;; [1] aggressive decommenting of constraints
(defun find-constraints-in-exprs (exprs)
; (find-constraints exprs 'plural))
; (desource+decomment 		; NEW: Remove desource+decomment, as we have comments on must-be-a
   (find-exprs exprs :expr-type 'constraint :plurality 'plural)) ; [1]

;;; *MAPCAN-SAFE*
;;; a, (a & b) (as && bs)   plurality = singular.
;;; (a) 		    plurality = plural (1 member).
;;; (a b) 		    plurality = plural (2 members).
;;; ((a b)) 		    plurality = plural (1 member).
;;; Note: (must-be-a Car)   plurality = singular   is a constraint,
;;;   but (must-be-a Car)   plurality = plural    isn't a constraint, it's two values "must-be-a" and "Car".
;;; Result is newly created list, so it is safe to mapcan over it.
;;; [1]    (find-constraints '#$(_Shut-Out16 (((<> _Be-Shut-Out5)) && ((<> _Be-Shut-Out15)))) 'plural)
;;; 	=> ((<> |_Be-Shut-Out5|) (<> |_Be-Shut-Out15|))

;;; GENERALIZE THIS to find expressions of any type
;;; expr-type = constraint | non-constraint | default | any
(defun find-exprs (expr &key expr-type (plurality 'singular))	; ie. a single expr given
  (cond ((null expr) nil)
	((and (listp expr)
	      (unification-operator (second expr)))
	 (cond ((>= (length expr) 4)
		(cond ((not (unification-operator (fourth expr)))
		       (report-error 'user-error "Badly formed unification expression ~a!~%" expr)))
		(find-exprs `(,(first expr) ,(second expr) ,(rest (rest expr)))
			    :expr-type expr-type :plurality 'singular))    ; (a & b & c) -> (a & (b & c))
	       (t (let ( (next-plurality (cond (; (eq (second expr) '&) 'singular)   ; & takes a value as arg, && takes a list of values
						(val-unification-operator (second expr)) 'singular)
					       (t 'plural))) )
		    (append (find-exprs (first expr) :expr-type expr-type :plurality next-plurality)
			    (find-exprs (third expr) :expr-type expr-type :plurality next-plurality))))))
	((and (eq plurality 'singular)		; & -> a single value/expr is given
	      (case expr-type
		    (constraint (constraint-exprp expr))
		    (non-constraint (not (constraint-exprp expr)))
		    (default (km-defaultp expr))
		    (any t)
;		    (override (overridep expr))
		    (t (report-error 'program-error "find-exprs: Unrecognized expr-type `~a'!~%" expr-type))))
	 (list expr))
	((and (eq plurality 'plural)		; special case - allowed to recurse if only one member
	      (singletonp expr))
	 (find-exprs (first expr) :expr-type expr-type :plurality 'singular))
	((and (eq plurality 'plural)			; && -> a list of values is given
	      (listp expr))
	 (mapcan #'(lambda (subexpr) (find-exprs subexpr :expr-type expr-type :plurality 'singular))  expr))))		; [1]

;;; ----------

;;; This is to remove constraints from a POST-EVALUATED expression ONLY. A post-evaluated expression is
;;;   single-valued slots: either a single value, or a single value &'ed with constraints
;;;			   eg. (1) -> (1), ((a & (must-be x))) -> (a)
;;;   multivalued slots:   a list of values + constraints eg. (1 2 (must-be y)) -> (1 2)
;;; RETURNS: A list of values
;;; (remove-constraints '#$((a & (must-be-a c)))) -> '#$(a)
;;; (remove-constraints '#$(a b (must-be-a c))) -> '#$(a b)
(defun remove-constraints (vals)
  (cond ((not *are-some-constraints*) vals)
	((null vals) nil)
	((and (singletonp vals)
	      (listp (first vals))
;	      (eq (second (first vals)) '&))					; single-valued-slot format ((a & (must-be b)))
	      (val-unification-operator (second (first vals))))
	 (remove-if #'constraint-exprp (&-expr-to-vals (first vals))))
	(t (remove-if #'constraint-exprp vals))))

(defun extract-constraints (vals)
  (cond ((not *are-some-constraints*) nil)
	((null vals) nil)
	((and (singletonp vals)
	      (listp (first vals))
;	      (eq (second (first vals)) '&))					; single-valued-slot format ((a & (must-be b)))
	      (val-unification-operator (second (first vals))))
	 (remove-if-not #'constraint-exprp (&-expr-to-vals (first vals))))
	(t (remove-if-not #'constraint-exprp vals))))

;;; ======================================================================
;;;		RECOGNIZING DESCRIPTIONS
;;; ======================================================================

(defun quoted-expressionp (expr) (quotep expr))

(defun quoted-descriptionp (expr)
  (and (quotep expr)
       (listp (unquote expr))
       (eq (first (unquote expr)) '#$every)))

;;; '(every ...) or (the-class ...)
(defun descriptionp (expr)
  (or (quoted-descriptionp expr)
      (the-class-exprp expr)))

(defun the-class-exprp (expr) (and (listp expr) (eq (first expr) '#$the-class)))

;;; '(a Cat) -> t
(defun instance-descriptionp (expr &key (fail-mode 'fail))
  (cond
   ((and (quoted-expressionp expr)
	 (listp (unquote expr)))
    (cond
     ((existential-exprp (unquote expr)))
     ((km-triplep (unquote expr)))		; <--- Bit of a fudge here: subsumes also handles triples as if they were descriptions
     ((eq fail-mode 'error)
      (cond
       ((eq (first (unquote expr)) '#$every)	; '(every Cat) -> ERROR
	(report-error 'user-error "Expecting an instance description '(a ...), but found a class~%description ~a instead!~%" expr))
       (t (report-error 'user-error "Expecting an instance description '(a ...), but found~%description ~a instead!~%" expr))))))
   ((eq fail-mode 'error)
    (report-error 'user-error "Expecting a quoted instance description '(a ...), but found an unquoted~%expression ~a instead!~%" expr))))

;;; Returns the class + slotsvals (as a two-element list) , if expr is indeed a class description
(defun class-descriptionp (expr &key (fail-mode 'fail))
  (cond
   ((quoted-descriptionp expr)
    (list (second (unquote expr)) (rest (rest (rest (unquote expr))))))
   ((the-class-exprp expr)		; (the-class X with Y)
    (let ( (class (second expr))
	   (slotsvals (cond ((eq (third expr) '#$called)
			     `((#$called ,(list (fourth expr))) ,@(rest (rest (rest (rest (rest expr)))))))
			    (t (rest (rest (rest expr)))))) )
      (list class slotsvals)))
   ((and (eq fail-mode 'error)
	 (quotep expr)
	 (eq (first (unquote expr)) '#$a))	; '(every Cat) -> ERROR
    (report-error 'user-error "Expecting a class description '(every ...), but found an instance~%description ~a instead!~%" expr))
   ((eq fail-mode 'error)
    (report-error 'user-error "Expecting a class description (the-class ...) or '(every ...), but found a different~%expression ~a instead!~%" expr))))

;;; (classes-in-description '#$(the-class X with (instance-of (Y)) (instance-of (Z)))) -> (X Y Z)
(defun classes-in-description (expr)
  (let* ((class+slotsvals (class-description-to-class+slotsvals expr))
	 (class (first class+slotsvals))
	 (slotsvals (second class+slotsvals))
	 (other-classes (my-mapcan #'(lambda (slotvals) (cond ((eq (slot-in slotvals) '#$instance-of) (vals-in slotvals)))) slotsvals)))
    (cons class other-classes)))

(defun class-description-to-class+slotsvals (expr &key (fail-mode 'fail))
  (class-descriptionp expr :fail-mode fail-mode))

;;; Name: a symbol denoting a function -- allows km-lisp-exprs* and *downcase-km-lisp-exprs* to be
;;; dynamically extended (thanks to Francis Leboutte)
(defun add-lisp&KM-function (name)
  (pushnew name *km-lisp-exprs* :test #'eq)
  (pushnew (intern (string-downcase name) *km-package*)
           *downcase-km-lisp-exprs*
           :test #'string=))


;;; ======================================================================

#|
The following KB has 4 axioms, one shown on each line:
(every Car has (parts ((a Engine with 			; Note 2 axioms: Engine, and
			  (parts ((a Fuel-Filter)))))) 	; parts of that Engins = Fuel-Filter
       (color (red)))
(Car has (superclasses (Vehicle)))

[1] Note that ground facts (Car has (superclasses (Vehicle))) will get counted twice, once in each direction,
    so let's divide this count by 2.
[2] Each separate axiom in a large KM expr is tagged internally with a "@" for explanation purposes
    Do (setq *developer-mode* t) then (showme <concept>) to see the @ visually
|#
(defun kb-size ()
  (let ((n 0))
    (mapc #'(lambda (concept)
	      (cond
	       ((not (anonymous-instancep concept)) ; avoid prototypes and run-time Skolems
		(mapc #'(lambda (facet)
			  (mapc #'(lambda (situation)
				    (mapc #'(lambda (slotvals)
					      (mapc #'(lambda (val)
							(cond ((kb-objectp val) (setq n (+ n 0.5))) ; [1]
							      (t (let ((n-embedded-rules
									(length (remove-if-not #'(lambda (x)
												   (eq x '@)) ; [2]
											       (flatten val)))))
								   (setq n (+ n n-embedded-rules))))))
						    (vals-in slotvals)))
					  (get-slotsvals concept :facet facet :situation situation)))
				(all-situations-and-theories)))
		      *all-facets*))))
	  (get-all-concepts))
    (values (floor n))))		; return integer for neatness
