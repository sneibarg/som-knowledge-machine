(ns som.km.minimatch-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.minimatch :as match]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(def ^:private success (symbol "t"))

(deftest variable-names-follow-the-lisp-rules
  (is (match/variable? (symbol "?x")))
  (is (match/variable? :?x))
  (is (match/variable? (symbol "?Any")))
  (is (not (match/variable? (symbol "x"))))
  (is (not (match/variable? (symbol ""))))
  (is (match/anonymous-var? (symbol "?any")))
  (is (match/anonymous-var? (symbol "?ANY")))
  (is (match/anonymous-var? (symbol "?*")))
  (is (not (match/anonymous-var? (symbol "?Any"))))
  (is (match/wildcard-var? (symbol "?*")))
  (is (not (match/wildcard-var? (symbol "?any"))))
  (is (match/rest-var? (symbol "&rest")))
  (is (match/rest-var? (symbol "&rest3")))
  (is (not (match/rest-var? (symbol "&REST"))))
  (is (not (match/rest-var? :&rest))))

(deftest minimatch-returns-captured-pieces-and-ignores-names
  (is (nil? (match/minimatch (symbol "x") (symbol "y"))))
  (is (= success (match/minimatch (term "(a b)") (term "(a b)"))))
  (is (= success (match/minimatch nil nil)))
  (is (nil? (match/minimatch (term "(a)") nil)))
  (is (nil? (match/minimatch 1 1.0)))
  (is (= (term "(b c)")
         (match/minimatch (term "(a b c)") (term "(a ?x ?y)"))))
  (is (= (term "(b c)")
         (match/minimatch (term "(a b c)") (term "(a ?x ?x)"))))
  (is (= (term "(c d e)")
         (match/minimatch (term "(a b c (d e))") (term "(a b ?x (?y ?z))"))))
  (is (= (term "(c (d e))")
         (match/minimatch (term "(a b c (d e))") (term "(a b ?x ?y)"))))
  (is (= (term "((c (d e)))")
         (match/minimatch (term "(a b c (d e))") (term "(a b &rest)"))))
  (is (= (term "((c))")
         (match/minimatch (term "(a b c)") (term "(a b &rest)"))))
  (is (nil? (match/minimatch (term "(a b c)") (term "(a b &REST)"))))
  (is (= success (match/minimatch (term "(a b c)") (term "(a b ?any)"))))
  (is (= (term "(b)")
         (match/minimatch (term "(a b c)") (term "(a ?x ?any)"))))
  (is (= (term "(4 7 8)")
         (match/minimatch (term "(1 2 3 4 5 6 7 8)")
                          (term "(?* 3 ?x ?* 6 ?y ?z ?*)"))))
  (is (= (symbol "a")
         (match/minimatch1 (term "(a b c)") (term "(?x b c)"))))
  (is (thrown? clojure.lang.ExceptionInfo
        (match/minimatch1 (term "(a b)") (term "(a b)")))))

(deftest minimatch-pattern-uses-each-element-once
  (is (= (term "(2 1)")
         (match/minimatch-pattern (term "((a 1) (b 2) (c 3))")
                                  (term "((b ?x) (a ?y))"))))
  (is (= (term "(1 2)")
         (match/minimatch-pattern (term "((a 1) (a 2))")
                                  (term "((a ?x) (a ?y))"))))
  ;; remove without a count drops every structurally equal copy.
  (is (nil? (match/minimatch-pattern (term "((a 1) (a 1))")
                                     (term "((a ?x) (a ?y))"))))
  (is (= success (match/minimatch-pattern (term "(a b)") nil)))
  (is (= (term "(1 ((c d)))")
         (match/minimatch-pattern (term "((a 1) (c d))")
                                  (term "((a ?x) &rest)")))))

(deftest find-pattern-returns-the-first-hit
  (is (= (symbol "b")
         (match/find-pattern1 (term "((a r b) (a r c))") (term "(a r ?x)"))))
  (is (= (term "(a b)")
         (match/find-pattern (term "((a r b) (a r c))") (term "(?x r ?y)"))))
  (is (nil? (match/find-pattern (term "((a b))") (term "(c ?x)"))))
  (is (thrown? clojure.lang.ExceptionInfo
        (match/find-pattern1 (term "((a b))") (term "(a b)")))))

(deftest find-handler-returns-a-map
  (let [take-one (fn [value] value)
        none (fn [] :none)
        table (term/km-list (term/km-list (term "(a ?x)") take-one)
                            (term/km-list (term "(a b)") none))
        found (match/find-handler (term "(a b)") table)]
    (is (= take-one (:handler found)))
    (is (= (term "(b)") (:bindings found)))
    (is (= (term "(a ?x)") (:pattern found)))
    (is (= (symbol "b") (match/apply-handler found)))
    (is (= (symbol "b") (match/find-and-apply-handler (term "(a b)") table))))
  (let [none (fn [] :none)
        found (match/find-handler (term "(a b)")
                                  [[(term "(a b)") none]])]
    (is (nil? (:bindings found)))
    (is (= (term "(a b)") (:pattern found)))
    (is (= :none (match/apply-handler found))))
  (let [second-handler (fn [value] value)]
    (is (= (symbol "c")
           (match/apply-handler
            (match/find-handler (term "(b c)")
                                [[(term "(a ?x)") (fn [_] :no)]
                                 [(term "(b ?x)") second-handler]])))))
  (is (nil? (match/find-handler (term "(z)") [])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Can't find a handler"
        (match/find-handler (term "(z)") [] :fail-mode :error))))

(deftest full-match-records-bindings
  (is (= (term "((?a . a) (?b . b) (?c . (c)))")
         (match/full-match (term "(a b (c))") (term "(?a ?b ?c)"))))
  (is (= (term "((?b . b) (&rest . (c d)))")
         (match/full-match (term "(a b c d)") (term "(?any ?b &rest)"))))
  (is (= (term "((?b . b) (&rest . ((c))))")
         (match/full-match (term "(a b (c))") (term "(?any ?b &rest)"))))
  (is (= utils/null-bindings (match/full-match 1 1)))
  (is (= utils/null-bindings (match/full-match 1 (symbol "?any"))))
  (is (= (symbol "b")
         (utils/val-of (symbol "?b")
                       (match/full-match (term "(a b c)") (term "(?a ?b ?c)")))))
  (is (nil? (match/full-match (symbol "a") (symbol "b"))))
  ;; ?* is an anonymous variable here. It does not swallow several elements.
  (is (nil? (match/full-match (term "(1 2 3)") (term "(?* 3)"))))
  ;; The header says a repeated variable must match the same object.
  ;; add-binding records both pairs. val-of returns the earlier one.
  (let [bindings (match/full-match (term "(a b)") (term "(?x ?x)"))]
    (is (= (term "((?x . a) (?x . b))") bindings))
    (is (= (symbol "a") (utils/val-of (symbol "?x") bindings)))))

(deftest string-match-returns-substrings
  (is (= (term/km-list " cat ")
         (match/string-match "the cat sat"
                             (term/km-list "the" (symbol "?cat") "sat"))))
  (is (= (term/km-list "" " cat ")
         (match/string-match "the cat sat"
                             (term/km-list (symbol "?var") "the" (symbol "?cat") "sat"))))
  (is (= (term/km-list "cat")
         (match/string-match "the cat sat"
                             (term/km-list (symbol "?any") " " (symbol "?word") " " (symbol "?any")))))
  (is (= success
         (match/string-match "cat"
                             (term/km-list "c" (term/km-list (symbol "or") "x" "a") "t"))))
  (is (= " cat "
         (match/string-match1 "the cat sat"
                              (term/km-list "the" (symbol "?cat") "sat"))))
  (is (thrown? clojure.lang.ExceptionInfo
        (match/string-match1 "cat"
                             (term/km-list "c" (term/km-list (symbol "or") "a") "t"))))
  (is (= (term/km-list " Cat ")
         (match/string-match "The Cat Sat"
                             (term/km-list "the" (symbol "?cat") "sat"))))
  (is (nil? (match/string-match "The cat sat"
                                (term/km-list "the" (symbol "?cat") "sat")
                                :case-sensitive? true)))
  (is (= success
         (match/string-match "abY"
                             (term/km-list (term/km-list (symbol "or") "a" "ab") "Y"))))
  ;; The first copy of the anchor is the only one tried.
  (is (nil? (match/string-match "XcdXef"
                                (term/km-list (symbol "?x") "X" "ef"))))
  (is (nil? (match/string-match "cat"
                                (term/km-list (symbol "?x")
                                              (term/km-list (symbol "or") "?" "")))))
  (is (nil? (match/string-match "cat" (term/km-list (symbol "?x") (symbol "?y")))))
  (is (= (term/km-list "cd")
         (match/string-match "abcd" (term/km-list "ab" (symbol "&rest"))))))

(deftest a-three-element-a-form-is-a-syntax-error
  (let [result (engine/evaluate "(a ?x ?x)")]
    (is (:ok result))
    (is (nil? (:value result)))
    (is (some #(re-find #"Syntax error" %) (:errors result))))
  (is (= "interpreter" (:evaluator (engine/status)))))
