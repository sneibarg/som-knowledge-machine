(ns som.km.utils-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(deftest nil-is-both-an-atom-and-a-list
  (is (utils/lisp-list? nil))
  (is (utils/lisp-atom? nil))
  (is (utils/lisp-list? (term "(a)")))
  (is (not (utils/lisp-atom? (term "(a)"))))
  (is (utils/lisp-atom? (symbol "nil")))
  (is (not (utils/lisp-list? (symbol "nil")))))

(deftest eql-matches-same-type-numbers-and-equal-walks-structure
  (is (utils/eql? 1 1))
  (is (utils/eql? 1 1N))
  (is (utils/eql? 1/2 2/4))
  (is (utils/eql? 1.0 1.0))
  (is (not (utils/eql? 1 1.0)))
  (is (not (utils/eql? 1 1/2)))
  (is (not (utils/eql? "ab" (str "a" "b"))))
  (is (utils/equal? "ab" (str "a" "b")))
  (is (utils/equal? (term "(a (b))") (term "(a (b))")))
  (is (not (utils/equal? (term "(a . nil)") (term "(a)"))))
  (is (not (utils/equal? nil (symbol "nil"))))
  (is (not (utils/equal? 1 1.0))))

(deftest elements-walks-a-proper-list
  (is (= [(symbol "a") (symbol "b")] (utils/elements (term "(a b)"))))
  (is (= [] (utils/elements nil)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"dotted"
        (utils/elements (term "(a . b)")))))

(deftest listify-leaves-a-list-alone
  (is (nil? (utils/listify nil)))
  (is (= (term "(a)") (utils/listify (symbol "a"))))
  (is (= (term "(a b)") (utils/listify (term "(a b)")))))

(deftest append-and-mapcan-splice-proper-lists
  (is (= (term "(1 2 3 4)")
         (utils/append-lists (term "((1 2) (3 4))"))))
  (is (= (term "(a a b b)")
         (utils/mapcan-list #(term/km-list % %) (term "(a b)"))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"dotted"
        (utils/append-lists (term/cons-cell (term "(a)") (symbol "b"))))))

(deftest member-is-a-test-and-remove-counts
  (is (utils/member? (symbol "b") (term "(a b c)")))
  (is (not (utils/member? (symbol "z") (term "(a b c)"))))
  (is (= (term "(a c)")
         (utils/remove-items (symbol "b") (term "(a b b c)"))))
  (is (= (term "(a b c)")
         (utils/remove-items (symbol "b") (term "(a b b c)") :count 1))))

(deftest remove-duplicates-keeps-the-survivor-from-the-chosen-end
  ;; Default from-end is false, so the later copy stays. This is the
  ;; rule get-all-concepts will use. The letters stay lowercase.
  (is (= (term "(a c b d e)")
         (utils/remove-duplicates (term "(a b c b d d e)"))))
  (is (= (term "(a b c d e)")
         (utils/remove-duplicates (term "(a b c b d d e)") :from-end? true)))
  ;; The default test is eql, so two separately built lists both stay.
  (is (= (term "((a) (a))")
         (utils/remove-duplicates (term "((a) (a))"))))
  (is (= (term "((a))")
         (utils/remove-duplicates (term "((a) (a))")
                                  :test utils/equal?
                                  :from-end? true))))

(deftest set-exclusive-or-is-empty-when-the-sets-agree
  (is (nil? (utils/set-exclusive-or (term "(a b)") (term "(b a)"))))
  (is (= (term "(a c)")
         (utils/set-exclusive-or (term "(a b)") (term "(b c)")))))

(deftest quote-and-unquote-follow-the-two-element-list
  (is (utils/quote? (term "'hi")))
  (is (not (utils/quote? (term "(quote)"))))
  (is (not (utils/quote? (term "(quote a b)"))))
  (is (= (symbol "hi") (utils/unquote-expr (term "'hi"))))
  (is (= (symbol "hi") (utils/unquote-expr (symbol "hi")))))

(deftest bindings-keep-the-earliest-pair
  (is (= (term "((t . t))") utils/null-bindings))
  (is (= (symbol "b")
         (utils/val-of (symbol "?b") (term "((?b . b))"))))
  (is (nil? (utils/val-of (symbol "?z") utils/null-bindings)))
  (is (identical? utils/null-bindings
                  (utils/add-binding (symbol "t") (symbol "t") utils/null-bindings)))
  (let [bound-to-nil (utils/add-binding (symbol "?x") nil utils/null-bindings)]
    (is (some? (utils/bound-pair (symbol "?x") bound-to-nil)))
    (is (nil? (utils/val-of (symbol "?x") bound-to-nil)))
    (is (nil? (utils/bound-pair (symbol "?z") bound-to-nil))))
  (is (= (term "((?x . a) (?x . b))")
         (utils/add-binding (symbol "?x") (symbol "b")
                            (utils/add-binding (symbol "?x") (symbol "a")
                                               utils/null-bindings))))
  (let [once (utils/add-binding (symbol "?x") (symbol "a") utils/null-bindings)]
    (is (= once (utils/add-binding (symbol "?x") (symbol "a") once)))))
