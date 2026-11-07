(ns som.km.explain-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.explain :as explain]
            [som.km.read :as read]
            [som.km.term :as term]))

(defn- term [text]
  (:value (read/read-term text)))

(deftest user-comments-are-bracketed-symbols
  (is (explain/user-comment? (symbol "[tag]")))
  (is (explain/user-comment? (symbol "[]")))
  (is (not (explain/user-comment? (symbol "[tag"))))
  (is (not (explain/user-comment? (symbol "tag]"))))
  (is (not (explain/user-comment? (symbol "["))))
  (is (not (explain/user-comment? "[tag]")))
  (is (not (explain/user-comment? nil)))
  (is (explain/comment-tag? (explain/convert-comment (symbol "[Car1]")))))

(deftest a-source-is-a-list-headed-by-at
  (is (explain/source? (term "(@ Car parts)")))
  (is (not (explain/source? (term "(a Car)"))))
  (is (not (explain/source? (symbol "@")))))

(deftest convert-comments-stores-the-comm-form
  (is (= (term/km-list (symbol "comm") (symbol "[Car1]") (symbol "Self"))
         (explain/convert-comment (symbol "[Car1]"))))
  (is (= (term "(a (comm [Car1] Self))")
         (explain/convert-comments (term "(a [Car1])"))))
  (let [stored (explain/convert-comment (symbol "[Car1]"))]
    (is (identical? stored (explain/convert-comments stored)))))

(deftest decomment-leaves-a-pair-unless-asked-to-collapse-it
  (is (= (term "(a)") (explain/decomment (term "(a [1])"))))
  (is (= (symbol "a")
         (explain/decomment (term "(a [1])") :no-delistification? false))))

(deftest desource-drops-a-source-and-one-pair-of-parentheses
  (is (= (term "(a Wheel with (position (front)))")
         (explain/desource
          (term "(a Wheel with (position ((front (@ Car has-part Wheel position)))))"))))
  (is (= (term "(:seq)")
         (explain/desource (term "(:seq (@ p))"))))
  (is (not= :seq (explain/desource (term "(:seq (@ p))")))))

(deftest desource-decomment-follows-the-lisp-examples
  ;; The comment above desource+decomment still prints (cat (dog (man))).
  ;; That is the older remove-if walk. The function that is defined
  ;; delistifies ([4] [45] man) to man, so the result is (cat (dog man)).
  (is (= (term "(cat (dog man))")
         (explain/desource-decomment
          (term "(cat [1] (dog [3] ([4] [45] man)))"))))
  (is (= (term "(a Man with (size (((a Large)))))")
         (explain/desource-decomment
          (term "(a Man with (size (((a [2] Large)))) [1])"))))
  (is (= (term "(a Man with (size (*large)))")
         (explain/desource-decomment
          (term "(a Man with (size (([2] *large))) [1])"))))
  (is (= (term "(instance-of (Thing))")
         (explain/desource-decomment (term "(instance-of (Thing [cat]))"))))
  (is (= (symbol "*cat")
         (explain/desource-decomment (term "(*cat [1])"))))
  (is (= (term "(no-inheritance)")
         (explain/desource-decomment (term "(no-inheritance [1])"))))
  (is (= (term "(:seq)")
         (explain/desource-decomment (term "(:seq [1])")))))

(deftest retain-comments-returns-the-same-expression
  (let [expr (term "(*cat [1])")]
    (is (= expr (explain/desource-decomment expr :retain-comments? true)))))

(deftest desource-decomment-top-level-collapses-one-pair
  (is (= (symbol "*black")
         (explain/desource-decomment-top-level (term "(*black (@ Car color))"))))
  (is (= (term "(the age of Fred)")
         (explain/desource-decomment-top-level (term "(the age of Fred (@ Car))"))))
  (is (= (term "(:seq)")
         (explain/desource-decomment-top-level (term "(:seq [1])"))))
  (is (= (term "(no-inheritance)")
         (explain/desource-decomment-top-level (term "(no-inheritance [1])")))))

(deftest a-dotted-list-is-an-error-for-mapcar-and-not-for-the-tail-walk
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"dotted"
        (explain/desource (term/cons-cell (symbol "a") (symbol "b")))))
  (let [expr (term/cons-cell (symbol "a") (symbol "b"))]
    (is (= expr (explain/desource-decomment expr)))))
