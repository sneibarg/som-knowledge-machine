(ns som.km.repl-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.repl :as repl]))

(deftest q-leaves-the-prompt
  (is (= {:leave true :text ""} (repl/respond "q")))
  (is (= {:leave true :text ""} (repl/respond "  q  "))))

(deftest other-text-is-submitted-to-the-engine
  (let [reply (repl/respond "Q")]
    (is (= false (:leave reply)))
    (is (= (:message (engine/evaluate "Q")) (:text reply))))
  (let [reply (repl/respond "  (a Cat) ")]
    (is (= false (:leave reply)))
    (is (= (:message (engine/evaluate "  (a Cat) ")) (:text reply)))))

(deftest an-answer-would-be-printed-from-the-value
  (is (= "42" (repl/reply-text {:ok true :value 42}))))

(deftest banner-names-the-knowledge-machine-version
  (is (re-find #"v2\.5\.45" (repl/banner)))
  (is (re-find #"q leaves the prompt" (repl/banner))))
