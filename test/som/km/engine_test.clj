(ns som.km.engine-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]))

(deftest status-names-the-build-and-both-fronts
  (let [status (engine/status)]
    (is (= "2.5.45" (:km-version status)))
    (is (= "som-knowledge-machine" (:name status)))
    (is (= ["repl" "http"] (:interfaces status)))
    (is (= "not-ported" (:evaluator status)))))

(deftest blank-text-is-refused
  (is (= {:ok false
          :error "empty"
          :message "Type a Knowledge Machine expression."}
         (engine/evaluate nil)))
  (is (= "empty" (:error (engine/evaluate "   ")))))

(deftest text-is-trimmed-and-not-evaluated
  (let [result (engine/evaluate "  (the age of Fred)  ")]
    (is (= false (:ok result)))
    (is (= "not-ported" (:error result)))
    (is (= "(the age of Fred)" (:input result)))
    (is (seq (:message result)))))
