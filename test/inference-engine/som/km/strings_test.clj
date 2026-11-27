(ns som.km.strings-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.strings :as strings]))

(deftest substitute-string-matches-the-lisp-examples
  (is (= "AA cAAt is rAA"
         (strings/substitute-string "a" "AA" "a cat is ra")))
  (is (= "aaaa"
         (strings/substitute-string "aa" "a" "aaaaaaa")))
  (is (= "a"
         (strings/substitute-string "aa" "a" "aaaaaaa" true)))
  (is (= [\a \| \b] (strings/explode "a|b"))))
