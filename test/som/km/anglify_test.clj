(ns som.km.anglify-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.anglify :as anglify]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- text-of [result]
  (term/car (:value result)))

(defn- slash [path]
  (str/replace path "\\" "/"))

(defn- temp-path [suffix]
  (.getAbsolutePath (java.io.File/createTempFile "km-step14-" suffix)))

(defmacro with-temp
  [binding & body]
  `(let [~binding (temp-path ".km")]
     (try
       ~@body
       (finally
         (io/delete-file ~binding true)))))

(deftest sentences-and-phrases-join-words
  (let [sentence (answer "(make-sentence (:seq \"a\" \"cat\"))")
        phrase (answer "(make-phrase (:seq \"a\" \"cat\"))")
        hello (answer "(make-sentence \"hello\")")
        plain (answer "(make-phrase \"hello\")")
        three (answer "(make-sentence 3)")
        precise (answer "(make-sentence 1.5)")
        period (answer "(make-sentence (:seq \"a\" \"cat\" \".\" \"the\" \"dog\"))")
        owned (answer "(make-sentence (:seq \"cat\" \"nospace\" \"'s\"))")]
    (is (:ok sentence))
    (is (empty? (:errors sentence)))
    (is (= "A cat." (text-of sentence)))
    (is (= "a cat" (text-of phrase)))
    (is (= "Hello." (text-of hello)))
    (is (= "hello" (text-of plain)))
    (is (= "3." (text-of three)))
    (is (= "1.500." (text-of precise)))
    (is (= "A cat. The dog." (text-of period)))
    (is (= "Cat's." (text-of owned)))))

(deftest andify-joins-with-and-and-commas
  (let [two (answer "(make-phrase (andify (:set \"a\" \"b\")))")
        three (answer "(make-phrase (andify (:set \"a\" \"b\" \"c\")))")]
    (is (= "a and b" (text-of two)))
    (is (= "a, b, and c" (text-of three)))
    (is (empty? (:errors three)))))

(deftest a-name-replaces-an-instance-until-it-stops
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        phrase (on cat "(make-phrase _Cat1)")
        named (answer "(Fred has (name (\"FRED\")))")
        word (on named "(make-phrase Fred)")
        sentence (on named "(make-sentence Fred)")]
    (is (= "the cat" (text-of phrase)))
    (is (empty? (:errors phrase)))
    (is (= "FRED" (text-of word)))
    (is (= "FRED." (text-of sentence)))))

(deftest a-loaded-verbose-flag-says-the-value
  (with-temp path
    (spit path "(SETQ *VERBOSE-NUMBER-TO-TEXT* t)\n")
    (let [refused (answer "(SETQ *VERBOSE-NUMBER-TO-TEXT* t)")
          loaded (answer (str "(load-kb \"" (slash path) "\")"))
          sentence (on loaded "(make-sentence 3)")]
      (is (= "not-ported" (:error refused)))
      (is (str/includes? (:message refused) "setq is not evaluated"))
      (is (:ok loaded))
      (is (= "The value 3." (text-of sentence))))))

(deftest pluralize-records-that-it-is-no-longer-defined
  (let [result (answer "(pluralize \"cat\")")]
    (is (:ok result))
    (is (nil? (:error result)))
    (is (nil? (:value result)))
    (is (some #(str/includes? % "pluralize is no longer defined") (:errors result)))
    (is (not (some #(str/includes? % "not-ported") (:errors result))))))

(deftest a-name-deeper-than-the-limit-records-an-error
  (let [started (engine/session)
        result (anglify/expand-text started (symbol "Cat") (fn [state _] state)
                                    :depth 101)]
    (is (some #(str/includes? % "Infinite recursion") (:errors (:state result))))))

(deftest taxonomy-prints-thing-in-list-order
  (let [fresh (answer "(taxonomy)")
        integer (on fresh "(the superclasses of Integer)")
        moth (answer "(Moth has (superclasses (Thing)))")
        yak (on moth "(Yak has (superclasses (Thing)))")
        fred (on yak "(Fred has (instance-of (Yak)))")
        hidden (on fred "(_Cat9 has (instance-of (Yak)))")
        again (on hidden "(_Hidden1 has (instance-of (Moth)))")
        tree (on again "(taxonomy)")
        same (on tree "(taxonomy)")
        text (:text tree)
        slots (answer "(color has (subslots (hue)))")
        hue (on slots "(taxonomy color subslots)")
        extra (answer "(taxonomy Thing subclasses extra)")]
    (is (str/includes? (:text fresh) "Removing redundant superclasses...\n"))
    (is (str/includes? (:text fresh) "Removing redundant subclasses...\n"))
    (is (str/includes? (:text fresh) "Computing subclasses of Thing...\n"))
    (is (re-find #"(?m)^Thing$" (:text fresh)))
    (is (= (term-of "(Number)") (:value integer)))
    (is (re-find #"(?m)^   Yak$" text))
    (is (re-find #"(?m)^   Moth$" text))
    (is (< (.indexOf text "\n   Yak\n") (.indexOf text "\n   Moth\n")))
    (is (re-find #"(?m)^I     Fred$" text))
    (is (nil? (re-find #"(?m)^I .*_Cat9$" text)))
    (is (nil? (re-find #"(?m)^I .*_Hidden1$" text)))
    (is (not (str/includes? text "_Cat9")))
    (is (not (str/includes? text "_Hidden1")))
    (is (= text (:text same)))
    (is (not (str/includes? (str (:text hue)) "Removing redundant")))
    (is (re-find #"(?m)^color$" (:text hue)))
    (is (re-find #"(?m)^   hue$" (:text hue)))
    (is (:ok extra))
    (is (nil? (:value extra)))
    (is (some #(str/includes? % "Too many arguments") (:errors extra)))))

(deftest justify-leaves-prints-one-english-sentence
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        plain (on color "(justify)")
        kb (assoc-in (:kb color) [:runtime :justify-leaves?] true)
        english (engine/evaluate "(justify)" {:kb kb :query (:query color)})]
    (is (not (str/includes? (str (:text plain)) "subgoal")))
    (is (str/includes? (:text english) "The color of the cat = black."))
    (is (not (str/includes? (:text english) "(from ")))
    (is (:ok english))))
