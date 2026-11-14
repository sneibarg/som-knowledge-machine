(ns som.km.creation-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- name-of [result]
  (term/symbol-name (term/car (:value result))))

(defn- slash [path]
  (str/replace path "\\" "/"))

(def ^:private door-file
  "src/resources/km-component-library/rkf-clib/components/core/Door.km")

(deftest a-cat-is-a-skolem-on-the-object-stack
  (let [created (answer "(a Cat)")
        classes (on created "(the instance-of of _Cat1)")
        stack (:obj-stack (:query created))
        again (on created "(a Cat)")]
    (is (:ok created))
    (is (nil? (:error created)))
    (is (= (term-of "(_Cat1)") (:value created)))
    (is (= (term-of "(Cat)") (:value classes)))
    (is (utils/member? (symbol "_Cat1") stack))
    (is (pos? (or (:skolems (:query created)) 0)))
    (is (str/includes? (:statistics created) "inferences"))
    (is (= (term-of "(_Cat2)") (:value again)))))

(deftest a-path-in-a-slot-is-evaluated-when-the-slot-is-read
  (let [fred (answer "(Fred has (color (red)))")
        created (on fred "(a Cat with (color ((the color of Fred))))")
        color (on created "(the color of _Cat1)")
        broken (answer "(a Cat with black)")
        number (answer "(a 1)")]
    (is (= (term-of "(_Cat1)") (:value created)))
    (is (= (term-of "(red)") (:value color)))
    (is (empty? (:errors color)))
    (is (nil? (:value broken)))
    (is (some #(re-find #"slot\+values" %) (:errors broken)))
    (is (nil? (:value number)))
    (is (some #(re-find #"Class name" %) (:errors number)))))

(deftest a-miss-creates-an-instance-and-a-bad-situation-turns-the-mode-on
  (let [entered (answer "(in-situation (a Cat))")]
    (is (nil? (:value entered)))
    (is (some #(re-find #"isn't declared an instance of Situation" %) (:errors entered)))
    (is (frame/situations-mode? (:kb entered)))
    (is (frame/known-frame? (:kb entered) (symbol "_Cat1")))))

(deftest a-component-file-creates-the-parts-its-rules-name
  (let [loaded (answer (str "(load-kb \"" (slash door-file) "\")"))
        door (on loaded "(a Door)")
        name (name-of door)
        plays (on door (str "(the plays of " name ")"))
        part (on plays (str "(the is-part-of of " name ")"))
        play-name (name-of plays)
        part-name (name-of part)
        play-class (on part (str "(the instance-of of " play-name ")"))
        part-class (on part (str "(the instance-of of " part-name ")"))]
    (is (:ok loaded))
    (is (nil? (:error loaded)))
    (is (empty? (:errors loaded)))
    (is (str/starts-with? name "_Door"))
    (is (str/starts-with? play-name "_Portal-Covering"))
    (is (= (term-of "(Portal-Covering)") (:value play-class)))
    (is (str/starts-with? part-name "_Architectural-Structure"))
    (is (= (term-of "(Architectural-Structure)") (:value part-class)))))
