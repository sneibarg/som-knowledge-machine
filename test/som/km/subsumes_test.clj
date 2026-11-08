(ns som.km.subsumes-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.subsumes :as subsumes]
            [som.km.term :as term]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- frames-of [result]
  (set (keys (:frames (:kb result)))))

(deftest an-instance-matches-a-quoted-description
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        yes (on cat "(_Cat1 is '(a Cat))")
        dog (answer "(_Dog1 has (instance-of (Dog)))")
        no (on dog "(_Dog1 is '(a Cat))")
        same (on cat "(_Cat1 is _Cat1)")]
    (is (= (term "(t)") (:value yes)))
    (is (empty? (:errors yes)))
    (is (nil? (:value no)))
    (is (empty? (:errors no)))
    (is (= (term "(t)") (:value same)))
    (is (empty? (:errors same)))))

(deftest a-description-can-require-a-slot-value
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        red (on cat "(_Cat1 has (color (red)))")
        blue (on cat "(_Cat1 has (color (blue)))")
        yes (on red "(_Cat1 is '(a Cat with (color (red))))")
        no (on blue "(_Cat1 is '(a Cat with (color (red))))")]
    (is (= (term "(t)") (:value yes)))
    (is (empty? (:errors yes)))
    (is (nil? (:value no)))
    (is (empty? (:errors no)))))

(deftest a-constraint-is-satisfied-before-the-match-succeeds
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        red (on cat "(_Cat1 has (color (red)))")
        open (on red "(_Cat1 is '(a Cat with (color (red (must-be-a Color)))))")
        colored (on red "(red has (instance-of (Color)))")
        closed (on colored "(_Cat1 is '(a Cat with (color (red (must-be-a Color)))))")
        thing (on red "(_Cat1 is '(a Cat with (color (red (must-be-a Thing)))))")]
    (is (nil? (:value open)))
    (is (empty? (:errors open)))
    (is (= (term "(t)") (:value closed)))
    (is (empty? (:errors closed)))
    (is (= (term "(t)") (:value thing)))
    (is (empty? (:errors thing)))))

(deftest the-search-returns-the-instances-already-stored
  (let [first-cat (answer "(_Cat1 has (instance-of (Cat)))")
        red (on first-cat "(_Cat1 has (color (red)))")
        second (on red "(_Cat2 has (instance-of (Cat)))")
        blue (on second "(_Cat2 has (color (blue)))")
        found (on blue "(the Cat with (color (red)))")
        both (on blue "(every Cat)")
        many (on blue "(_Cat2 has (color (red)))")
        two (on many "(the Cat with (color (red)))")
        none (on blue "(the Cat with (color (green)))")]
    (is (= (term "(_Cat1)") (:value found)))
    (is (empty? (:errors found)))
    (is (= (term "(_Cat2 _Cat1)") (:value both)))
    (is (nil? (:value two)))
    (is (some #(re-find #"multiple values" %) (:errors two)))
    (is (nil? (:value none)))
    (is (some #(re-find #"No values found" %) (:errors none)))
    (is (= (frames-of blue) (frames-of none)))
    (is (= (:counter (:kb blue)) (:counter (:kb none))))))

(deftest a-covered-existential-is-not-stored-again
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        owned (on cat "(_Pete has (owns (_Cat1)))")
        again (on owned "(_Pete has (owns ((a Cat))))")
        kept (frame/get-vals (:kb again) (symbol "_Pete") (symbol "owns"))
        plain (answer "(_Pete has (owns (_Dog1)))")
        both (on plain "(_Pete has (owns ((a Cat))))")
        stored (frame/get-vals (:kb both) (symbol "_Pete") (symbol "owns"))]
    (is (= (term "(_Cat1)") (:value kept)))
    (is (= (term "(((_Dog1) && ((a Cat))))") (:value stored)))))

(deftest set-unification-drops-an-existential-that-covers-an-instance
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        covered (on cat "((_Cat1) && ((a Cat)))")
        dog (on cat "((_Cat1) && ((a Dog)))")
        painted (on cat "((_Cat1) && ((a Cat with (color (red)))))")
        color (frame/get-vals (:kb painted) (symbol "_Cat1") (symbol "color"))]
    (is (= (term "(_Cat1)") (:value covered)))
    (is (empty? (:errors covered)))
    (is (not= "not-ported" (:error covered)))
    (is (= (frames-of cat) (frames-of covered)))
    (is (= (:counter (:kb cat)) (:counter (:kb covered))))
    (is (= (term "(_Cat1 (a Dog))") (:value dog)))
    (is (empty? (:errors dog)))
    (is (not= "not-ported" (:error dog)))
    (is (= (term "(_Cat1)") (:value painted)))
    (is (empty? (:errors painted)))
    (is (= (term "(red)") (:value color)))))

(deftest a-slotless-class-description-uses-the-subclass-link
  (let [numbers (answer "(Number subsumes Integer)")
        swapped (answer "(Integer subsumes Number)")
        before (answer "(Cat subsumes Animal)")
        linked (answer "(Cat has (superclasses (Animal)))")
        after (on linked "(Animal subsumes Cat)")
        still (on linked "(Cat subsumes Animal)")
        slotted (answer "('(a Cat with (color (red))) is '(a Animal))")]
    (is (= (term "(t)") (:value numbers)))
    (is (empty? (:errors numbers)))
    (is (nil? (:value swapped)))
    (is (nil? (:value before)))
    (is (= (term "(t)") (:value after)))
    (is (nil? (:value still)))
    (is (= "not-ported" (:error slotted)))))

(deftest isa-uses-the-stored-class
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        yes (on cat "(_Cat1 isa Cat)")
        no (on cat "(_Cat1 isa Dog)")
        number (answer "(1 isa Number)")]
    (is (= (term "(t)") (:value yes)))
    (is (nil? (:value no)))
    (is (empty? (:errors no)))
    (is (= (term "(t)") (:value number)))))

(deftest the-plus-searches-and-then-refuses-to-create
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        red (on cat "(_Cat1 has (color (red)))")
        found (on red "(the+ Cat with (color (red)))")
        also (on red "(a+ Cat with (color (red)))")
        missing (on red "(the+ Cat with (color (green)))")
        defined (answer "(every Cat has (color (black)))")
        created (answer "(a Cat)")]
    (is (= (term "(_Cat1)") (:value found)))
    (is (not= "not-ported" (:error found)))
    (is (= (term "(_Cat1)") (:value also)))
    (is (= "not-ported" (:error missing)))
    (is (= (term "(Cat)") (:value defined)))
    (is (not= "not-ported" (:error defined)))
    (is (= "not-ported" (:error created)))))

(deftest the-plus-keeps-the-first-of-several-matches
  (let [first-cat (answer "(_Cat1 has (instance-of (Cat)))")
        red (on first-cat "(_Cat1 has (color (red)))")
        second (on red "(_Cat2 has (instance-of (Cat)))")
        both (on second "(_Cat2 has (color (red)))")
        picked (on both "(the+ Cat with (color (red)))")]
    (is (= (term "(_Cat2)") (:value picked)))
    (is (some #(re-find #"multiple values" %) (:errors picked)))
    (is (not= "not-ported" (:error picked)))))

(deftest a-path-searches-the-object-stack
  (let [wing (answer "(_Wing1 has (instance-of (Wing)))")
        linked (on wing "(_Wing1 has (parts-of (airplane)))")
        found (on linked "(every (airplane parts Wing))")]
    (is (= (term "(_Wing1)") (:value found)))
    (is (empty? (:errors found)))))

(deftest a-set-can-include-a-value
  (is (= (term "(t)") (:value (answer "((:set 1 2) includes 2)"))))
  (is (nil? (:value (answer "((:set 1 2) includes 3)"))))
  (is (= (term "(t)") (:value (answer "((:set 1 2) is-superset-of (:set 2))"))))
  (is (nil? (:value (answer "((:set 1) is-superset-of (:set 1 2))")))))

(deftest a-path-becomes-an-existential
  (let [kb (:kb (frame/reset (frame/knowledge-base)))]
    (is (= (term "(a wing with (parts-of (airplane)))")
           (subsumes/path-to-existential-expr kb (term "(airplane parts wing)"))))
    (is (= (term "(a edp with (parts-of ((a wing with (parts-of (airplane01))))))")
           (subsumes/path-to-existential-expr
            kb (term "(airplane01 parts wing parts edp)"))))
    (is (= (term "(a Thing with (parts-of ((a wing with (parts-of (airplane01))))))")
           (subsumes/path-to-existential-expr
            kb (term "(airplane01 parts wing parts)"))))
    (is (= (term "(a Thing with (parts-of (airplane)))")
           (subsumes/path-to-existential-expr kb (term "(airplane parts *)"))))))
