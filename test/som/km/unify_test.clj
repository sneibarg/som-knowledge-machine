(ns som.km.unify-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- holds?
  "True when value is an element of a KM list."
  [value items]
  (boolean (some #(utils/eql? % value) (utils/elements items))))

(deftest same-class-instances-unify
  (let [left (answer "(_Cat1 has (instance-of (Cat)))")
        both (on left "(_Cat2 has (instance-of (Cat)))")
        unified (on both "(_Cat1 & _Cat2)")]
    (is (= (term "(_Cat1)") (:value unified)))
    (is (empty? (:errors unified)))
    (is (= (symbol "_Cat1")
           (frame/dereference (:kb unified) (symbol "_Cat2"))))))

(deftest different-named-instances-do-not-unify
  (let [left (answer "(*Fred has (age (1)))")
        both (on left "(*Sue has (age (2)))")
        failed (on both "(*Fred & *Sue)")]
    (is (nil? (:value failed)))
    (is (some #(re-find #"different objects" %) (:errors failed)))
    (is (= (:kb both) (:kb failed)))))

(deftest numbers-and-the-equality-test
  (is (= (term "(1)") (:value (answer "(1 & 1)"))))
  (let [different (answer "(1 & 2)")
        tested (answer "(1 &? 1.0)")
        committed (answer "(1 & 1.0)")]
    (is (nil? (:value different)))
    (is (= 1 (count (:errors different))))
    (is (some #(re-find #"different numbers" %) (:errors different)))
    (is (= (term "(t)") (:value tested)))
    (is (= (term "(1)") (:value committed)))
    (is (empty? (:errors committed)))))

(deftest a-test-does-not-keep-the-trial
  (let [left (answer "(_C1 has (instance-of (Cat)))")
        both (on left "(_C2 has (instance-of (Cat)))")
        tested (on both "(_C1 &? _C2)")
        numbers (answer "(1 &? 2)")
        fresh (answer "t")]
    (is (= (term "(t)") (:value tested)))
    (is (= (:kb both) (:kb tested)))
    (is (= (symbol "_C2") (frame/dereference (:kb tested) (symbol "_C2"))))
    (is (nil? (:value numbers)))
    (is (= (:kb fresh) (:kb numbers)))))

(deftest class-subsumption-can-reject-a-pair
  (let [left (answer "(_C1 has (instance-of (Cat)))")
        both (on left "(_D1 has (instance-of (Dog)))")
        rejected (on both "(_C1 &+ _D1)")
        combined (on both "(_C1 & _D1)")
        classes (frame/get-vals (:kb combined) (symbol "_C1") (symbol "instance-of"))]
    (is (nil? (:value rejected)))
    (is (empty? (:errors rejected)))
    (is (= (:kb both) (:kb rejected)))
    (is (= (term "(_C1)") (:value combined)))
    (is (holds? (symbol "Cat") (:value classes)))
    (is (holds? (symbol "Dog") (:value classes)))))

(deftest set-unification-keeps-a-failed-pair
  (let [animal (answer "(Animal has (superclasses (Thing)))")
        cat (on animal "(Cat has (superclasses (Animal)))")
        left (on cat "(_C1 has (instance-of (Cat)))")
        both (on left "(_A1 has (instance-of (Animal)))")
        merged (on both "((_C1) && (_A1))")
        classes (frame/get-vals (:kb merged) (symbol "_C1") (symbol "instance-of"))
        dog (answer "(_Cat1 has (instance-of (Cat)))")
        apart (on dog "(_Dog1 has (instance-of (Dog)))")
        kept (on apart "((_Cat1) && (_Dog1))")]
    (is (= (term "(_C1)") (:value merged)))
    (is (= (symbol "_C1") (frame/dereference (:kb merged) (symbol "_A1"))))
    (is (= (term "(Cat)") (:value classes)))
    (is (empty? (:errors kept)))
    (is (= (term "(_Cat1 _Dog1)") (:value kept)))
    (is (= (symbol "_Dog1") (frame/dereference (:kb kept) (symbol "_Dog1"))))))

(deftest a-single-valued-slot-can-keep-a-residue
  (let [slot (answer "(age has (cardinality (N-to-1)))")
        left (on slot "(_P1 has (age (_A)))")
        both (on left "(_P2 has (age (_B)))")
        lazy (on both "(_P1 & _P2)")
        age (frame/get-vals (:kb lazy) (symbol "_P1") (symbol "age"))
        read (on lazy "(the age of _P1)")
        eager-slot (answer "(age has (cardinality (N-to-1)))")
        eager-left (on eager-slot "(_P1 has (age (_A)))")
        eager-both (on eager-left "(_P2 has (age (_B)))")
        eager (on eager-both "(_P1 &! _P2)")
        ground (frame/get-vals (:kb eager) (symbol "_P1") (symbol "age"))]
    (is (= (term "((_A & _B))") (:value age)))
    (is (= (term "(_A)") (:value read)))
    (is (= (symbol "_A") (frame/dereference (:kb read) (symbol "_B"))))
    (is (= (term "(_A)") (:value ground)))
    (is (= (symbol "_A") (frame/dereference (:kb eager) (symbol "_B"))))))

(deftest plus-eager-may-fail-quietly
  (let [left (answer "(_C1 has (instance-of (Cat)))")
        both (on left "(_D1 has (instance-of (Dog)))")
        failed (on both "(_C1 &+! _D1)")]
    (is (nil? (:value failed)))
    (is (empty? (:errors failed)))
    (is (= (:kb both) (:kb failed)))))

(deftest an-inequality-blocks-unification
  (let [left (answer "(_C1 has (instance-of (Cat)))")
        right (on left "(_C2 has (instance-of (Cat)))")
        banned (on right "(_C1 /== _C2)")
        failed (on banned "(_C1 & _C2)")]
    (is (= (term "(_C1)") (:value banned)))
    (is (nil? (:value failed)))
    (is (= 1 (count (:errors failed))))
    (is (some #(re-find #"/==" %) (:errors failed)))
    (is (= (symbol "_C2") (frame/dereference (:kb failed) (symbol "_C2"))))))

(deftest a-stored-value-is-checked-against-must-be-a
  (let [stored (answer "(Pat has (color (red (must-be-a Color))))")
        read (on stored "(the color of Pat)")
        classes (frame/get-vals (:kb read) (symbol "red") (symbol "instance-of"))
        bare (answer "(Pat has (color ((must-be-a Color))))")
        empty (on bare "(the color of Pat)")
        again (frame/get-vals (:kb empty) (symbol "Pat") (symbol "color"))]
    (is (= (term "(red)") (:value read)))
    (is (holds? (symbol "Color") (:value classes)))
    (is (nil? (:value empty)))
    (is (= (term "((must-be-a Color))") (:value again)))))

(deftest cardinality-constraints-do-not-invent-fillers
  (let [cats (answer "(_C1 has (instance-of (Cat)))")
        pair (on cats "(_C2 has (instance-of (Cat)))")
        owner (on pair "(_P has (pets (_C1 _C2 (at-most 1 Cat))))")
        unified (on owner "(the pets of _P)")
        banned (on pair "(_C1 has (/== (_C2)))")
        held (on banned "(_Q has (pets (_C1 _C2 (at-most 1 Cat))))")
        kept (on held "(the pets of _Q)")
        one (on cats "(_R has (pets (_C1 (at-least 2 Cat))))")
        short (on one "(the pets of _R)")
        exact (on cats "(_S has (pets (_C1 (exactly 1 Cat))))")
        counted (on exact "(the pets of _S)")]
    (is (= (term "(_C1)") (:value unified)))
    (is (= (symbol "_C1") (frame/dereference (:kb unified) (symbol "_C2"))))
    (is (some #(re-find #"at-most" %) (:errors kept)))
    (is (holds? (symbol "_C1") (:value kept)))
    (is (holds? (symbol "_C2") (:value kept)))
    (is (= (term "(_C1)") (:value short)))
    (is (empty? (:errors short)))
    (is (= (term "(_C1)") (:value counted)))
    (is (empty? (:errors counted)))))

(deftest ages-on-a-single-valued-slot-fail-the-test
  (let [slot (answer "(age has (cardinality (N-to-1)))")
        left (on slot "(_P1 has (age (23)))")
        both (on left "(_P2 has (age (24)))")
        tested (on both "(_P1 &? _P2)")]
    (is (nil? (:value tested)))
    (is (= (:kb both) (:kb tested)))))

(deftest creation-stays-unported-and-a-test-can-use-an-existential
  (is (= "not-ported" (:error (answer "(a Cat)"))))
  (let [tested (answer "(1 &? (a Thing))")
        combined (answer "(1 & (a Coordinate))")]
    (is (= (term "(t)") (:value tested)))
    (is (not= "not-ported" (:error tested)))
    (is (= (term "(1)") (:value combined)))
    (is (not= "not-ported" (:error combined)))))

(deftest abort-stops-at-the-failed-unification
  (let [before (answer "t")
        failed (engine/evaluate "(1 & 2)" {:kb (:kb before)
                                           :query (assoc (:query before) :on-error :abort)})
        continued (answer "(1 & 2)")]
    (is (nil? (:value failed)))
    (is (seq (:errors failed)))
    (is (= (:kb before) (:kb failed)))
    (is (nil? (:value continued)))
    (is (seq (:errors continued)))))
