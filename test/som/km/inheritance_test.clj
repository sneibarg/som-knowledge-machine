(ns som.km.inheritance-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.explain :as explain]
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

(defn- items [values]
  (set (utils/elements values)))

(defn- holds? [item values]
  (contains? (items values) item))

(deftest a-class-rule-is-inherited-by-an-instance
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        again (on color "(the color of _Cat1)")
        own (on color "(the color of Cat)")
        tagged (:value (frame/get-vals (:kb ruled) (symbol "Cat") (symbol "color")
                                       :facet (symbol "member-properties")
                                       :dereference? false))]
    (is (= (term "(Cat)") (:value ruled)))
    (is (empty? (:errors ruled)))
    (is (= (term "(black)") (:value color)))
    (is (empty? (:errors color)))
    (is (= (term "(black)") (:value again)))
    (is (nil? (:value own)))
    (is (= (symbol "black") (term/car (term/car tagged))))
    (is (explain/source? (term/car (term/cdr (term/car tagged)))))))

(deftest a-subclass-inherits-and-a-local-value-is-kept
  (let [animal (answer "(every Animal has (color (black)))")
        linked (on animal "(Cat has (superclasses (Animal)))")
        cat (on linked "(every Cat has (color (brown)))")
        inst (on cat "(_Cat1 has (instance-of (Cat)))")
        color (on inst "(the color of _Cat1)")
        local (on color "(_Cat1 has (color (blue)))")
        both (on local "(the color of _Cat1)")
        same (answer "(every Animal has (color (black)))")
        child (on same "(every Cat has (color (black)))")
        under (on child "(Cat has (superclasses (Animal)))")
        one (on under "(_Cat1 has (instance-of (Cat)))")
        once (on one "(the color of _Cat1)")]
    (is (= #{(symbol "black") (symbol "brown")} (items (:value color))))
    (is (empty? (:errors color)))
    (is (= #{(symbol "black") (symbol "brown") (symbol "blue")} (items (:value both))))
    (is (= (term "(black)") (:value once)))))

(deftest case-and-self-are-preserved
  (let [ruled (answer "(every Cat has (color (Black)))")
        named (on ruled "(every Cat has (owner (Self)))")
        cat (on named "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        owner (on color "(the owner of _Cat1)")]
    (is (= (term "(Black)") (:value color)))
    (is (= (term "(_Cat1)") (:value owner)))))

(deftest a-second-rule-is-visible-after-the-cache-is-cleared
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        empty (on cat "(the color of _Cat1)")
        ruled (on empty "(every Cat has (color (black)))")
        color (on ruled "(the color of _Cat1)")
        more (on color "(every Cat has (color (brown)))")
        both (on more "(the color of _Cat1)")
        extra (on both "(every Cat also-has (color (tan)))")
        three (on extra "(the color of _Cat1)")
        now (answer "(every Cat has (color (black)))")
        replaced (on now "(every Cat now-has (color (white)))")
        fresh (on replaced "(_Cat2 has (instance-of (Cat)))")
        white (on fresh "(the color of _Cat2)")]
    (is (nil? (:value empty)))
    (is (= (term "(black)") (:value color)))
    (is (= #{(symbol "black") (symbol "brown")} (items (:value both))))
    (is (= #{(symbol "black") (symbol "brown") (symbol "tan")} (items (:value three))))
    (is (= (term "(white)") (:value white)))))

(deftest a-subslot-value-is-read-with-the-parent-slot
  (let [sub (answer "(color has (subslots (hue)))")
        deeper (on sub "(hue has (subslots (shade)))")
        cat (on deeper "(_Cat1 has (hue (red)))")
        shade (on cat "(_Cat1 has (shade (pink)))")
        local (on shade "(_Cat1 has (color (blue)))")
        color (on local "(the color of _Cat1)")
        direct (on color "(the subslots of color)")
        walked (on color "(the all-subslots of color)")
        above (on color "(the all-superslots of shade)")]
    (is (= #{(symbol "red") (symbol "pink") (symbol "blue")} (items (:value color))))
    (is (= (term "(hue)") (:value direct)))
    (is (= #{(symbol "hue") (symbol "shade")} (items (:value walked))))
    (is (= #{(symbol "hue") (symbol "color")} (items (:value above))))))

(deftest class-walks-add-thing-and-leave-stored-lists-alone
  (let [cat (answer "(every Cat has (color (black)))")
        linked (on cat "(Tabby has (superclasses (Cat)))")
        kitten (on linked "(Kitten has (superclasses (Tabby)))")
        inst (on kitten "(_Cat1 has (instance-of (Cat)))")
        tabby (on inst "(_Tabby1 has (instance-of (Tabby)))")
        classes (on tabby "(the all-classes of _Cat1)")
        supers (on tabby "(the all-superclasses of Cat)")
        bare (on tabby "(the all-superclasses of Animal)")
        number (answer "(the all-classes of 1)")
        integer (answer "(the all-superclasses of Integer)")
        of-one (answer "(the instance-of of 1)")
        named (answer "(the classes of 1)")
        rejected (answer "(the all-superclasses of 1)")
        stored (on tabby "(the subclasses of Cat)")
        under (on tabby "(the all-subclasses of Cat)")
        direct (on tabby "(the instances of Cat)")
        every (on tabby "(the all-instances of Cat)")
        flags (answer "(the all-instances of Boolean)")
        sequence (answer "(the subclasses of Sequence)")
        thing (on cat "(Thing subsumes Cat)")
        broad (on cat "(the all-subclasses of Thing)")]
    (is (= (term "(Thing Cat)") (:value classes)))
    (is (= (term "(Thing)") (:value supers)))
    (is (= (term "(Thing)") (:value bare)))
    (is (= (term "(Thing Integer Number)") (:value number)))
    (is (= (term "(Thing Number)") (:value integer)))
    (is (= (term "(Integer)") (:value of-one)))
    (is (= (term "(Integer)") (:value named)))
    (is (nil? (:value rejected)))
    (is (some #(re-find #"non-kb-object" %) (:errors rejected)))
    (is (= (term "(Tabby)") (:value stored)))
    (is (= #{(symbol "Tabby") (symbol "Kitten")} (items (:value under))))
    (is (= (term "(_Cat1)") (:value direct)))
    (is (= #{(symbol "_Cat1") (symbol "_Tabby1")} (items (:value every))))
    (is (= (term "(t f)") (:value flags)))
    (is (= (term "(Pair Triple)") (:value sequence)))
    (is (= (term "(t)") (:value thing)))
    (is (holds? (symbol "Cat") (:value broad)))))

(deftest a-cycle-in-a-walk-is-a-broken-taxonomy
  (let [looped (answer "(Cat has (subclasses (Cat)))")
        slots (answer "(color has (subslots (hue)))")
        back (on slots "(hue has (subslots (color)))")]
    (is (= (term "(Cat)") (:value looped)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"own subclass"
                          (on looped "(the subclasses of Cat)")))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"own subclass"
                          (on looped "(the all-subclasses of Cat)")))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"own subslot"
                          (on back "(the all-subslots of color)")))))

(deftest an-inherited-constraint-is-checked
  (let [ruled (answer "(every Cat has (color ((mustnt-be-a Dog))))")
        open (on ruled "(red has (instance-of (Dog)))")
        cat (on open "(_Cat1 has (instance-of (Cat)))")
        stored (on cat "(_Cat1 has (color (red)))")
        color (on stored "(the color of _Cat1)")
        plain (answer "(every Cat has (color ((must-be-a Color))))")
        ink (on plain "(_Cat2 has (instance-of (Cat)))")
        painted (on ink "(_Cat2 has (color (ink)))")
        read (on painted "(the color of _Cat2)")
        classes (frame/get-vals (:kb read) (symbol "ink") (symbol "instance-of"))]
    (is (holds? (symbol "red") (:value color)))
    (is (not= "not-ported" (:error color)))
    (is (some #(re-find #"Constraint violation" %) (:errors color)))
    (is (holds? (symbol "ink") (:value read)))
    (is (holds? (symbol "Color") (:value classes)))
    (is (empty? (:errors read)))))

(deftest an-inherited-instance-is-created-and-remembered
  (let [ruled (answer "(every Cat has (friend ((a Cat))))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        friend (on cat "(the friend of _Cat1)")
        again (on friend "(the friend of _Cat1)")
        name (term/car (:value friend))
        classes (on friend (str "(the instance-of of " (term/symbol-name name) ")"))
        defined (answer "(every Cat has-definition (color (black)))")
        why (answer "(why)")
        created (answer "(a Cat)")
        bad (answer "(every 1 has (color (black)))")]
    (is (:ok friend))
    (is (str/starts-with? (term/symbol-name name) "_Cat"))
    (is (not= (symbol "_Cat1") name))
    (is (= (:value friend) (:value again)))
    (is (= (term "(Cat)") (:value classes)))
    (is (frame/already-done? (:kb friend) (symbol "_Cat1") (symbol "friend")
                             term/global-situation))
    (is (not= "not-ported" (:error defined)))
    (is (nil? (:value defined)))
    (is (some #(re-find #"instance-of" %) (:errors defined)))
    (is (nil? (:value why)))
    (is (not= "not-ported" (:error why)))
    (is (re-find #"There are no answers to explain" (:text why)))
    (is (:ok created))
    (is (= (term "(_Cat1)") (:value created)))
    (is (nil? (:value bad)))
    (is (some #(re-find #"class name" %) (:errors bad)))))
