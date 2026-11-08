(ns som.km.prototype-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
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

(defn- items [values]
  (set (utils/elements values)))

(defn- holds? [item values]
  (contains? (items values) item))

(defn- nth-value [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- mentions? [pattern state]
  (some #(re-find pattern %) (:errors state)))

(defn- label [frame]
  (when (term/km-symbol? frame) (term/symbol-name frame)))

(defn- proto-name [state]
  (label (term/car (:value state))))

(deftest a-cat-outside-prototype-mode-stays-refused
  (let [created (answer "(a Cat)")
        slotted (answer "(a Cat with (color (black)))")
        called (answer "(a Cat called Fred)")]
    (is (= "not-ported" (:error created)))
    (is (= "This form is not ported yet: (a Cat)." (:message created)))
    (is (= "not-ported" (:error slotted)))
    (is (= "This form is not ported yet: (a Cat with (color (black)))." (:message slotted)))
    (is (= "not-ported" (:error called)))))

(deftest a-prototype-supplies-a-slot-and-records-the-clone
  (let [opened (answer "(a-prototype Cat)")
        name (proto-name opened)
        colored (on opened (str "(" name " has (color (black)))"))
        closed (on colored "(end-prototype)")
        cat (on closed "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        from (on color "(the cloned-from of _Cat1)")
        built (on from "(the clone-built-from of _Cat1)")
        defined (frame/definition (:kb closed) (symbol name))
        records (some (fn [[source target]]
                        (when (utils/eql? target (symbol "_Cat1"))
                          (let [found (frame/explanations (:kb color) source)]
                            (when found found))))
                      (:bindings (:kb color)))]
    (is (str/starts-with? name "_Proto"))
    (is (= (term (str "(" name ")")) (:value opened)))
    (is (empty? (:errors opened)))
    (is (= (term (str "(" name ")")) (:value colored)))
    (is (= (term "(t)") (:value closed)))
    (is (empty? (:errors closed)))
    (is (= (term "(black)") (:value color)))
    (is (empty? (:errors color)))
    (is (holds? (symbol name) (:value from)))
    (is (holds? (symbol name) (:value built)))
    (is (frame/classification-enabled? (:kb color)))
    (is (frame/dereferencing-on? (:kb color)))
    (is (= (term (str "((a-prototype Cat) (" name " has (color (black))) (end-prototype))"))
           defined))
    (is (some (fn [record]
                (and (utils/eql? (symbol "color") (nth-value record 1))
                     (utils/eql? (symbol "black") (nth-value record 2))
                     (utils/eql? (symbol "cloned-from")
                                 (term/car (nth-value record 3)))))
              (utils/elements records)))
    (is (not (some #(utils/eql? (symbol "instance-of") (nth-value % 1))
                   (utils/elements records))))))

(deftest a-participant-expression-is-cloned-as-an-instance
  (let [opened (answer "(a-prototype Cat)")
        name (proto-name opened)
        part (on opened (str "(" name " has (color ((a Color))))"))
        closed (on part "(end-prototype)")
        cat (on closed "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        hue (term/car (:value color))
        kind (on color (str "(the instance-of of " (label hue) ")"))
        participants (on part (str "(the prototype-participants of " name ")"))]
    (is (empty? (:errors part)))
    (is (= 2 (count (utils/elements (:value participants)))))
    (is (empty? (:errors color)))
    (is (str/starts-with? (label hue) "_"))
    (is (not (str/starts-with? (label hue) "_Proto")))
    (is (= (term "(Color)") (:value kind)))))

(deftest a-with-form-does-not-evaluate-its-existential
  (let [opened (answer "(a-prototype Cat with (color ((a Color))))")
        closed (on opened "(end-prototype)")
        cat (on closed "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")]
    (is (empty? (:errors opened)))
    (is (= "not-ported" (:error color)))
    (is (re-find #"\(a Color\)" (:message color)))))

(deftest a-second-prototype-is-used-for-its-own-slot
  (let [opened (answer "(a-prototype Cat)")
        name (proto-name opened)
        colored (on opened (str "(" name " has (color (black)))"))
        closed (on colored "(end-prototype)")
        again (on closed "(a-prototype Cat)")
        other (proto-name again)
        sized (on again (str "(" other " has (size (small)))"))
        done (on sized "(end-prototype)")
        cat (on done "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        size (on color "(the size of _Cat1)")]
    (is (= (term "(black)") (:value color)))
    (is (empty? (:errors color)))
    (is (= (term "(small)") (:value size)))
    (is (empty? (:errors size)))))

(deftest a-prototype-of-a-superclass-applies-to-the-subclass
  (let [opened (answer "(a-prototype Wine with (color (red)))")
        closed (on opened "(end-prototype)")
        linked (on closed "(Cat has (superclasses (Wine)))")
        cat (on linked "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")]
    (is (= (term "(red)") (:value color)))
    (is (empty? (:errors color)))))

(deftest a-class-rule-still-applies-beside-a-prototype
  (let [ruled (answer "(every Cat has (color (black)))")
        opened (on ruled "(a-prototype Cat)")
        name (proto-name opened)
        sized (on opened (str "(" name " has (size (small)))"))
        closed (on sized "(end-prototype)")
        cat (on closed "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        size (on color "(the size of _Cat1)")]
    (is (= (term "(black)") (:value color)))
    (is (= (term "(small)") (:value size)))
    (is (empty? (:errors size)))))

(deftest an-earlier-empty-read-stays-empty
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        empty (on cat "(the color of _Cat1)")
        opened (on empty "(a-prototype Cat)")
        name (proto-name opened)
        colored (on opened (str "(" name " has (color (black)))"))
        closed (on colored "(end-prototype)")
        still (on closed "(the color of _Cat1)")]
    (is (nil? (:value empty)))
    (is (nil? (:value still)))
    (is (empty? (:errors still)))))

(deftest querying-a-protoinstance-outside-mode-records-an-error
  (let [opened (answer "(a-prototype Cat)")
        name (proto-name opened)
        colored (on opened (str "(" name " has (color (black)))"))
        closed (on colored "(end-prototype)")
        asked (on closed (str "(the color of " name ")"))
        classes (on closed (str "(the instance-of of " name ")"))
        stored (on closed "(the instances of Cat)")
        all (on stored "(_Cat1 has (instance-of (Cat)))")
        every (on all "(the all-instances of Cat)")]
    (is (= (term "(black)") (:value asked)))
    (is (mentions? #"Attempt to query a protoinstance" asked))
    (is (= (term "(Cat)") (:value classes)))
    (is (empty? (:errors classes)))
    (is (some #(= name (label %)) (utils/elements (:value stored))))
    (is (holds? (symbol "_Cat1") (:value every)))
    (is (not (some #(= name (label %)) (utils/elements (:value every)))))))

(deftest prototype-mode-rejects-a-nested-entry-and-a-local-situation
  (let [opened (answer "(a-prototype Cat)")
        nested (on opened "(a-prototype Cat)")
        base (answer "(the classes of Thing)")
        local (engine/evaluate "(a-prototype Cat)"
                               {:kb (frame/set-situation (:kb base) (symbol "_Sit1"))
                                :query (:query base)})
        theory (engine/evaluate "(a-prototype Cat)"
                                {:kb (assoc (:kb base)
                                            :situation (symbol "_Thy1")
                                            :theories [(symbol "_Thy1")])
                                 :query (:query base)})
        bad (answer "(a-prototype (1 + 2))")
        broken (answer "(a-prototype Cat with (color black))")
        idle (on broken "(end-prototype)")
        plain (answer "(clone Cat)")]
    (is (mentions? #"already in prototype mode" nested))
    (is (mentions? #"end-prototype" nested))
    (is (nil? (:value nested)))
    (is (not= "not-ported" (:error nested)))
    (is (mentions? #"Can't enter prototype mode when in a Situation!" local))
    (is (nil? (:value local)))
    (is (mentions? #"Can't enter prototype mode when in a Theory!" theory))
    (is (mentions? #"Class name must be a symbol or class description" bad))
    (is (nil? (:value bad)))
    (is (nil? (:value broken)))
    (is (mentions? #"Bad structure" broken))
    (is (= (term "(t)") (:value idle)))
    (is (mentions? #"Attempt to clone a non-prototype" plain))
    (is (nil? (:value plain)))))
