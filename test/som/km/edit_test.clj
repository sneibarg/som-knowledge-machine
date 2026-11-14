(ns som.km.edit-test
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

(defn- items [values]
  (set (utils/elements values)))

(defn- holds? [item values]
  (contains? (items values) item))

(defn- mentions? [pattern state]
  (some #(re-find pattern %) (:errors state)))

(defn- count-of [result key]
  (or (get-in result [:query key]) 0))

(defn- label [frame]
  (when (term/km-symbol? frame) (term/symbol-name frame)))

(defn- stored [state frame slot]
  (:value (frame/get-vals (:kb state) frame slot)))

(deftest also-has-appends-and-now-has-replaces
  (let [stored (answer "(Fred has (color (red)))")
        added (on stored "(Fred also-has (color (blue)))")
        color (on added "(the color of Fred)")
        again (on color "(Fred also-has (color (red)))")
        same (on again "(the color of Fred)")
        replaced (on same "(Fred now-has (color (green)))")
        green (on replaced "(the color of Fred)")
        loved (on green "(Fred has (loves (Sue)))")
        moved (on loved "(Fred now-has (loves (Mary)))")
        loves (on moved "(the loves of Fred)")
        old (on loves "(the loves-of of Sue)")
        new (on old "(the loves-of of Mary)")
        bad (on new "(Fred also-has (color red))")
        kept (on bad "(the color of Fred)")
        number (answer "(1 also-has (color (red)))")]
    (is (= (term "(Fred)") (:value added)))
    (is (empty? (:errors added)))
    (is (= (term "(red blue)") (:value color)))
    (is (= (term "(red blue)") (:value same)))
    (is (= (term "(green)") (:value green)))
    (is (= (term "(Mary)") (:value loves)))
    (is (nil? (:value old)))
    (is (empty? (:errors old)))
    (is (= (term "(Fred)") (:value new)))
    (is (nil? (:value bad)))
    (is (mentions? #"Bad structure" bad))
    (is (= (term "(green)") (:value kept)))
    (is (nil? (:value number)))
    (is (mentions? #"KB object" number))
    (is (zero? (count-of number :skolems)))))

(deftest also-hasnt-removes-a-value
  (let [stored (answer "(Fred has (color (red blue)))")
        removed (on stored "(Fred also-hasnt (color (red)))")
        color (on removed "(the color of Fred)")
        missing (on color "(Fred also-hasnt (color (green)))")
        still (on missing "(the color of Fred)")
        loved (on still "(Fred has (loves (Sue)))")
        gone (on loved "(Fred also-hasnt (loves (Sue)))")
        loves (on gone "(the loves of Fred)")
        inverse (on loves "(the loves-of of Sue)")
        every (answer "(every Cat also-hasnt (color (red)))")
        number (answer "(1 also-hasnt (color (red)))")]
    (is (= (term "(Fred)") (:value removed)))
    (is (empty? (:errors removed)))
    (is (= (term "(blue)") (:value color)))
    (is (empty? (:errors missing)))
    (is (= (term "(blue)") (:value still)))
    (is (nil? (:value loves)))
    (is (nil? (:value inverse)))
    (is (empty? (:errors inverse)))
    (is (nil? (:value every)))
    (is (mentions? #"Can't use also-hasnt" every))
    (is (mentions? #"every Cat also-hasnt" every))
    (is (nil? (:value number)))
    (is (mentions? #"\(1 also-has \(color \(red\)\)\)" number))))

(deftest an-empty-now-has-classifies
  (let [defined (answer "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
        house (on defined "(_House1 has (instance-of (House)))")
        off (on house "(disable-classification)")
        fred (on off "(Fred has (instance-of (Person)) (owns (_House1)))")
        sue (on fred "(Sue has (instance-of (Person)) (owns (_House1)))")
        enabled (on sue "(enable-classification)")
        now (on enabled "(Fred now-has)")
        untouched (on now "(Sue also-has)")
        added (on untouched "(Pete has (instance-of (Person)))")
        owned (on added "(Pete also-has (owns (_House1)))")]
    (is (holds? (symbol "House-Owner") (stored now (symbol "Fred") (symbol "instance-of"))))
    (is (not (holds? (symbol "House-Owner")
                     (stored untouched (symbol "Sue") (symbol "instance-of")))))
    (is (holds? (symbol "House-Owner")
                (stored owned (symbol "Pete") (symbol "instance-of"))))
    (is (empty? (:errors owned)))))

(deftest now-has-leaves-a-prototype-path-unevaluated
  (let [opened (answer "(a-prototype Cat)")
        made (on opened "(a Cat)")
        name (label (term/car (:value made)))
        added (on made (str "(" name " also-has (color ((a Color))))"))
        color (stored added (symbol name) (symbol "color"))
        replaced (on added (str "(" name " now-has (size ((a Size))))"))
        size (stored replaced (symbol name) (symbol "size"))]
    (is (term/km-symbol? (term/car color)))
    (is (empty? (:errors added)))
    (is (term/cons? (term/car size)))
    (is (= (symbol "a") (term/car (term/car size))))
    (is (empty? (:errors replaced)))))

(deftest position-reads-an-argument-or-a-value
  (let [stored (answer "(Fred has (color (red blue)) (parts ((:pair wing 1) (:pair tail 2))))")
        colors (on stored "(the1 color of Fred)")
        first (on colors "(theNth 1 of (the color of Fred))")
        second (on first "(theNth 2 of (the color of Fred))")
        wings (on second "(the1 parts of Fred)")
        indexes (on wings "(the2 parts of Fred)")
        pair (on indexes "(theNth 1 of (the parts of Fred))")
        missing (on pair "(the3 of (:pair x y))")
        plain (on missing "(the2 of red)")
        named (on plain "(theN 2 of (:pair x y))")
        past (on named "(theNth 5 of (:set x y))")
        bad (on past "(theNth 0 of (a Cat))")
        quiet (answer "(theNth nil of 1)")
        refused (answer "(theNth (showme 1) of (a Cat))")]
    (is (= (term "(red blue)") (:value colors)))
    (is (= (term "(red)") (:value first)))
    (is (= (term "(blue)") (:value second)))
    (is (= (term "(wing tail)") (:value wings)))
    (is (= (term "(1 2)") (:value indexes)))
    (is (= (term "((:pair wing 1))") (:value pair)))
    (is (nil? (:value missing)))
    (is (empty? (:errors missing)))
    (is (nil? (:value plain)))
    (is (empty? (:errors plain)))
    (is (= (term "(y)") (:value named)))
    (is (nil? (:value past)))
    (is (empty? (:errors past)))
    (is (nil? (:value bad)))
    (is (mentions? #"non-negative integer" bad))
    (is (mentions? #"\(the 0 of \(a Cat\)\)" bad))
    (is (= 1 (count-of bad :skolems)))
    (is (nil? (:value quiet)))
    (is (mentions? #"didn't return a value" quiet))
    (is (mentions? #"non-negative integer" quiet))
    (is (= "not-ported" (:error refused)))
    (is (zero? (count-of refused :skolems)))))

(deftest append-and-reverse-build-one-sequence
  (let [joined (answer "(1 append 2)")
        bag (answer "((:bag 1) append (:bag 2))")
        mixed (answer "((:seq 1) append (:bag 2))")
        empty (answer "(nil append (:seq 1))")
        pair (answer "((:pair x 1) append (:seq y))")
        turned (answer "(reverse (:seq 1 2 3))")
        blank (answer "(reverse nil)")
        bagged (answer "(reverse (:bag 1))")]
    (is (= (term "((:seq 1 2))") (:value joined)))
    (is (empty? (:errors joined)))
    (is (= (term "((:bag 1 2))") (:value bag)))
    (is (= (term "((:seq 1 2))") (:value mixed)))
    (is (mentions? #"both sequences or both bags" mixed))
    (is (= (term "((:seq 1))") (:value empty)))
    (is (empty? (:errors empty)))
    (is (= (term "((:seq (:pair x 1) y))") (:value pair)))
    (is (= (term "((:seq 3 2 1))") (:value turned)))
    (is (nil? (:value blank)))
    (is (empty? (:errors blank)))
    (is (nil? (:value bagged)))
    (is (mentions? #"non-sequence" bagged))
    (is (mentions? #"\(:seq <e1> \.\.\. <en>\)" bagged))))
