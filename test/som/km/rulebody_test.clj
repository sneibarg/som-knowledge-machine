(ns som.km.rulebody-test
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

(defn- mentions? [pattern state]
  (some #(re-find pattern %) (:errors state)))

(defn- count-of [result key]
  (or (get-in result [:query key]) 0))

(defn- label [frame]
  (when (term/km-symbol? frame) (term/symbol-name frame)))

(deftest if-chooses-a-branch
  (let [then (answer "(if t then 1 else 2)")
        else (answer "(if (not t) then 1 else 2)")
        false-atom (answer "(if f then 1 else 2)")
        missing (answer "(if nil then 1)")
        refused (answer "(if (showme 1) then (a Cat) else (a Dog))")]
    (is (= (term "(1)") (:value then)))
    (is (empty? (:errors then)))
    (is (some? (:statistics then)))
    (is (= (term "(2)") (:value else)))
    (is (= (term "(1)") (:value false-atom)))
    (is (nil? (:value missing)))
    (is (empty? (:errors missing)))
    (is (= "not-ported" (:error refused)))
    (is (zero? (count-of refused :skolems)))))

(deftest quantifiers-walk-a-set
  (let [kept (answer "(allof (:set 1 2 3) where (It > 1))")
        one (answer "(oneof (:set 1 2 3) where (It > 1))")
        mapped (answer "(forall (:set 1 2) (It + 1))")
        must (answer "(allof (:set 1 2) must (It > 0))")
        failed (answer "(allof (:set 1 2) must (It > 1))")
        empty-must (answer "(allof nil must (showme It))")
        empty-forall (answer "(forall nil (showme It))")
        named (answer "(allof ?x in (:set 1 2 3) where (?x > 1))")
        named-map (answer "(forall ?x in (:set 1 2) (?x + 1))")
        nested (answer "(allof2 (:set 1 2) where (It2 > 1))")
        refused (answer "(forall (:set 1) (showme It))")]
    (is (= (term "(2 3)") (:value kept)))
    (is (= (term "(2)") (:value one)))
    (is (= (term "(2 3)") (:value mapped)))
    (is (= (term "(t)") (:value must)))
    (is (nil? (:value failed)))
    (is (empty? (:errors failed)))
    (is (= (term "(t)") (:value empty-must)))
    (is (not= "not-ported" (:error empty-must)))
    (is (nil? (:value empty-forall)))
    (is (not= "not-ported" (:error empty-forall)))
    (is (empty? (:errors empty-forall)))
    (is (= (term "(2 3)") (:value named)))
    (is (= (term "(2 3)") (:value named-map)))
    (is (= (term "(2)") (:value nested)))
    (is (= "not-ported" (:error refused)))))

(deftest theoneof-takes-one-value
  (let [one (answer "(theoneof (:set 1) where t)")
        several (answer "(theoneof (:set 1 2) where t)")
        bad (answer "(forall cat in (:set 1) It)")]
    (is (= (term "(1)") (:value one)))
    (is (empty? (:errors one)))
    (is (= (term "(1)") (:value several)))
    (is (mentions? #"single value" several))
    (is (nil? (:value bad)))
    (is (mentions? #"Second argument" bad))
    (is (mentions? #"\(forall cat in \(:set 1\) It\)" bad))))

(deftest sequences-and-bags-project-one-collection
  (let [kept (answer "(forall-seq (:seq 1 2 3) where (It > 1) (It + 1))")
        nil-kept (answer "(forall-seq (:seq 1) where t nil)")
        nil-seq (term/km-list (term/cons-cell :seq (term/km-list nil)))
        sentinel (answer "(forall-seq (:seq 1) where t to-remove)")
        bag (answer "(forall-bag (:bag 1 2 3) where (It > 1) (It + 1))")
        bag-nil (answer "(forall-bag (:bag 1) where t nil)")
        quiet (answer "(forall-seq nil It)")
        bad (answer "(forall-seq ?x in nil It)")]
    (is (= (term "((:seq 3 4))") (:value kept)))
    (is (= nil-seq (:value nil-kept)))
    (is (= (term "((:seq))") (:value sentinel)))
    (is (= (term "((:bag 3 4))") (:value bag)))
    (is (= (term "((:bag))") (:value bag-nil)))
    (is (nil? (:value quiet)))
    (is (empty? (:errors quiet)))
    (is (nil? (:value bad)))
    (is (mentions? #"single sequence" bad))
    (is (mentions? #"where" bad))
    (is (mentions? #"\?x" bad))))

(deftest called-keeps-tagged-values
  (let [cat (answer "(_Cat1 has (called (Fred)))")
        dog (on cat "(_Dog1 has (called (Sue)))")
        found (on dog "((:set _Cat1 _Dog1) called Fred)")
        same (on dog "(_Cat1 uniquely-called Fred)")
        quiet (on dog "(_Cat1 called Sue)")
        noisy (on quiet "(fail-noisily)")
        missed (on noisy "(_Cat1 called Sue)")
        tagged (answer "(a Cat called Fred)")
        unique (answer "(a Cat uniquely-called Fred)")
        unique-slot (on unique "(the uniquely-called of _Cat1)")
        bad (answer "(a Cat called (a Dog))")
        bad-with (answer "(a Cat called (a Dog) with (color (red)))")
        bad-slots (answer "(a Cat called Fred with (color red))")]
    (is (= (term "(_Cat1)") (:value found)))
    (is (empty? (:errors found)))
    (is (= (term "(_Cat1)") (:value same)))
    (is (nil? (:value quiet)))
    (is (empty? (:errors quiet)))
    (is (nil? (:value missed)))
    (is (mentions? #"called/uniquely-called" missed))
    (is (= (term "(_Cat1)") (:value tagged)))
    (is (frame/are-some? (:kb tagged) :tags))
    (is (frame/are-some? (:kb unique) :tags))
    (is (frame/are-some? (:kb unique) :constraints))
    (is (= (term "(Fred)") (:value unique-slot)))
    (is (nil? (:value bad)))
    (is (zero? (count-of bad :skolems)))
    (is (frame/are-some? (:kb bad) :tags))
    (is (some #(str/includes? % "\n    - The tag") (:errors bad)))
    (is (nil? (:value bad-with)))
    (is (zero? (count-of bad-with :skolems)))
    (is (frame/are-some? (:kb bad-with) :tags))
    (is (some #(str/includes? % "\n   - The tag") (:errors bad-with)))
    (is (nil? (:value bad-slots)))
    (is (zero? (count-of bad-slots :skolems)))
    (is (frame/are-some? (:kb bad-slots) :tags))
    (is (mentions? #"Bad structure" bad-slots))))

(deftest a-class-slot-keeps-values-of-that-class
  (let [red (answer "(_Red1 has (instance-of (Color)))")
        stored (on red "(Fred has (color (_Red1 red)))")
        only (on stored "(the Color color of Fred)")
        all (on stored "(the * color of Fred)")
        wing (on stored "(_Wing1 has (instance-of (Wing)))")
        fuse (on wing "(_Fuse1 has (instance-of (Fuselage)))")
        parts (on fuse "(Fred has (parts (_Wing1 _Fuse1)))")
        walked (on parts "(the Wing (parts *) of Fred)")
        counted (answer "(the Number number of (:set x y))")
        dropped (answer "(the Cat number of (:set x y))")]
    (is (= (term "(_Red1)") (:value only)))
    (is (empty? (:errors only)))
    (is (holds? (symbol "_Red1") (:value all)))
    (is (holds? (symbol "red") (:value all)))
    (is (= (term "(_Wing1)") (:value walked)))
    (is (= (term "(2)") (:value counted)))
    (is (nil? (:value dropped)))
    (is (empty? (:errors dropped)))))

(deftest a-class-rule-can-use-if
  (let [ruled (answer "(every Cat has (label ((if (the color of Self) then named else unnamed))))")
        named (on ruled "(_Cat1 has (instance-of (Cat)) (color (red)))")
        label (on named "(the label of _Cat1)")
        plain (on label "(_Cat2 has (instance-of (Cat)))")
        unlabeled (on plain "(the label of _Cat2)")]
    (is (= (term "(named)") (:value label)))
    (is (empty? (:errors label)))
    (is (= (term "(unnamed)") (:value unlabeled)))
    (is (empty? (:errors unlabeled)))))

(deftest a-called-with-form-expands-paths-in-prototype-mode
  (let [opened (answer "(a-prototype Cat)")
        made (on opened "(a Cat called Fred with (color ((a Color))))")
        name (label (term/car (:value made)))
        stored (:value (frame/get-vals (:kb made) (symbol name) (symbol "color")))
        tag (on made (str "(the called of " name ")"))]
    (is (:ok made))
    (is (str/starts-with? name "_"))
    (is (term/km-symbol? (term/car stored)))
    (is (= (term "(Fred)") (:value tag)))
    (is (frame/are-some? (:kb made) :tags))
    (is (empty? (:errors made)))))
