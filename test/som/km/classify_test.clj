(ns som.km.classify-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
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

(defn- count-of [result key]
  (or (get-in result [:query key]) 0))

(defn- slot-set [result frame facet]
  (set (keep #(when (term/cons? %) (term/car %))
             (utils/elements
              (:value (frame/get-slotsvals (:kb result) frame :facet facet))))))

(defn- stored-classes [result frame]
  (:value (frame/get-vals (:kb result) frame (symbol "instance-of"))))

(defn- slash [path]
  (str/replace path "\\" "/"))

(deftest a-definition-is-stored-and-indexed
  (let [defined (answer "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
        parents (frame/defined-subclasses (:kb defined) (symbol "Person"))]
    (is (:ok defined))
    (is (= (term "(House-Owner)") (:value defined)))
    (is (empty? (:errors defined)))
    (is (zero? (count-of defined :skolems)))
    (is (zero? (count-of defined :classifications-attempted)))
    (is (zero? (count-of defined :classifications-succeeded)))
    (is (frame/are-some? (:kb defined) :definitions))
    (is (holds? (symbol "House-Owner") parents))
    (is (contains? (slot-set defined (symbol "House-Owner") (symbol "member-definition"))
                   (symbol "owns")))))

(deftest a-definition-without-instance-of-is-an-error
  (let [missing (answer "(every House-Owner has-definition (color (black)))")
        nested (answer "(every House-Owner has-definition (instance-of ((a Person))))")
        bad-class (answer "(every 1 has-definition (instance-of (Thing)))")
        bad-instance (answer "(1 has-definition (instance-of (Thing)))")]
    (is (nil? (:value missing)))
    (is (some #(re-find #"You must specify an `instance-of' slot value" %)
              (:errors missing)))
    (is (nil? (frame/defined-subclasses (:kb missing) (symbol "Thing"))))
    (is (nil? (:value nested)))
    (is (some #(re-find #"atomic class name" %) (:errors nested)))
    (is (zero? (count-of nested :skolems)))
    (is (nil? (:value bad-class)))
    (is (some #(re-find #"isn't/doesn't evaluate to a class name" %)
              (:errors bad-class)))
    (is (nil? (:value bad-instance)))
    (is (some #(re-find #"isn't/doesn't evaluate to a KB object name" %)
              (:errors bad-instance)))
    (is (some #(re-find #"\(every 1 has-definition" %) (:errors bad-instance)))))

(deftest a-matching-instance-gains-the-defined-class
  (let [defined (answer "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
        house (on defined "(_House1 has (instance-of (House)))")
        fred (on house "(Fred has (instance-of (Person)) (owns (_House1)))")
        ruled (on fred "(every House-Owner has (title (owner)))")
        title (on ruled "(the title of Fred)")
        classes (on title "(the instance-of of Fred)")
        sue (on house "(Sue has (instance-of (Person)))")
        sue-classes (on sue "(the instance-of of Sue)")]
    (is (empty? (:errors fred)))
    (is (pos? (count-of fred :classifications-attempted)))
    (is (pos? (count-of fred :classifications-succeeded)))
    (is (= (term "(owner)") (:value title)))
    (is (holds? (symbol "House-Owner") (:value classes)))
    (is (holds? (symbol "Person") (:value classes)))
    (is (empty? (:errors sue)))
    (is (pos? (count-of sue :classifications-attempted)))
    (is (zero? (count-of sue :classifications-succeeded)))
    (is (holds? (symbol "Person") (:value sue-classes)))
    (is (not (holds? (symbol "House-Owner") (:value sue-classes))))))

(deftest now-has-definition-replaces-and-an-empty-one-removes
  (let [defined (answer "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
        replaced (on defined "(every House-Owner now-has-definition (instance-of (Person)) (color (red)))")
        cleared (on replaced "(every House-Owner now-has-definition)")]
    (is (= (term "(House-Owner)") (:value replaced)))
    (is (contains? (slot-set replaced (symbol "House-Owner") (symbol "member-definition"))
                   (symbol "color")))
    (is (not (contains? (slot-set replaced (symbol "House-Owner") (symbol "member-definition"))
                        (symbol "owns"))))
    (is (holds? (symbol "House-Owner")
                (frame/defined-subclasses (:kb replaced) (symbol "Person"))))
    (is (= (term "(House-Owner)") (:value cleared)))
    (is (empty? (slot-set cleared (symbol "House-Owner") (symbol "member-definition"))))
    (is (nil? (frame/defined-subclasses (:kb cleared) (symbol "Person"))))
    (is (frame/are-some? (:kb cleared) :definitions))))

(deftest an-own-definition-unifies-a-later-instance
  (let [house (answer "(_House1 has (instance-of (House)))")
        defined (on house "(Fred has-definition (instance-of (Person)) (owns (_House1)))")
        created (on defined "(a Person with (owns (_House1)))")
        name (term/car (:value created))
        kb (:kb created)]
    (is (= (term "(Fred)") (:value defined)))
    (is (empty? (:errors defined)))
    (is (or (utils/eql? (frame/dereference kb name) (symbol "Fred"))
            (utils/eql? (frame/dereference kb (symbol "Fred")) name)))
    (is (pos? (count-of created :classifications-succeeded)))))

(deftest a-written-unification-reclassifies-and-a-test-does-not
  (let [defined (answer "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
        house (on defined "(_House1 has (instance-of (House)))")
        left (on house "(_Person1 has (instance-of (Person)))")
        right (on left "(_Person2 has (owns (_House1)))")
        joined (on right "(_Person1 & _Person2)")
        ruled (on joined "(every House-Owner has (title (owner)))")
        title (on ruled "(the title of _Person1)")
        probed (on right "(_Person1 &? _Person2)")
        cat (on defined "(a Cat)")
        same (on defined "(1 & 1)")]
    (is (empty? (:errors joined)))
    (is (= (term "(_Person1)") (:value joined)))
    (is (utils/eql? (symbol "_Person1")
                    (frame/dereference (:kb joined) (symbol "_Person2"))))
    (is (holds? (symbol "House-Owner") (stored-classes joined (symbol "_Person1"))))
    (is (pos? (count-of joined :classifications-attempted)))
    (is (pos? (count-of joined :classifications-succeeded)))
    (is (= (term "(owner)") (:value title)))
    (is (zero? (count-of probed :classifications-attempted)))
    (is (zero? (count-of probed :classifications-succeeded)))
    (is (not (holds? (symbol "House-Owner") (stored-classes probed (symbol "_Person1")))))
    (is (zero? (count-of cat :classifications-attempted)))
    (is (zero? (count-of cat :classifications-succeeded)))
    (is (zero? (count-of same :classifications-attempted)))
    (is (zero? (count-of same :classifications-succeeded)))
    (is (zero? (get-in same [:query :unifications] 0)))))

(deftest load-stores-a-definition-and-eval-instances-classifies
  (let [path (.getAbsolutePath (java.io.File/createTempFile "km-step17-" ".km"))
        bare (.getAbsolutePath (java.io.File/createTempFile "km-step17-bare-" ".km"))]
    (try
      (spit path "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))\n"
            :encoding "UTF-8")
      (spit bare "Fred\n" :encoding "UTF-8")
      (let [loaded (answer (str "(load-kb \"" (slash path) "\")"))
            off (answer "(disable-classification)")
            defined (on off "(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))")
            house (on defined "(_House1 has (instance-of (House)))")
            fred (on house "(Fred has (instance-of (Person)) (owns (_House1)))")
            enabled (on fred "(enable-classification)")
            plain (on enabled (str "(load-kb \"" (slash bare) "\")"))
            again (on plain (str "(load-kb \"" (slash bare) "\" :eval-instances t)"))]
        (is (:ok loaded))
        (is (= (term "(t)") (:value loaded)))
        (is (empty? (:errors loaded)))
        (is (holds? (symbol "House-Owner")
                    (frame/defined-subclasses (:kb loaded) (symbol "Person"))))
        (is (not (holds? (symbol "House-Owner") (stored-classes fred (symbol "Fred")))))
        (is (= (term "(t)") (:value plain)))
        (is (not (holds? (symbol "House-Owner") (stored-classes plain (symbol "Fred")))))
        (is (zero? (count-of plain :classifications-succeeded)))
        (is (:ok again))
        (is (holds? (symbol "House-Owner") (stored-classes again (symbol "Fred"))))
        (is (pos? (count-of again :classifications-attempted)))
        (is (pos? (count-of again :classifications-succeeded))))
      (finally
        (io/delete-file path true)
        (io/delete-file bare true)))))

(deftest a-slotted-prototype-applies-through-its-description
  (let [cell (answer "(Cell has (superclasses (Thing)))")
        nucleus (on cell "(Nucleus has (superclasses (Thing)))")
        opened (on nucleus "(a-prototype Euk-cell with (wall (rigid)))")
        root (term/symbol-name (term/car (:value opened)))
        scoped (on opened (str "(" root " has (prototype-scope ((the-class Cell with (has-part ((a Nucleus)))))))"))
        closed (on scoped "(end-prototype)")
        placed (on closed "(_Cell1 has (instance-of (Cell)) (has-part (_Nuc1)))")
        early (on placed "(the instance-of of _Cell1)")
        nuc (on early "(_Nuc1 has (instance-of (Nucleus)))")
        wall (on nuc "(the wall of _Cell1)")
        classes (on wall "(the instance-of of _Cell1)")
        nuclei (on wall "(the instances of Nucleus)")
        bare (on nuc "(_Cell2 has (instance-of (Cell)))")
        empty (on bare "(the wall of _Cell2)")
        bare-classes (on empty "(the instance-of of _Cell2)")
        prior (on nuc "(_Cell3 has (instance-of (Euk-cell)))")
        owned (on prior "(the wall of _Cell3)")]
    (is (empty? (:errors opened)))
    (is (empty? (:errors scoped)))
    (is (not (holds? (symbol "Euk-cell") (:value early))))
    (is (empty? (:errors wall)))
    (is (= (term "(rigid)") (:value wall)))
    (is (holds? (symbol "Euk-cell") (:value classes)))
    (is (holds? (symbol "Cell") (:value classes)))
    (is (pos? (count-of wall :classifications-attempted)))
    (is (pos? (count-of wall :classifications-succeeded)))
    (is (zero? (count-of wall :skolems)))
    (is (holds? (symbol "_Nuc1") (:value nuclei)))
    (is (= 1 (count (utils/elements (:value nuclei)))))
    (is (nil? (:value empty)))
    (is (empty? (:errors empty)))
    (is (not (holds? (symbol "Euk-cell") (:value bare-classes))))
    (is (= (term "(rigid)") (:value owned)))
    (is (empty? (:errors owned)))))

(deftest the-class-answers-the-description
  (let [plain (answer "(the-class Cat)")
        slotted (answer "(the-class Cat with (color (black)))")]
    (is (:ok plain))
    (is (= (term "((the-class Cat))") (:value plain)))
    (is (:ok slotted))
    (is (= (term "((the-class Cat with (color (black))))") (:value slotted)))))

(deftest a-definition-whose-body-is-if-adds-the-class
  (let [defined (answer "(every Colored has-definition (instance-of (Cat)) (color ((if t then red))))")
        cat (on defined "(_Cat1 has (instance-of (Cat)) (color (red)))")
        color (on cat "(the color of _Cat1)")
        classes (on color "(the instance-of of _Cat1)")]
    (is (:ok defined))
    (is (:ok color))
    (is (= (term "(red)") (:value color)))
    (is (holds? (symbol "Colored") (:value classes)))
    (is (empty? (:errors color)))))
