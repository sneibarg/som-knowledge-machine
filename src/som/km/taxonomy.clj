(ns som.km.taxonomy
  "Class links stored on the knowledge base.

  Subsumption walks superclasses stored on the class, and the built-in
  links used when a class has none stored. It does not walk rules
  inherited from classes, supersituations, or projection. A class with
  nothing stored and no built-in link has Thing as its superclass. A
  stored list still wins over that fallthrough and over a built-in
  link. A cycle is a broken taxonomy and throws.

  immediate-classes reads instance-of on the instance. An expression
  stored there is not evaluated. A missing instance-of is (Thing).

  The slot walks all-superclasses, all-subclasses, all-classes,
  all-instances, and all-subslots read the stored links and the
  built-in side table. They do not evaluate a slot expression and they
  do not call the interpreter. all-superclasses adds Thing and leaves
  the class itself out. immediate-superclasses adds Thing only when
  nothing is stored and the class is not a built-in link.

  taxonomy-text prints the tree. The walk follows the relation in list
  order. It does not sort by symbol name and it does not follow hash
  order. The interpreter is passed in as km-int."
  (:refer-clojure :exclude [isa?])
  (:require [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private thing (symbol "Thing"))
(def ^:private class-name (symbol "Class"))
(def ^:private string-class (symbol "String"))
(def ^:private integer-class (symbol "Integer"))
(def ^:private number-class (symbol "Number"))
(def ^:private slot-class (symbol "Slot"))
(def ^:private sequence-class (symbol "Sequence"))
(def ^:private bag-class (symbol "Bag"))
(def ^:private pair-class (symbol "Pair"))
(def ^:private triple-class (symbol "Triple"))
(def ^:private function-class (symbol "Function"))
(def ^:private quoted-class (symbol "Quoted-Expression"))
(def ^:private bag-aggregation (symbol "Bag-Aggregation-Slot"))
(def ^:private set-aggregation (symbol "Set-Aggregation-Slot"))

(def ^:private superclass-order
  "Built-in [child parent] links, in the Lisp alist order."
  [[(symbol "Integer") (symbol "Number")]
   [(symbol "Number") thing]
   [(symbol "Pair") sequence-class]
   [(symbol "Triple") sequence-class]
   [(symbol "Sequence") thing]
   [(symbol "Exhaustive-Partition") (symbol "Partition")]
   [(symbol "Partition") thing]
   [(symbol "Set-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Seq-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Bag-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Aggregation-Slot") slot-class]
   [(symbol "Slot") thing]
   [(symbol "Aggregate") thing]
   [(symbol "Class") thing]
   [(symbol "String") thing]
   [(symbol "Boolean") thing]
   [(symbol "Situation") thing]
   [(symbol "Cardinality") thing]
   [(symbol "Fluent-Status") thing]
   [(symbol "Bag") thing]
   [(symbol "Theory") thing]
   [(symbol "Function") thing]])

(def ^:private superclass-links
  (into {} (map (fn [[child parent]] [child [parent]])) superclass-order))

(def ^:private instance-of-links
  {(symbol "t") (symbol "Boolean")
   (symbol "f") (symbol "Boolean")
   (symbol "*Fluent") (symbol "Fluent-Status")
   (symbol "*Non-Fluent") (symbol "Fluent-Status")
   (symbol "*Inertial-Fluent") (symbol "Fluent-Status")
   term/global-situation (symbol "Situation")})

(def ^:private bag-aggregation-slots
  (set (map symbol ["min" "max" "sum" "average" "difference" "product" "quotient"])))

(def ^:private set-aggregation-slots
  (set (map symbol ["first" "second" "third" "fourth" "fifth" "last"
                    "unification" "set-unification" "append" "number"])))

(def structure-classes
  "Classes KM treats as sequence-like when one side is not a frame."
  #{sequence-class pair-class triple-class bag-class})

(defn- chain [items]
  (term/build-list (vec items) nil))

(defn- set-equal?
  "True when the two lists hold the same elements. Order does not matter."
  [left right]
  (let [le (utils/elements left)
        re (utils/elements right)]
    (and (every? #(utils/member? % right) le)
         (every? #(utils/member? % left) re))))

(defn- every-kb-object?
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (kb/kb-object? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- read-global
  [kb frame slot]
  (if (kb/kb-object? frame)
    (frame/get-vals kb frame slot :situation term/global-situation)
    {:kb kb :value nil}))

(defn- drop-self
  "Stored superclasses, or a throw when the class lists itself."
  [class stored]
  (if (and (some? stored) (utils/member? class stored))
    (throw (ex-info (str "You have a cycle in the taxonomy (not allowed)! "
                         class " is its own superclass.")
                    {:class class}))
    stored))

(defn immediate-superclasses
  "The superclasses of class.

  Thing has none. A class description uses its class. A stored list is
  used as it is, and it wins over a built-in link. A built-in link is
  used when nothing is stored. Anything else is (Thing)."
  [kb class]
  (cond
    (utils/eql? class thing) {:kb kb :value nil}
    (kb/the-class? class) {:kb kb :value (chain [(term/car (term/cdr class))])}
    :else
    (let [found (read-global kb class (symbol "superclasses"))
          stored (drop-self class (:value found))]
      (cond
        (some? stored) (assoc found :value stored)
        (contains? superclass-links class)
        {:kb (:kb found) :value (chain (superclass-links class))}
        :else {:kb (:kb found) :value (chain [thing])}))))

(defn is-subclass-of?
  "class when class is target or sits under it. Otherwise nil.

  The walk uses immediate-superclasses. Thing as the child is never a
  subclass of another class. The same class succeeds and returns itself."
  [kb class target]
  (letfn [(walk [kb class path]
            (cond
              (utils/eql? class target) {:kb kb :value class}
              (utils/eql? class thing) {:kb kb :value nil}
              (utils/member? class path)
              (throw (ex-info (str "You have a cycle in the taxonomy (not allowed)! "
                                   (pr-str (into (vec (reverse (utils/elements path))) [class])))
                              {:class class :path path}))
              (and (kb/kb-object? class) (kb/kb-object? target))
              (let [supers (immediate-superclasses kb class)]
                (if (utils/member? target (:value supers))
                  {:kb (:kb supers) :value class}
                  (loop [rest (:value supers)
                         kb (:kb supers)]
                    (if (nil? rest)
                      {:kb kb :value nil}
                      (let [deeper (walk kb (term/car rest) (term/cons-cell class path))]
                        (if (some? (:value deeper))
                          deeper
                          (recur (term/cdr rest) (:kb deeper))))))))
              :else {:kb kb :value nil}))]
    (walk kb class nil)))

(defn all-superclasses0
  "class and the classes stored above it, without Thing.

  Duplicates may remain. A cycle throws."
  [kb class]
  (letfn [(walk [kb class path]
            (cond
              (utils/eql? class thing) {:kb kb :value []}
              (utils/member? class path)
              (throw (ex-info (str "You have a cycle in the taxonomy (not allowed)! "
                                   (pr-str (into (vec (reverse (utils/elements path))) [class])))
                              {:class class :path path}))
              :else
              (let [supers (immediate-superclasses kb class)]
                (loop [rest (:value supers)
                       kb (:kb supers)
                       acc [class]]
                  (if (nil? rest)
                    {:kb kb :value acc}
                    (let [deeper (walk kb (term/car rest) (term/cons-cell class path))]
                      (recur (term/cdr rest)
                             (:kb deeper)
                             (into acc (:value deeper)))))))))]
    (let [walked (walk kb class nil)]
      (assoc walked :value (chain (:value walked))))))

(defn classes-subsume-classes?
  "True when every class in classes1 has a subclass in classes2.

  An empty classes1 succeeds. The walk is is-subclass-of?."
  [kb classes1 classes2]
  (loop [classes1 classes1
         kb kb]
    (if (nil? classes1)
      {:kb kb :value true}
      (let [class1 (term/car classes1)
            found (loop [classes2 classes2
                         kb kb]
                    (if (nil? classes2)
                      {:kb kb :value false}
                      (let [under (is-subclass-of? kb (term/car classes2) class1)]
                        (if (some? (:value under))
                          {:kb (:kb under) :value true}
                          (recur (term/cdr classes2) (:kb under))))))]
        (if (:value found)
          (recur (term/cdr classes1) (:kb found))
          found)))))

(defn remove-subsumers
  "The most specific classes. A superclass is dropped.

  A constraint expression is kept. Order follows the first copy."
  [kb classes]
  (let [nodup (utils/remove-duplicates classes :test utils/eql? :from-end? true)]
    (loop [classes nodup
           kb kb
           acc []]
      (if (nil? classes)
        {:kb kb :value (chain acc)}
        (let [class (term/car classes)
              covered (loop [others nodup
                             kb kb]
                        (if (nil? others)
                          {:kb kb :value false}
                          (let [other (term/car others)]
                            (if (or (utils/eql? other class)
                                    (kb/constraint-expr? class)
                                    (kb/constraint-expr? other))
                              (recur (term/cdr others) kb)
                              (let [under (is-subclass-of? kb other class)]
                                (if (some? (:value under))
                                  {:kb (:kb under) :value true}
                                  (recur (term/cdr others) (:kb under))))))))]
          (recur (term/cdr classes)
                 (:kb covered)
                 (if (:value covered) acc (conj acc class))))))))

(defn remove-subsumees
  "The most general classes. A subclass is dropped.

  A constraint expression is kept. Order follows the input, and a later
  duplicate is dropped."
  [kb classes]
  (let [kept (loop [classes classes
                    kb kb
                    acc []]
               (if (nil? classes)
                 {:kb kb :value acc}
                 (let [class (term/car classes)
                       covered (loop [others classes
                                      kb kb]
                                 (if (nil? others)
                                   {:kb kb :value false}
                                   (let [other (term/car others)]
                                     (if (or (utils/eql? other class)
                                             (kb/constraint-expr? class)
                                             (kb/constraint-expr? other))
                                       (recur (term/cdr others) kb)
                                       (let [under (is-subclass-of? kb class other)]
                                         (if (some? (:value under))
                                           {:kb (:kb under) :value true}
                                           (recur (term/cdr others) (:kb under))))))))]
                   (recur (term/cdr classes)
                          (:kb covered)
                          (if (:value covered) acc (conj acc class))))))]
    (assoc kept :value (utils/remove-duplicates (chain (:value kept))
                                                :test utils/eql?
                                                :from-end? true))))

(defn- drop-constraints-flag
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (chain acc)
      (not (term/cons? values)) values
      (kb/constraint-expr? (term/car values)) (recur (term/cdr values) acc)
      :else (recur (term/cdr values) (conj acc (term/car values))))))

(defn- instance-of-values
  "instance-of values that are frames. Expressions are left unevaluated
  and then ignored. Own definition is included when definitions exist."
  [kb instance]
  (let [defined (if (frame/are-some? kb :definitions)
                  (frame/get-vals kb instance (symbol "instance-of")
                                  :facet (symbol "own-definition")
                                  :situation term/global-situation)
                  {:kb kb :value nil})
        own (frame/get-vals (:kb defined) instance (symbol "instance-of")
                            :facet (symbol "own-properties")
                            :situation term/global-situation)
        combined (utils/append-lists (term/km-list (:value defined) (:value own)))
        plain (if (frame/are-some? (:kb own) :constraints)
                (drop-constraints-flag combined)
                combined)]
    {:kb (:kb own)
     :value (if (and (some? plain) (every-kb-object? plain)) plain nil)}))

(defn immediate-classes
  "The classes of instance from values stored on it.

  A number is Integer or Number. A built-in instance, a built-in slot,
  a string, a quote, and a structured list use their built-in class.
  A frame in the global situation uses its own instance-of. Expressions
  on that slot are not evaluated. Nothing stored means (Thing).
  Supersituations, projection, and the done cache are not consulted.
  Constraints on instance-of are not enforced from here."
  [kb instance]
  (cond
    (integer? instance) {:kb kb :value (chain [integer-class])}
    (number? instance) {:kb kb :value (chain [number-class])}
    (contains? instance-of-links instance)
    {:kb kb :value (chain [(instance-of-links instance)])}
    (contains? bag-aggregation-slots instance) {:kb kb :value (chain [bag-aggregation])}
    (contains? set-aggregation-slots instance) {:kb kb :value (chain [set-aggregation])}
    (frame/built-in-slot? instance) {:kb kb :value (chain [slot-class])}
    (kb/the-class? instance) {:kb kb :value (chain [class-name])}
    (utils/quote? instance) {:kb kb :value (chain [quoted-class])}
    (string? instance) {:kb kb :value (chain [string-class])}
    (kb/km-seq? instance) {:kb kb :value (chain [sequence-class])}
    (kb/km-bag? instance) {:kb kb :value (chain [bag-class])}
    (kb/km-pair-value? instance) {:kb kb :value (chain [pair-class])}
    (kb/km-triple? instance) {:kb kb :value (chain [triple-class])}
    (kb/km-function? instance) {:kb kb :value (chain [function-class])}
    (term/structured-list? instance)
    (immediate-classes kb (term/car (term/cdr instance)))
    (not (kb/kb-object? instance))
    {:kb kb :value (chain [thing])}
    :else
    (let [found (instance-of-values kb instance)]
      {:kb (:kb found)
       :value (or (:value found) (chain [thing]))})))

(defn isa?
  "True when an immediate class of instance is target or sits under it."
  [kb instance target]
  (let [classes (immediate-classes kb instance)]
    (loop [rest (:value classes)
           kb (:kb classes)]
      (if (nil? rest)
        {:kb kb :value false}
        (let [under (is-subclass-of? kb (term/car rest) target)]
          (if (some? (:value under))
            {:kb (:kb under) :value true}
            (recur (term/cdr rest) (:kb under))))))))

(defn- classes-of
  "Classes for a compatible-classes test.

  A passed list is used as it is. Otherwise the instance is classified."
  [kb instance classes]
  (if (some? classes)
    {:kb kb :value classes}
    (immediate-classes kb instance)))

(defn- locked-violation
  "A locked class replaced by a strict subclass, or nil."
  [kb instance classes]
  (if-not (kb/kb-object? instance)
    {:kb kb :value nil}
    (let [primary (read-global kb instance (symbol "locked-instance-of"))
          secondary (if (some? (:value primary))
                     primary
                     (read-global (:kb primary) instance (symbol "locked-instances-of")))
          locked (:value secondary)]
      (if (nil? locked)
        {:kb (:kb secondary) :value nil}
        (loop [classes classes
               kb (:kb secondary)]
          (if (nil? classes)
            {:kb kb :value nil}
            (let [class (term/car classes)
                  hit (loop [locked locked
                             kb kb]
                        (if (nil? locked)
                          {:kb kb :value false}
                          (let [under (is-subclass-of? kb class (term/car locked))]
                            (if (and (some? (:value under))
                                     (not (utils/eql? class (term/car locked))))
                              {:kb (:kb under) :value true}
                              (recur (term/cdr locked) (:kb under))))))]
              (if (:value hit)
                {:kb (:kb hit) :locked (term/car locked) :violator class}
                (recur (term/cdr classes) (:kb hit))))))))))

(defn- member-of-classes
  [kb classes]
  (loop [classes classes
         kb kb
         acc []]
    (if (nil? classes)
      {:kb kb :value acc}
      (let [found (read-global kb (term/car classes) (symbol "member-of"))]
        (recur (term/cdr classes)
               (:kb found)
               (into acc (utils/elements (:value found))))))))

(defn disjoint-class-sets
  "Partitions shared by the classes that are not in both sets.

  Nil means the two sets can be combined. The members of a partition
  are not re-checked. Exhaustive partitions are not checked."
  [kb classes1 classes2]
  (let [above1 (loop [rest classes1
                      kb kb
                      acc []]
                 (if (nil? rest)
                   {:kb kb :value acc}
                   (if (utils/eql? (term/car rest) thing)
                     (recur (term/cdr rest) kb acc)
                     (let [above (all-superclasses0 kb (term/car rest))]
                       (recur (term/cdr rest) (:kb above) (into acc (utils/elements (:value above))))))))
        above2 (loop [rest classes2
                      kb (:kb above1)
                      acc []]
                 (if (nil? rest)
                   {:kb kb :value acc}
                   (if (utils/eql? (term/car rest) thing)
                     (recur (term/cdr rest) kb acc)
                     (let [above (all-superclasses0 kb (term/car rest))]
                       (recur (term/cdr rest) (:kb above) (into acc (utils/elements (:value above))))))))
        left (utils/remove-duplicates (chain (:value above1)) :test utils/eql? :from-end? true)
        right (utils/remove-duplicates (chain (:value above2)) :test utils/eql? :from-end? true)]
    (if (or (utils/equal? left right)
            (every? #(utils/member? % right) (utils/elements left))
            (every? #(utils/member? % left) (utils/elements right)))
      {:kb (:kb above2) :value nil}
      (let [only1 (loop [rest left
                         acc []]
                    (if (nil? rest)
                      (chain acc)
                      (recur (term/cdr rest)
                             (if (utils/member? (term/car rest) right) acc (conj acc (term/car rest))))))
            only2 (loop [rest right
                         acc []]
                    (if (nil? rest)
                      (chain acc)
                      (recur (term/cdr rest)
                             (if (utils/member? (term/car rest) left) acc (conj acc (term/car rest))))))
            parts1 (member-of-classes (:kb above2) only1)
            parts2 (member-of-classes (:kb parts1) only2)
            shared (loop [rest (chain (:value parts1))
                          acc []]
                     (if (nil? rest)
                       (chain acc)
                       (recur (term/cdr rest)
                              (if (utils/member? (term/car rest) (chain (:value parts2)) utils/eql?)
                                (conj acc (term/car rest))
                                acc))))]
        {:kb (:kb parts2) :value shared}))))

(defn compatible-classes?
  "Whether two class lists may be combined.

  :classes-subsumep requires one list to subsume the other. A value that
  is not a frame and whose classes meet Sequence, Pair, Triple, or Bag
  uses that same subsumption test. Otherwise the test is disjoint
  partitions. Locked classes are checked when :check-locked? is set.
  :value is true or false. :partitions and :locked explain a failure."
  [kb & {:keys [instance1 instance2 classes1 classes2 classes-subsumep check-locked?]}]
  (let [left (classes-of kb instance1 classes1)
        right (classes-of (:kb left) instance2 classes2)
        classes1 (:value left)
        classes2 (:value right)
        kb (:kb right)]
    (cond
      (= classes-subsumep :exact-match)
      {:kb kb
       :value (set-equal? classes1 classes2)
       :partitions nil
       :locked nil}

      check-locked?
      (let [locked1 (locked-violation kb instance1 classes2)]
        (if (:locked locked1)
          {:kb (:kb locked1) :value false :partitions nil :locked [(:locked locked1) (:violator locked1)]}
          (let [locked2 (locked-violation (:kb locked1) instance2 classes1)]
            (if (:locked locked2)
              {:kb (:kb locked2) :value false :partitions nil :locked [(:locked locked2) (:violator locked2)]}
              (compatible-classes? (:kb locked2)
                                   :instance1 instance1
                                   :instance2 instance2
                                   :classes1 classes1
                                   :classes2 classes2
                                   :classes-subsumep classes-subsumep
                                   :check-locked? false)))))

      (or classes-subsumep
          (and (some? instance1)
               (not (kb/kb-object? instance1))
               (some structure-classes (utils/elements classes1)))
          (and (some? instance2)
               (not (kb/kb-object? instance2))
               (some structure-classes (utils/elements classes2))))
      (let [forward (classes-subsume-classes? kb classes1 classes2)
            backward (if (:value forward)
                       forward
                       (classes-subsume-classes? (:kb forward) classes2 classes1))]
        {:kb (:kb backward) :value (boolean (:value backward)) :partitions nil :locked nil})

      :else
      (let [disjoint (disjoint-class-sets kb classes1 classes2)]
        {:kb (:kb disjoint)
         :value (nil? (:value disjoint))
         :partitions (:value disjoint)
         :locked nil}))))

(defn classes-subsume-instance?
  "True when classes1 subsumes the immediate classes of instance2.

  proper? also requires that instance2's classes do not subsume classes1."
  [kb instance1 instance2 & {:keys [proper?]}]
  (let [left (immediate-classes kb instance1)
        right (immediate-classes (:kb left) instance2)
        forward (classes-subsume-classes? (:kb right) (:value left) (:value right))]
    (if-not (and (:value forward) proper?)
      forward
      (if (frame/remove-subsumers-slot? (:kb forward) (symbol "instance-of"))
        {:kb (:kb forward)
         :value (not (set-equal? (:value left) (:value right)))}
        (let [back (classes-subsume-classes? (:kb forward) (:value right) (:value left))]
          {:kb (:kb back) :value (not (:value back))})))))

(defn- builtin-subclasses
  "Children of class in the built-in link order."
  [class]
  (loop [links superclass-order
         acc []]
    (if (empty? links)
      (chain acc)
      (let [[child parent] (first links)]
        (recur (rest links)
               (if (utils/eql? parent class) (conj acc child) acc))))))

(defn- unplaced-class?
  [kb concept]
  (and (frame/class? kb concept)
       (not (utils/eql? concept thing))
       (not (contains? superclass-links concept))
       (nil? (:value (read-global kb concept (symbol "superclasses"))))))

(defn- unplaced-classes
  "Classes with no stored superclass and no built-in link, in frame order."
  [kb]
  (chain (filterv #(unplaced-class? kb %) (frame/objects kb))))

(defn- subclasses-of-thing
  "Direct subclasses of Thing.

  Stored subclasses come first. A built-in child of Thing with nothing
  stored of its own is next. An unplaced user class is last."
  [kb]
  (let [stored (read-global kb thing (symbol "subclasses"))
        extras (loop [links superclass-order
                      acc []]
                 (if (empty? links)
                   acc
                   (let [[child parent] (first links)]
                     (recur (rest links)
                            (if (and (utils/eql? parent thing)
                                     (nil? (:value (read-global kb child (symbol "superclasses")))))
                              (conj acc child)
                              acc)))))]
    {:kb (:kb stored)
     :value (utils/remove-duplicates
             (chain (into (into (vec (utils/elements (:value stored))) extras)
                          (utils/elements (unplaced-classes kb))))
             :test utils/eql?)}))

(defn immediate-subclasses
  "The subclasses stored on class.

  Thing uses the stored list, the unused built-in children, and the
  unplaced classes. Another class uses its stored subclasses, or the
  built-in children when nothing is stored. A class listed as its own
  subclass is a broken taxonomy and throws."
  [kb class]
  (if (utils/eql? class thing)
    (subclasses-of-thing kb)
    (let [found (read-global kb class (symbol "subclasses"))
          stored (:value found)]
      (cond
        (and (some? stored) (utils/member? class stored))
        (throw (ex-info (str "You have a cycle in the taxonomy (not allowed)! "
                             class " is its own subclass.")
                        {:class class}))
        (some? stored) found
        :else {:kb (:kb found) :value (builtin-subclasses class)}))))

(defn all-subclasses
  "The classes under class, not including class.

  A later duplicate is kept. A cycle throws."
  [kb class]
  (let [imm (immediate-subclasses kb class)]
    (letfn [(walk [kb class path]
              (cond
                (utils/member? class path utils/eql?)
                (throw (ex-info (str "You have a cycle in the taxonomy (not allowed)! "
                                     class " is its own subclass.")
                                {:class class :path path}))
                :else
                (let [below (immediate-subclasses kb class)]
                  (loop [rest (:value below)
                         kb (:kb below)
                         acc [class]]
                    (if (nil? rest)
                      {:kb kb :value acc}
                      (let [deeper (walk kb (term/car rest)
                                         (term/cons-cell class path))]
                        (recur (term/cdr rest)
                               (:kb deeper)
                               (into acc (:value deeper)))))))))]
      (loop [rest (:value imm)
             kb (:kb imm)
             acc []]
        (if (nil? rest)
          {:kb kb
           :value (utils/remove-duplicates (chain acc) :test utils/eql?)}
          (let [deeper (walk kb (term/car rest) (term/km-list class))]
            (recur (term/cdr rest)
                   (:kb deeper)
                   (into acc (:value deeper)))))))))

(defn all-superclasses
  "Thing and the classes above class. class itself is left out.

  A class with nothing stored above it answers (Thing). Thing answers
  nil. This is the slot walk. all-superclasses0 is the subsumption walk
  and does not add Thing."
  [kb class]
  (if (utils/eql? class thing)
    {:kb kb :value nil}
    (let [supers (immediate-superclasses kb class)
          walked (loop [rest (:value supers)
                        kb (:kb supers)
                        acc []]
                   (if (nil? rest)
                     {:kb kb :value acc}
                     (let [deeper (all-superclasses0 kb (term/car rest))]
                       (recur (term/cdr rest)
                              (:kb deeper)
                              (into acc (utils/elements (:value deeper)))))))]
      {:kb (:kb walked)
       :value (term/cons-cell thing
                              (utils/remove-duplicates (chain (:value walked))
                                                       :test utils/eql?))})))

(defn all-classes
  "Thing and the classes of instance, including the classes above them.

  immediate-classes supplies the classes and does not evaluate an
  expression stored on instance-of."
  [kb instance]
  (let [classes (immediate-classes kb instance)
        walked (loop [rest (:value classes)
                      kb (:kb classes)
                      acc []]
                 (if (nil? rest)
                   {:kb kb :value acc}
                   (let [deeper (all-superclasses0 kb (term/car rest))]
                     (recur (term/cdr rest)
                            (:kb deeper)
                            (into acc (utils/elements (:value deeper)))))))]
    {:kb (:kb walked)
     :value (term/cons-cell thing
                            (utils/remove-duplicates (chain (:value walked))
                                                     :test utils/eql?))}))

(defn immediate-subslots
  "The subslots stored on slot in *Global.

  Nil until a subslots or superslots value has been stored. The slot
  itself is not included. There are no built-in subslot links."
  [kb slot]
  (if-not (frame/are-some? kb :subslots)
    {:kb kb :value nil}
    (read-global kb slot (symbol "subslots"))))

(defn all-subslots
  "slot's subslots and the subslots under those. slot is left out.

  A cycle throws."
  [kb slot]
  (letfn [(walk [kb slot path]
            (if (utils/member? slot path utils/eql?)
              (throw (ex-info (str "You have a cycle in the subslots (not allowed)! "
                                   slot " is its own subslot.")
                              {:slot slot :path path}))
              (let [imm (immediate-subslots kb slot)]
                (loop [rest (:value imm)
                       kb (:kb imm)
                       acc []]
                  (if (nil? rest)
                    {:kb kb :value acc}
                    (let [sub (term/car rest)
                          deeper (walk kb sub (term/cons-cell slot path))]
                      (recur (term/cdr rest)
                             (:kb deeper)
                             (into (conj acc sub) (:value deeper)))))))))]
    (let [walked (walk kb slot nil)]
      (assoc walked :value (chain (:value walked))))))

(defn immediate-superslots
  "The superslots stored on slot in *Global.

  Nil until a subslots or superslots value has been stored."
  [kb slot]
  (if-not (frame/are-some? kb :subslots)
    {:kb kb :value nil}
    (read-global kb slot (symbol "superslots"))))

(defn all-superslots
  "slot's superslots and the superslots above those. slot is left out.

  A cycle throws."
  [kb slot]
  (letfn [(walk [kb slot path]
            (if (utils/member? slot path utils/eql?)
              (throw (ex-info (str "You have a cycle in the superslots (not allowed)! "
                                   slot " is its own superslot.")
                              {:slot slot :path path}))
              (let [imm (immediate-superslots kb slot)]
                (loop [rest (:value imm)
                       kb (:kb imm)
                       acc []]
                  (if (nil? rest)
                    {:kb kb :value acc}
                    (let [sub (term/car rest)
                          deeper (walk kb sub (term/cons-cell slot path))]
                      (recur (term/cdr rest)
                             (:kb deeper)
                             (into (conj acc sub) (:value deeper)))))))))]
    (let [walked (walk kb slot nil)]
      (assoc walked :value (chain (:value walked))))))

(defn- protoinstance?
  [kb instance]
  (frame/protoinstance? kb instance))

(defn- keep-real-instances
  [kb values]
  (let [values (frame/dereference kb values)]
    (loop [values values
           acc []]
      (cond
        (nil? values) (chain acc)
        (not (term/cons? values)) (chain acc)
        (and (kb/kb-object? (term/car values))
             (not (protoinstance? kb (term/car values))))
        (recur (term/cdr values) (conj acc (term/car values)))
        :else (recur (term/cdr values) acc)))))

(defn- builtin-instances
  "t and f for Boolean, and the three fluent statuses. Situation is not
  answered here, so *Global is read from the stored instances."
  [class]
  (cond
    (utils/eql? class (symbol "Boolean"))
    (chain [(symbol "t") (symbol "f")])
    (utils/eql? class (symbol "Fluent-Status"))
    (chain [(symbol "*Fluent") (symbol "*Non-Fluent") (symbol "*Inertial-Fluent")])
    :else nil))

(defn immediate-instances
  "The instances of class stored in *Global.

  Boolean and Fluent-Status use the built-in instances. Every other
  class, including Situation, uses the instances slot. A prototype
  participant is left out. The values are not projected."
  [kb class]
  (if-let [built (builtin-instances class)]
    {:kb kb :value (keep-real-instances kb built)}
    (let [found (read-global kb class (symbol "instances"))]
      {:kb (:kb found) :value (keep-real-instances (:kb found) (:value found))})))

(defn all-instances
  "The instances of class and of the classes under it.

  A later duplicate is kept. Prototype participants are left out.
  The instances slot is read in *Global."
  [kb class]
  (let [subs (all-subclasses kb class)
        classes (term/cons-cell class (:value subs))]
    (loop [rest classes
           kb (:kb subs)
           acc []]
      (if (nil? rest)
        {:kb kb
         :value (utils/remove-duplicates (chain acc) :test utils/eql?)}
        (let [imm (immediate-instances kb (term/car rest))]
          (recur (term/cdr rest)
                 (:kb imm)
                 (into acc (utils/elements (:value imm)))))))))

(def ^:private indent 3)
(def ^:private max-depth 9999)

(defn- add-text
  [state text]
  (assoc state :text (str (:text state) text)))

(defn- member-set
  [values]
  (set (utils/elements values)))

(defn- same-members?
  [left right]
  (= (member-set left) (member-set right)))

(defn- extras
  [original kept]
  (let [have (member-set kept)]
    (filterv #(not (contains? have %)) (utils/elements original))))

(defn- drop-redundant
  "Delete superclass or subclass values that remove-subsumers would drop.

  The check walks every stored frame. A link that is already minimal
  stays, including its order."
  [state slot shrink]
  (loop [names (vec (frame/objects (:kb state)))
         state state]
    (if (empty? names)
      state
      (let [class (first names)
            found (frame/get-vals (:kb state) class slot :query (:query state))
            shrunk (shrink (:kb found) (:value found))
            state (assoc state :kb (:kb shrunk) :query (:query found))]
        (recur (rest names)
               (if (same-members? (:value found) (:value shrunk))
                 state
                 (reduce (fn [state value]
                           (let [deleted (frame/delete-val (:kb state) class slot value
                                                           :query (:query state))]
                             (assoc state :kb (:kb deleted) :query (:query deleted))))
                         state
                         (extras (:value found) (:value shrunk)))))))))

(defn clean-taxonomy
  "Remove a redundant superclass or subclass link.

  The three progress lines are recorded on :text. Partition checking
  is not run. The Lisp prints the same three lines and then checks
  partitions."
  [state]
  (-> state
      (add-text "Removing redundant superclasses...\n")
      (drop-redundant (symbol "superclasses") remove-subsumers)
      (add-text "Removing redundant subclasses...\n")
      (drop-redundant (symbol "subclasses") remove-subsumees)
      (add-text "Computing subclasses of Thing...\n")))

(defn- spaces
  [n]
  (if (pos? n) (apply str (repeat n \space)) ""))

(defn- concept-text
  [kb concept htmlify?]
  (cond
    (and htmlify?
         (kb/kb-object? concept)
         (frame/known-frame? kb concept))
    ""
    (nil? concept) "()"
    :else (print/km-format concept)))

(defn- line-for
  [kb concept tab htmlify? mark]
  (str (case mark
         :instance (str "I" (spaces (dec tab)))
         :unplaced (str "?" (spaces (dec tab)))
         (spaces tab))
       (concept-text kb concept htmlify?)))

(defn- refused-state?
  [state]
  (= "not-ported" (:error state)))

(defn- slot-of
  [state frame relation km-int]
  (km-int state (term/km-list (symbol "the") relation (symbol "of") frame)))

(defn- named-values
  [kb values]
  (filterv #(frame/named-instance? kb %) (utils/elements values)))

(defn- skip-tax-node?
  [kb node relation]
  (and (utils/eql? relation (symbol "instance-of"))
       (or (not (kb/kb-object? node))
           (frame/anonymous-instance? kb node))))

(declare tax-nodes)

(defn- tax-node
  [state node relation km-int htmlify? done tab]
  (let [item (line-for (:kb state) node tab htmlify? nil)
        instances (slot-of state node (symbol "instances") km-int)]
    (if (refused-state? instances)
      {:state instances :lines [item] :done done}
      (let [children (slot-of instances node relation km-int)]
        (if (refused-state? children)
          {:state children :lines [item] :done done}
          (let [named (named-values (:kb children) (:value instances))
                specs (filterv utils/lisp-atom?
                               (utils/elements (:value children)))
                instance-lines (mapv #(line-for (:kb children) %
                                                (+ tab indent) htmlify? :instance)
                                     named)]
            (if (and (seq specs) (contains? done node))
              {:state children
               :lines [item (str (spaces (+ tab indent)) "...")]
               :done done}
              (let [deeper (tax-nodes children specs relation km-int htmlify?
                                      (into (conj done node)
                                            (utils/elements (:value instances)))
                                      (+ tab indent))]
                {:state (:state deeper)
                 :lines (into (into [item] instance-lines) (:lines deeper))
                 :done (:done deeper)}))))))))

(defn- tax-nodes
  [state nodes relation km-int htmlify? done tab]
  (cond
    (or (nil? nodes) (not (or (seq nodes) (term/cons? nodes))))
    {:state state :lines [] :done done}

    (> (quot tab indent) max-depth)
    {:state state
     :lines [(str (spaces (+ tab indent)) "...more...")]
     :done done}

    :else
    (loop [nodes (vec nodes)
           state state
           done done
           lines []]
      (cond
        (empty? nodes) {:state state :lines lines :done done}
        (not (utils/lisp-atom? (first nodes)))
        (recur (rest nodes) state done lines)
        (skip-tax-node? (:kb state) (first nodes) relation)
        (recur (rest nodes) state done lines)
        :else
        (let [one (tax-node state (first nodes) relation km-int htmlify? done tab)]
          (if (refused-state? (:state one))
            {:state (:state one)
             :lines (into lines (:lines one))
             :done (:done one)}
            (recur (rest nodes)
                   (:state one)
                   (:done one)
                   (into lines (:lines one)))))))))

(defn- unplaced-lines
  [state done htmlify?]
  (let [kb (:kb state)
        names (loop [pending (vec (frame/objects kb))
                     seen #{}
                     acc []]
                (if (empty? pending)
                  acc
                  (let [name (frame/dereference kb (first pending))]
                    (recur (rest pending)
                           (conj seen name)
                           (if (or (contains? done name)
                                   (contains? seen name)
                                   (utils/eql? name thing)
                                   (frame/anonymous-instance? kb name))
                             acc
                             (conj acc name))))))]
    (mapv #(line-for kb % indent htmlify? :unplaced) names)))

(defn taxonomy-text
  "The lines of (taxonomy node relation), and the knowledge base.

  Descending subclasses removes redundant links first and records the
  three progress lines. Under Thing those lines are followed by Thing,
  then each subclass in list order, then a named frame the walk did not
  reach. A named instance is marked with I. An unplaced frame is marked
  with ?. Three spaces is one level. htmlify omits a known frame's name
  because htextify returns nothing. The command does not pass htmlify."
  [state node relation km-int & {:keys [htmlify?] :or {htmlify? false}}]
  (let [node (or node thing)
        relation (or relation (symbol "subclasses"))
        state (if (utils/eql? relation (symbol "subclasses"))
                (clean-taxonomy state)
                state)]
    (if (and (utils/eql? node thing)
             (utils/eql? relation (symbol "subclasses")))
      (let [top (immediate-subclasses (:kb state) thing)
            children (filterv #(not (utils/eql? % thing))
                              (utils/elements (:value top)))
            state (assoc state :kb (:kb top))
            walked (tax-nodes state children relation km-int htmlify? #{} indent)]
        (if (refused-state? (:state walked))
          {:state (:state walked) :lines (:lines walked)}
          (let [lines (into (:lines walked)
                            (unplaced-lines (:state walked)
                                            (conj (:done walked) thing)
                                            htmlify?))]
            {:state (reduce (fn [state line]
                              (add-text state (str line "\n")))
                            (add-text (:state walked) "Thing\n")
                            lines)
             :lines (:lines walked)})))
      (let [walked (tax-node state node relation km-int htmlify? #{} 0)]
        (if (refused-state? (:state walked))
          walked
          {:state (reduce (fn [state line]
                            (add-text state (str line "\n")))
                          (:state walked)
                          (:lines walked))
           :lines (:lines walked)})))))
