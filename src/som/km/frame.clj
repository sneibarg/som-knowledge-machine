(ns som.km.frame
  "The frame store.

  A knowledge base is a value the caller holds and passes back in.
  One caller uses a given value at a time. put-vals, get-vals, add-val,
  and delete-val return that value together with the Lisp result.

  A frame has four facets. A facet holds an ordered list of
  (slot (value ...)). In *Global the facet name is the facet. In
  another situation the name is the concatenation curr-situation-facet
  builds, cached on the knowledge base. A non-fluent slot is stored
  in *Global unless the current situation is a theory. A universal
  slot is stored in *Global either way. put-vals stores a fact about
  a prototype participant in *Global. Explanations are stored on the
  frame, oldest first. In *Global the property is explanation. In
  another situation the name is explanation joined to the situation
  name. reset rebuilds the built-in vocabulary.

  The object stack is recorded on the query. Storage does not read it.
  The goal stack is also on the query. reset clears both.
  valset-subsumes-valset? compares structure. When *valset-subsumes*
  holds a function, the store uses that test, so an existential can
  cover an instance. A stored expression is left as data until then."
  (:refer-clojure :exclude [class?])
  (:require [som.km.explain :as explain]
            [som.km.kbutils :as kb]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private own-properties (symbol "own-properties"))
(def ^:private member-properties (symbol "member-properties"))
(def ^:private own-definition (symbol "own-definition"))
(def ^:private member-definition (symbol "member-definition"))

(def facets
  "The four facets, in the Lisp order."
  [own-properties member-properties own-definition member-definition])

(def ^:private facet-set (set facets))
(def ^:private own-facets #{own-properties own-definition})

(def ^:private n-to-n (symbol "N-to-N"))
(def ^:private n-to-1 (symbol "N-to-1"))
(def ^:private one-to-n (symbol "1-to-N"))
(def ^:private one-to-1 (symbol "1-to-1"))
(def ^:private single-cardinalities #{one-to-1 n-to-1})
(def ^:private valid-cardinalities #{one-to-n one-to-1 n-to-1 n-to-n})

(defn- km-symbol
  "A symbol with this name and no namespace.

  A name such as /== contains a slash. The one-argument symbol call
  would treat that slash as a namespace marker."
  [name]
  (symbol nil name))

(defn- syms
  [names]
  (into #{} (map km-symbol) names))

(defn- symv
  [names]
  (mapv km-symbol names))

(def ^:private built-in-single-valued-order
  (symv ["cardinality" "aggregation-function" "ignore-inverses"
         "inverse" "inverse2" "inverse3" "remove-subsumers" "remove-subsumees"
         "inherit-with-overrides" "simple-inherit-with-overrides" "fluent-status"
         "seq-length" "bag-length" "after-situation-of" "prototype-participant-of"
         "combine-values-by-appending" "uniquely-called" "dont-cache-values"
         "nowexists" "abs" "log" "exp" "sqrt" "floor"
         "min" "max" "sum" "average" "difference" "product" "quotient"
         "first" "second" "third" "fourth" "fifth" "last" "unification"
         "set-unification" "append" "number"]))

(def ^:private built-in-multivalued-order
  (symv ["domain" "range" "element-type" "element-type-of"
         "superclasses" "subclasses" "instances" "instance-of"
         "locked-instance-of" "locked-instances" "add-list" "del-list"
         "pcs-list" "ncs-list" "supersituations" "subsituations" "subslots"
         "superslots" "slots-to-opportunistically-evaluate" "prev-situation"
         "next-situation" "block-projection-for" "before-situation-of"
         "before-situation" "after-situation" "domain-of" "range-of"
         "fluent-status-of" "called" "prototype-participants" "prototypes"
         "prototype-of" "cloned-from" "clone-built-from" "has-built-clones"
         "has-clones" "prototype-scope" "name" "elements" "member-of" "members"
         "classes" "all-instances" "all-prototypes" "all-classes"
         "all-superclasses" "all-subclasses" "all-supersituations" "all-subslots"
         "most-specific" "most-general" "assertions" "==" "/==" "<" ">"]))

(def ^:private built-in-single-valued (set built-in-single-valued-order))

(def ^:private built-in-multivalued (set built-in-multivalued-order))

(def ^:private built-in-slot-order
  (into built-in-single-valued-order built-in-multivalued-order))

(def ^:private bag-aggregation-slots
  (syms ["min" "max" "sum" "average" "difference" "product" "quotient"]))

(def ^:private set-aggregation-slots
  (syms ["first" "second" "third" "fourth" "fifth" "last"
         "unification" "set-unification" "append" "number"]))

(def ^:private built-in-slots
  (into built-in-single-valued built-in-multivalued))

(def ^:private built-in-classes
  (syms ["Integer" "Number" "Thing" "Slot" "Aggregate" "Aggregation-Slot"
         "Seq-Aggregation-Slot" "Bag-Aggregation-Slot" "Set-Aggregation-Slot"
         "String" "Class" "Situation" "Boolean" "Partition"
         "Exhaustive-Partition" "Cardinality" "Fluent-Status"
         "Pair" "Triple" "Sequence" "Bag" "Theory" "Function"]))

(def ^:private built-in-instances
  (into (syms ["1-to-N" "1-to-1" "N-to-1" "N-to-N"
               "*Fluent" "*Inertial-Fluent" "*Non-Fluent" "t" "f" "T"])
        [term/global-situation]))

(def ^:private built-in-frames
  (into (into built-in-slots built-in-classes) built-in-instances))

(def ^:private fluent-status-fluent (symbol "*Fluent"))
(def ^:private fluent-status-inertial (symbol "*Inertial-Fluent"))
(def ^:private fluent-status-non (symbol "*Non-Fluent"))
(def ^:private valid-fluent-statuses
  #{fluent-status-fluent fluent-status-inertial fluent-status-non})

(def ^:private nonfluent-instances-classes
  (syms ["Situation" "Slot" "Partition" "Theory"]))

(def ^:private superclass-links
  [[(symbol "Integer") (symbol "Number")]
   [(symbol "Number") (symbol "Thing")]
   [(symbol "Pair") (symbol "Sequence")]
   [(symbol "Triple") (symbol "Sequence")]
   [(symbol "Sequence") (symbol "Thing")]
   [(symbol "Exhaustive-Partition") (symbol "Partition")]
   [(symbol "Partition") (symbol "Thing")]
   [(symbol "Set-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Seq-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Bag-Aggregation-Slot") (symbol "Aggregation-Slot")]
   [(symbol "Aggregation-Slot") (symbol "Slot")]
   [(symbol "Slot") (symbol "Thing")]
   [(symbol "Aggregate") (symbol "Thing")]
   [(symbol "Class") (symbol "Thing")]
   [(symbol "String") (symbol "Thing")]
   [(symbol "Boolean") (symbol "Thing")]
   [(symbol "Situation") (symbol "Thing")]
   [(symbol "Cardinality") (symbol "Thing")]
   [(symbol "Fluent-Status") (symbol "Thing")]
   [(symbol "Bag") (symbol "Thing")]
   [(symbol "Theory") (symbol "Thing")]
   [(symbol "Function") (symbol "Thing")]])

(def ^:private instance-of-links
  [[(symbol "t") (symbol "Boolean")]
   [(symbol "f") (symbol "Boolean")]
   [fluent-status-fluent (symbol "Fluent-Status")]
   [fluent-status-non (symbol "Fluent-Status")]
   [fluent-status-inertial (symbol "Fluent-Status")]
   [term/global-situation (symbol "Situation")]])

(def ^:private unlinked-instances
  (symv ["1-to-N" "1-to-1" "N-to-1" "N-to-N" "T"]))

(defn- runtime-defaults
  []
  {:default-fluent-status fluent-status-fluent
   :instance-of-is-fluent? false
   :are-some-definitions? false
   :are-some-prototype-definitions? false
   :are-some-prototypes? false
   :are-some-subslots? false
   :are-some-constraints? false
   :are-some-tags? false
   :are-some-defaults? false
   :classes-using-assertions nil
   :visible-theories nil
   :curr-prototype nil
   :situations-mode? false
   :classification-enabled? true
   :prototype-classification-enabled? true
   :max-padding-instances 0
   :use-prototypes? true
   :recursive-prototypes? false
   :eagerly-unify-prototypes? true
   :record-explanations? true
   :record-explanations-for-clones? true
   :add-cloned-from-links? true
   :propagate-explanations? true
   :dereference-explanations-during-cloning? true
   :logging? false
   :logging-creations? false
   :internal-logging? false
   :slot-checking-enabled? false
   :verbose-number-to-text? false
   :output-precision 3
   :default-km-behavior-for-expand-text? true
   :justify-leaves? false
   :developer-mode? false
   :trace? false
   :interactive-trace? false
   :suspended-trace nil
   :trace-classify? false
   :trace-unify? false
   :trace-subsumes? false
   :trace-constraints? false
   :trace-other-situations? false
   :trace-to-file? false
   :trace-file "%trace.km"
   :show-comments? true
   :spypoints []
   :reset-statistics-enabled? true
   :inference-report-frequency nil
   :profile-cpu {}
   :profile-entries {}
   :profile-starts {}
   :kb-accesses 0})

(def ^:private are-some-flags
  {:definitions :are-some-definitions?
   :prototype-definitions :are-some-prototype-definitions?
   :prototypes :are-some-prototypes?
   :subslots :are-some-subslots?
   :constraints :are-some-constraints?
   :tags :are-some-tags?
   :defaults :are-some-defaults?})

(def ^:private remove-subsumer-slots
  (syms ["instance-of" "classes" "superclasses" "member-type"]))

(def ^:private remove-subsumee-slots
  (syms ["subclasses" "prototype-of" "domain" "range"]))

(def ^:private non-inverse-slots
  (into (syms ["prototype-scope" "cardinality" "aggregation-function"
               "add-list" "del-list" "pcs-list" "ncs-list"
               "inherit-with-overrides" "simple-inherit-with-overrides"
               "called" "uniquely-called" "arity" "nowexists"
               "block-projection-for" "remove-subsumers" "remove-subsumees"
               "combine-values-by-appending" "dont-cache-values"
               "ignore-inverses" "name" "=="])
        [:incomplete]))

(def ^:private appending-slots
  (syms [">" "<" "/==" "==" "add-list" "del-list" "pcs-list" "ncs-list"
         "prototype-scope" "domain" "range" "cardinality" "arity"
         "slots-to-opportunistically-evaluate" "locked-instances"
         "locked-instance-of" "inverse" "inverse2" "inverse3"
         "inherit-with-overrides" "simple-inherit-with-overrides"
         "superclasses" "subclasses" "instances" "instance-of"
         "supersituations" "members" "member-of" "prototypes" "prototypes-of"
         "prototype-participants" "prototype-participant-of"
         "clone-built-from" "has-built-clones" "cloned-from" "has-clones"
         "domain-of" "range-of" "remove-subsumers" "remove-subsumees"
         "subsituations" "subslots" "superslots" "id"
         "combine-values-by-appending" "dont-cache-values" "ignore-inverses"
         "fluent-status" "called" "uniquely-called" "block-projection-for"]))

(def ^:private built-in-inverses
  (into {} (map (fn [[left right]] [(km-symbol left) (km-symbol right)]))
        [["inverse" "inverse"] ["inverse2" "inverse2"] ["inverse3" "inverse3"]
         ["instances" "instance-of"] ["instance-of" "instances"]
         ["locked-instance-of" "locked-instances"]
         ["locked-instances" "locked-instance-of"]
         ["subslots" "superslots"] ["superslots" "subslots"]
         ["subclasses" "superclasses"] ["superclasses" "subclasses"]
         ["supersituations" "subsituations"]
         ["subsituations" "supersituations"]
         ["prototypes" "prototype-of"] ["prototype-of" "prototypes"]
         ["members" "member-of"] ["member-of" "members"]
         ["prototype-participants" "prototype-participant-of"]
         ["prototype-participant-of" "prototype-participants"]
         ["next-situation" "prev-situation"] ["prev-situation" "next-situation"]
         ["cloned-from" "has-clones"] ["has-clones" "cloned-from"]
         ["clone-built-from" "has-built-clones"]
         ["has-built-clones" "clone-built-from"]
         ["/==" "/=="]]))

(def ^:private built-in-inverse2s
  (into {} (map (fn [[left right]] [(symbol left) (symbol right)]))
        [["next-situation" "after-situation"]
         ["after-situation" "next-situation"]
         ["prev-situation" "before-situation"]
         ["before-situation" "prev-situation"]]))

(def ^:private inverse-suffix "-of")
(def ^:private self-symbol (symbol "Self"))
(def ^:private prototype-scope (symbol "prototype-scope"))
(def ^:private overwriting (symbol "overwriting"))
(def ^:private appending (symbol "appending"))

(def empty-query
  "A query whose object stack and goal stack are empty.

  Storage does not read either stack. The goal stack is consulted by
  som.km.stack."
  {:obj-stack nil
   :goal-stack nil})

(defn knowledge-base
  "An empty knowledge base.

  The current situation is *Global. The gensym counter is 0.
  Dereferencing is on, ununification stays off, and inverses are
  installed. The object stack is not active. t is not recorded on that
  stack. The built-in vocabulary is not installed yet: reset does that.
  The default fluent status is *Fluent, and the optimization flags are
  clear. Logging and creation logging start off. Slot checking starts
  off."
  []
  {:frames {}
   :frame-order []
   :bindings {}
   :counter 0
   :situation term/global-situation
   :situations [term/global-situation]
   :theories []
   :facet-cache {}
   :deleted []
   :dereferencing-on? true
   :allow-ununify? false
   :installing-inverses? true
   :active-obj-stack? false
   :unstackable-instances (term/km-list (symbol "t"))
   :runtime (runtime-defaults)})

(defn- result
  [kb value query]
  {:kb kb :value value :query query})

(defn- dotted!
  [tail]
  (throw (ex-info "This list is dotted." {:tail tail})))

(defn- remember-name
  [names value]
  (if (some #(utils/eql? % value) names) names (conj names value)))

(defn situations
  "Situation names, with *Global first and later names in the order they were entered."
  [kb]
  (:situations kb))

(defn theories
  "Theory names, in the order they were entered."
  [kb]
  (:theories kb))

(defn gensym-counter
  "The counter create-instance-name advances. A fresh knowledge base starts at 0."
  [kb]
  (:counter kb))

(defn allow-ununify?
  "Ununification stays off. This is *allow-ununify*."
  [kb]
  (boolean (:allow-ununify? kb)))

(defn dereferencing-on?
  "True when dereference follows bindings."
  [kb]
  (boolean (:dereferencing-on? kb)))

(defn set-dereferencing
  "Turn following of bindings on or off for later calls on this knowledge base."
  [kb on?]
  (assoc kb :dereferencing-on? (boolean on?)))

(defn set-active-obj-stack
  "Record every asserted frame and value on the query when on? is true.

  The flag starts off. Storage still does not read the stack."
  [kb on?]
  (assoc kb :active-obj-stack? (boolean on?)))

(defn unstackable-instances
  "Instances that are not recorded on the object stack.

  The list starts as (t). This is *unstackable-kb-instances*."
  [kb]
  (:unstackable-instances kb))

(defn set-unstackable-instances
  "Replace the instances that are not recorded on the object stack.

  reset keeps this list. The Lisp variable is not cleared by reset-kb."
  [kb instances]
  (assoc kb :unstackable-instances instances))

(defn set-installing-inverses
  "Turn automatic inverse links on or off."
  [kb on?]
  (assoc kb :installing-inverses? (boolean on?)))

(defn set-situation
  "Make situation current and remember its name.

  theory? records the name as a theory. This does not evaluate a body.
  A situation name is a knowledge-base object."
  [kb situation & {:keys [theory?]}]
  (when-not (kb/kb-object? situation)
    (throw (ex-info "A situation name is a knowledge-base object."
                    {:situation situation})))
  (if theory?
    (-> kb
        (assoc :situation situation)
        (update :theories remember-name situation))
    (-> kb
        (assoc :situation situation)
        (update :situations remember-name situation))))

(declare dereference fluent? universal-slot? obj-stack get-vals)

(defn current-situation
  "The situation in force, after following a binding."
  [kb]
  (dereference kb (:situation kb)))

(defn theory-situation?
  "True when situation is a theory.

  An entered theory is on :theories. A situation whose instance-of in
  *Global includes Theory is a theory too. The read passes *Global, so
  this does not call target-situation and a non-fluent lookup cannot
  recurse through this test."
  [kb situation]
  (or (some #(utils/eql? situation %) (:theories kb))
      (and (kb/kb-object? situation)
           (utils/member? (symbol "Theory")
                          (:value (get-vals kb situation (symbol "instance-of")
                                            :situation term/global-situation
                                            :dereference? false))))))

(defn situations-mode?
  "True after a non-global situation has been entered.

  The flag is sticky. reset builds a fresh runtime and turns it off.
  Entering a theory does not turn it on."
  [kb]
  (boolean (:situations-mode? (:runtime kb))))

(defn set-situations-mode
  "Turn situations mode on. It is not turned off again."
  [kb]
  (assoc-in kb [:runtime :situations-mode?] true))

(defn visible-theories
  "Theories currently visible, newest first. Nil when none are."
  [kb]
  (:visible-theories (:runtime kb)))

(defn set-visible-theories
  "Replace the visible theories. Nil means none are visible."
  [kb theories]
  (assoc-in kb [:runtime :visible-theories] theories))

(defn local-situation?
  "True in a situation that is not *Global and not a theory."
  [kb]
  (let [situation (current-situation kb)]
    (and (not (utils/eql? situation term/global-situation))
         (not (theory-situation? kb situation)))))

(defn local-theory?
  "True when the current situation is a theory."
  [kb]
  (let [situation (current-situation kb)]
    (and (not (utils/eql? situation term/global-situation))
         (theory-situation? kb situation))))

(defn- nonfluent-instances-class?
  "True when a value is Situation, Slot, Partition, or Theory.

  is-subclass-of would also accept a subclass. That walk waits for the
  taxonomy."
  [values]
  (loop [values values]
    (cond
      (nil? values) false
      (not (term/cons? values)) (dotted! values)
      (contains? nonfluent-instances-classes (term/car values)) true
      :else (recur (term/cdr values)))))

(defn target-situation
  "The situation a slot is stored in.

  The global situation stays the global situation. A universal slot is
  stored there, including inside a theory. A non-universal non-fluent
  is stored there too, unless the situation is a theory. vals is used
  only for instance-of:
  an instance of Situation, Slot, Partition, or Theory is stored in
  *Global once instance-of itself is fluent. put-vals, get-vals, add-val,
  and delete-val call this without vals. add-slotsvals passes vals."
  [kb situation instance slot & [vals]]
  (cond
    (utils/eql? situation term/global-situation) term/global-situation
    (and (some? slot) (universal-slot? kb slot)) term/global-situation
    (and (some? slot)
         (not (fluent? kb slot))
         (not (theory-situation? kb situation)))
    term/global-situation
    (and (utils/eql? slot (symbol "instance-of"))
         (nonfluent-instances-class? vals))
    term/global-situation
    (and (utils/eql? slot (symbol "instances"))
         (contains? nonfluent-instances-classes instance))
    term/global-situation
    :else situation))

(defn- chosen-situation
  [kb situation instance slot]
  (if (nil? situation)
    (target-situation kb (current-situation kb) instance slot)
    situation))

(declare class? slot?)

(def ^:private unstackable-instance (symbol "t"))

(defn- stackable?
  "A frame is worth recording on the object stack.

  Classes, slots, and the unstackable instances are left off. The
  unstackable list starts as (t). This is stackable."
  [kb frame]
  (and (kb/kb-object? frame)
       (not (class? kb frame))
       (not (slot? kb frame))
       (not (utils/member? frame
                            (get kb :unstackable-instances
                                 (term/km-list unstackable-instance))))))

(defn push-to-obj-stack
  "Record frame on the front of the query's object stack.

  A frame already on the stack is left where it is. Classes, slots, and
  the unstackable instances are not recorded. t starts on that list.
  Storage does not read this stack. obj-stack follows bindings when
  the stack is read."
  [kb query frame]
  (let [query (or query empty-query)]
    (if (and (stackable? kb frame)
             (not (utils/member? frame (:obj-stack query))))
      (update query :obj-stack #(term/cons-cell frame %))
      query)))

(defn- push-all
  [kb query frames]
  (loop [frames frames
         query query]
    (cond
      (nil? frames) query
      (term/cons? frames)
      (recur (term/cdr frames) (push-to-obj-stack kb query (term/car frames)))
      :else (dotted! frames))))

(defn- remove-from-stack
  [kb query frame]
  (let [read (obj-stack kb query)]
    (update (:query read) :obj-stack #(utils/remove-items frame %))))

(defn- known-raw?
  [kb frame]
  (contains? (:frames kb) frame))

(defn known-frame?
  "True when this knowledge base has a frame of this name.

  Membership is the whole test. A built-in name such as Thing is not a
  frame until reset installs the vocabulary. A binding alone does not
  make a name known. A name that is not a knowledge-base object is an
  error."
  [kb frame]
  (if (kb/kb-object? frame)
    (known-raw? kb frame)
    (throw (ex-info (str frame " is not a knowledge-base object.")
                    {:frame frame}))))

(defn objects
  "Known frame names, in the order they were first stored.

  A frame that only holds a binding is included when it was stored
  first. The Lisp walks a hash table, so its order is not this order."
  [kb]
  (:frame-order kb))

(declare get-slotsvals vals-in)

(defn note-done
  "Record that slot was computed for frame in situation.

  The pair is stored on the frame. A frame that is not already stored
  is left alone, so this does not create a partial frame. A repeated
  pair is stored once. Inheritance and prototypes are both in force,
  so a computed answer is recorded."
  [kb frame slot situation]
  (if-not (and (kb/kb-object? frame) (known-raw? kb frame))
    kb
    (let [pair (term/km-list slot situation)
          done (get-in kb [:frames frame :done])]
      (if (utils/member? pair done utils/equal?)
        kb
        (assoc-in kb [:frames frame :done] (term/cons-cell pair done))))))

(defn already-done?
  "True when note-done recorded slot for frame in situation."
  [kb frame slot situation]
  (and (kb/kb-object? frame)
       (known-raw? kb frame)
       (utils/member? (term/km-list slot situation)
                      (get-in kb [:frames frame :done])
                      utils/equal?)))

(defn- drop-done-slot
  [done slot]
  (loop [done done
         acc []]
    (cond
      (nil? done) (term/build-list acc nil)
      (not (term/cons? done)) (term/build-list acc nil)
      (and (term/cons? (term/car done))
           (utils/eql? (term/car (term/car done)) slot))
      (recur (term/cdr done) acc)
      :else (recur (term/cdr done) (conj acc (term/car done))))))

(defn- clear-related-done
  "Clear the cache on frames named by frame's global slot values.

  A new instance-of can change an answer that was cached on a value."
  [kb frame]
  (let [slots (:value (get-slotsvals kb frame
                                     :situation term/global-situation
                                     :dereference? false))]
    (loop [pairs slots
           kb kb]
      (cond
        (nil? pairs) kb
        (not (term/cons? pairs)) kb
        :else
        (recur (term/cdr pairs)
               (loop [values (vals-in (term/car pairs))
                      kb kb]
                 (cond
                   (nil? values) kb
                   (not (term/cons? values)) kb
                   (and (kb/kb-object? (term/car values))
                        (known-raw? kb (term/car values)))
                   (recur (term/cdr values)
                          (update-in kb [:frames (term/car values)] dissoc :done))
                   :else (recur (term/cdr values) kb))))))))

(defn un-done
  "Drop cached answers on frame.

  No slot clears every cached slot. A slot clears the pairs for that
  slot. instance-of also clears every cached slot, and the cache on
  frames named by the global values of frame. A frame that is not
  stored is left alone."
  [kb frame & {:keys [slot]}]
  (cond
    (not (and (kb/kb-object? frame) (known-raw? kb frame))) kb
    (utils/eql? slot (symbol "instance-of"))
    (clear-related-done (update-in kb [:frames frame] dissoc :done) frame)
    (nil? slot)
    (update-in kb [:frames frame] dissoc :done)
    :else
    (assoc-in kb [:frames frame :done]
              (drop-done-slot (get-in kb [:frames frame :done]) slot))))

(defn reset-done
  "Clear the done cache on every stored frame.

  Seeing or hiding a theory changes answers that were already computed."
  [kb]
  (reduce (fn [kb frame]
            (if (contains? (:frames kb) frame)
              (update-in kb [:frames frame] dissoc :done)
              kb))
          kb
          (:frame-order kb)))

(defn deleted-frames
  "Frames delete-frame has removed, oldest first."
  [kb]
  (:deleted kb))

(defn built-in-concept?
  "True for a built-in class, slot, or instance name.

  The name is not a frame until reset installs the vocabulary."
  [concept]
  (contains? built-in-frames concept))

(defn built-in-slot?
  "True for a slot in the built-in slot list."
  [slot]
  (contains? built-in-slots slot))

(defn built-in-concept-type
  "The built-in kind of concept, or nil.

  write-frame uses this label: \"single-valued slot\", \"multivalued
  slot\", \"class\", or \"instance\"."
  [concept]
  (cond
    (contains? built-in-single-valued concept) "single-valued slot"
    (contains? built-in-multivalued concept) "multivalued slot"
    (contains? built-in-classes concept) "class"
    (contains? built-in-instances concept) "instance"))

(defn- frame-record
  [kb frame]
  (get (:frames kb) frame))

(defn- store-frame
  [kb frame record]
  (let [known? (known-raw? kb frame)
        stored (cond-> (assoc-in kb [:frames frame] record)
                 (not known?) (update :frame-order conj frame))]
    (if (and (not known?)
             (kb/kb-object? frame)
             (get-in stored [:runtime :logging-creations?]))
      (assoc stored :creations (into [frame] (or (:creations stored) [])))
      stored)))

(def explanation-facet
  "The property explanations use in *Global. Another situation joins this name to the situation name."
  (symbol "explanation"))

(defn- nth-value
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn explanation-property
  "The symbol explanations are stored under in situation.

  *Global uses explanation. Another situation joins that name to the
  situation name, the same way a facet is joined. The joined name is
  cached, so a later call returns the same symbol."
  [kb situation]
  (cond
    (utils/eql? situation term/global-situation)
    (result kb explanation-facet empty-query)

    :else
    (if-let [cached (get-in kb [:facet-cache explanation-facet situation])]
      (result kb cached empty-query)
      (let [joined (symbol (str "explanation" (term/symbol-name situation)))]
        (result (assoc-in kb [:facet-cache explanation-facet situation] joined)
                joined
                empty-query)))))

(defn- explanation-vector
  [record property]
  (let [stored (get-in record [:explanations property])]
    (if (vector? stored) stored [])))

(defn explanations
  "The explanation records on frame in situation, oldest first.

  Each record is (instance slot value explanation). The default
  situation is *Global. A frame with none answers nil. Another
  situation is a separate property and is not included here. The Lisp
  keeps the newest record first."
  [kb frame & {:keys [situation] :or {situation term/global-situation}}]
  (let [named (explanation-property kb situation)]
    (term/build-list (explanation-vector (frame-record (:kb named) frame)
                                         (:value named))
                     nil)))

(declare protoinstance?)

(defn record-explanation
  "Append one explanation record when it is not already stored.

  The record is (instance slot value explanation). A duplicate under
  equal? is left as it is. The frame's facets and done list stay.
  A fluent slot uses situation. A non-fluent slot uses *Global. A fact
  about a prototype participant uses *Global. The Lisp keeps the newest
  record first. This appends, so the oldest stays first."
  [kb frame entry & {:keys [situation]}]
  (let [slot (nth-value entry 1)
        situation (or situation (current-situation kb))
        situation (if (and (protoinstance? kb frame)
                           (not (utils/eql? situation term/global-situation)))
                    term/global-situation
                    situation)
        situation (if (and (some? slot) (kb/kb-object? frame))
                    (target-situation kb situation frame slot)
                    situation)
        named (explanation-property kb situation)
        kb (:kb named)
        property (:value named)
        record (or (frame-record kb frame) {:facets {}})
        existing (explanation-vector record property)]
    (if (some #(utils/equal? % entry) existing)
      kb
      (store-frame kb frame
                   (assoc-in record [:explanations property]
                             (conj existing entry))))))

(defn defined-prototypes
  "Prototypes registered on class, in the order they were stored.

  Several prototypes of one class stay in that order. The Lisp sorts
  them most-specific first when the scope is written."
  [kb class]
  (term/build-list (or (:defined-prototypes (frame-record kb class)) []) nil))

(defn add-definition
  "Append one expression to a prototype's cosmetic definition.

  showme and save read this list in a later step. The frame's facets
  stay."
  [kb prototype expr]
  (let [record (or (frame-record kb prototype) {:facets {}})
        existing (or (:definition record) [])]
    (store-frame kb prototype (assoc record :definition (conj existing expr)))))

(defn definition
  "The expressions recorded while a prototype was built, oldest first."
  [kb prototype]
  (term/build-list (or (:definition (frame-record kb prototype)) []) nil))

(defn- forget-frame
  [kb frame]
  (-> kb
      (update :frames dissoc frame)
      (update :frame-order (fn [order] (filterv #(not (utils/eql? % frame)) order)))
      (update :bindings dissoc frame)
      (update :deleted conj frame)))

(defn get-binding
  "The value this frame is bound to, or nil. This is get-binding."
  [kb frame]
  (get (:bindings kb) frame))

(defn- dereference-on
  [kb value seen]
  (cond
    (nil? value) nil
    (and (kb/kb-object? value) (contains? seen value))
    (throw (ex-info "A binding cycle was found." {:frame value}))

    (kb/kb-object? value)
    (if-let [bound (get-binding kb value)]
      (dereference-on kb bound (conj seen value))
      value)

    (term/cons? value)
    (let [head (dereference-on kb (term/car value) seen)
          tail (dereference-on kb (term/cdr value) seen)]
      (if (and (identical? head (term/car value))
               (identical? tail (term/cdr value)))
        value
        (term/cons-cell head tail)))

    :else value))

(defn dereference
  "Follow bindings when dereferencing is on.

  A symbol is replaced by the frame it is bound to, and that chain is
  followed. A list is walked. The same list is returned when nothing in
  it changed. A binding cycle is an error. With dereferencing off, value
  is returned unchanged."
  [kb value]
  (if (dereferencing-on? kb)
    (dereference-on kb value #{})
    value))

(defn obj-stack
  "The object stack after bindings are followed.

  When a binding changes an entry, the returned query stores the
  followed stack. Duplicates are left in place. This is obj-stack.
  unfiltered-obj-stack is the stored list."
  [kb query]
  (let [query (or query empty-query)
        raw (:obj-stack query)
        clean (dereference kb raw)]
    (result kb clean
            (if (utils/equal? clean raw)
              query
              (assoc query :obj-stack clean)))))

(defn unfiltered-obj-stack
  "The object stack as stored, without following bindings."
  [query]
  (:obj-stack (or query empty-query)))

(defn- clear-facets
  [kb frame]
  (if-let [record (frame-record kb frame)]
    (store-frame kb frame (assoc record :facets {}))
    kb))

(declare merge-explanations)

(defn km-bind
  "Bind the dereferenced frame1 to the dereferenced frame2.

  The same object is left unchanged. Otherwise the bound-away frame's
  explanation records are copied onto the survivor, and that frame
  keeps its own records. It loses its slot values and keeps its place
  in the knowledge base when it was already known. A name that was
  never stored stays unknown: the binding is recorded, and known-frame?
  stays false. Ununification data is not recorded."
  [kb frame1 frame2 & {:keys [query] :or {query empty-query}}]
  (when-not (kb/kb-object? frame1)
    (throw (ex-info "A binding is stored on a knowledge-base object."
                    {:frame frame1})))
  (let [left (dereference kb frame1)
        right (dereference kb frame2)]
    (cond
      (not (kb/kb-object? left))
      (throw (ex-info "A binding is stored on a knowledge-base object."
                      {:frame left}))

      (utils/eql? left right) (result kb nil query)

      :else
      (let [merged (if (kb/kb-object? right)
                     (merge-explanations kb left right)
                     kb)
            cleared (if (known-raw? merged left) (clear-facets merged left) merged)]
        (result (assoc-in cleared [:bindings left] right)
                right
                query)))))

(defn ununify
  "Undo a binding. Ununification stays off, so the knowledge base is unchanged and the result is nil."
  [kb _frame & {:keys [query] :or {query empty-query}}]
  (result kb nil query))

(defn bind-self
  "Replace the symbol Self with self.

  This is subst. A Self inside quote is replaced too."
  [expr self]
  (cond
    (and (term/km-symbol? expr) (utils/eql? expr self-symbol)) self
    (term/cons? expr)
    (term/cons-cell (bind-self (term/car expr) self)
                    (bind-self (term/cdr expr) self))
    :else expr))

(defn slot-in
  "The slot of one (slot (values)) pair."
  [slotvals]
  (when-not (term/cons? slotvals)
    (throw (ex-info "Slot values are a slot and a list of values."
                    {:slotvals slotvals})))
  (term/car slotvals))

(defn vals-in
  "The value list of one (slot (values)) pair.

  Nil, from a missing slot, has no values. A second element that is not
  a list is an error."
  [slotvals]
  (cond
    (nil? slotvals) nil
    (term/pair? slotvals)
    (let [values (term/car (term/cdr slotvals))]
      (if (utils/lisp-list? values)
        values
        (throw (ex-info "A slot was given a single value rather than a list of values."
                        {:slot (slot-in slotvals) :value values}))))
    :else
    (throw (ex-info "Slot values are a slot and a list of values."
                    {:slotvals slotvals}))))

(defn make-slotvals
  "One (slot (values)) pair."
  [slot values]
  (term/km-list slot values))

(defn- find-slot
  [slotsvals slot]
  (loop [slotsvals slotsvals]
    (cond
      (nil? slotsvals) nil
      (not (term/cons? slotsvals)) (dotted! slotsvals)
      (utils/eql? slot (slot-in (term/car slotsvals))) (term/car slotsvals)
      :else (recur (term/cdr slotsvals)))))

(defn- update-slot
  [slotsvals slot values]
  (loop [slotsvals slotsvals
         acc []
         found? false]
    (cond
      (nil? slotsvals)
      (term/build-list (if found? acc (conj acc (make-slotvals slot values))) nil)

      (not (term/cons? slotsvals)) (dotted! slotsvals)

      (and (not found?) (utils/eql? slot (slot-in (term/car slotsvals))))
      (recur (term/cdr slotsvals) (conj acc (make-slotvals slot values)) true)

      :else
      (recur (term/cdr slotsvals) (conj acc (term/car slotsvals)) found?))))

(defn- remove-slot
  [slotsvals slot]
  (loop [slotsvals slotsvals
         acc []]
    (cond
      (nil? slotsvals) (term/build-list acc nil)
      (not (term/cons? slotsvals)) (dotted! slotsvals)
      (utils/eql? slot (slot-in (term/car slotsvals)))
      (recur (term/cdr slotsvals) acc)
      :else (recur (term/cdr slotsvals) (conj acc (term/car slotsvals))))))

(defn curr-situation-facet
  "The property name for facet in situation.

  *Global uses the facet itself. Another situation uses the facet name
  joined to the situation name. The joined name is cached, so a later
  call returns the same symbol."
  [kb facet situation]
  (cond
    (not (contains? facet-set facet))
    (throw (ex-info "A facet is one of the four frame facets." {:facet facet}))

    (utils/eql? situation term/global-situation) (result kb facet empty-query)

    :else
    (if-let [cached (get-in kb [:facet-cache facet situation])]
      (result kb cached empty-query)
      (let [joined (symbol (str (term/symbol-name facet)
                                (term/symbol-name situation)))]
        (result (assoc-in kb [:facet-cache facet situation] joined)
                joined
                empty-query)))))

(defn- raw-slots
  [kb frame facet situation]
  (let [frame (dereference kb frame)
        named (curr-situation-facet kb facet situation)
        kb (:kb named)]
    {:kb kb
     :frame frame
     :slots (get-in kb [:frames frame :facets (:value named)])}))

(defn- read-vals
  [kb frame slot facet situation dereference?]
  (let [found (raw-slots kb frame facet situation)
        values (vals-in (find-slot (:slots found) slot))
        kb (:kb found)]
    {:kb kb
     :value (if dereference? (dereference kb values) values)}))

(defn- require-slot
  [slot frame]
  (when-not (term/lisp-symbol? slot)
    (throw (ex-info (str "The slot name " slot " should be a symbol.")
                    {:slot slot :frame frame}))))

(defn- require-frame
  [frame slot]
  (when-not (kb/kb-object? frame)
    (throw (ex-info (str "The frame name " frame " should be a knowledge-base object.")
                    {:slot slot :frame frame}))))

(defn get-slotsvals
  "The (slot (values)) list on one facet.

  The frame name is followed when it is bound. dereference? also follows
  bindings inside the list. A missing frame has no slots."
  [kb frame & {:keys [facet situation dereference? query]
               :or {facet own-properties dereference? true query empty-query}}]
  (require-frame frame nil)
  (let [situation (chosen-situation kb situation frame nil)
        found (raw-slots kb frame facet situation)
        slots (:slots found)
        kb (:kb found)]
    (result kb (if dereference? (dereference kb slots) slots) query)))

(defn get-vals
  "The values of one slot.

  dereference? follows bindings in the values. The frame name is
  followed either way. A missing slot has no values. A slot or a frame
  that is not a knowledge-base name is an error."
  [kb frame slot & {:keys [facet situation dereference? query]
                    :or {facet own-properties dereference? true query empty-query}}]
  (require-slot slot frame)
  (require-frame frame slot)
  (let [situation (chosen-situation kb situation frame slot)
        found (read-vals kb frame slot facet situation dereference?)
        kb (update-in (:kb found) [:runtime :kb-accesses] (fnil inc 0))]
    (result kb (:value found) query)))

(defn gets-vals
  "The values of one slot on several frames.

  A later duplicate, compared with equal?, is dropped. The earlier value
  stays where it was."
  [kb frames slot & {:keys [facet situation dereference? query]
                     :or {facet own-properties dereference? true query empty-query}}]
  (let [situation (if (nil? situation)
                    (target-situation kb
                                      (current-situation kb)
                                      (when (term/cons? frames) (term/car frames))
                                      slot)
                    situation)]
    (loop [frames frames
           kb kb
           acc nil]
      (cond
        (nil? frames)
        (result kb (utils/remove-duplicates acc :test utils/equal? :from-end? true) query)

        (not (term/cons? frames)) (dotted! frames)

        :else
        (let [found (get-vals kb (term/car frames) slot
                              :facet facet
                              :situation situation
                              :dereference? dereference?
                              :query query)]
          (recur (term/cdr frames)
                 (:kb found)
                 (utils/append-lists (term/km-list acc (:value found)))))))))

(defn get-unique-val
  "The one value of a slot, or nil when it has none.

  Several values produce the first one and a :message. fail-mode :error
  throws when there is no value. :fail returns nil."
  [kb frame slot & {:keys [facet situation fail-mode query]
                    :or {facet own-properties fail-mode :fail query empty-query}}]
  (let [found (get-vals kb frame slot :facet facet :situation situation :query query)
        values (:value found)]
    (cond
      (term/singleton? values) (assoc found :value (term/car values))
      (some? values)
      (assoc found
             :value (term/car values)
             :message "The slot should have at most one value. The first one is used.")
      (= fail-mode :error)
      (throw (ex-info (str "No value found for the " slot " of " frame ".")
                      {:slot slot :frame frame}))
      :else found)))

(defn- unique-stored
  "The first stored value, or nil. Used while computing a slot's own inverse or cardinality."
  [kb frame slot]
  (let [found (read-vals kb frame slot own-properties term/global-situation true)]
    (when (term/cons? (:value found))
      (term/car (:value found)))))

(defn- invert-cardinality
  [cardinality]
  (cond
    (nil? cardinality) nil
    (utils/eql? cardinality one-to-n) n-to-1
    (utils/eql? cardinality n-to-1) one-to-n
    (utils/eql? cardinality n-to-n) n-to-n
    (utils/eql? cardinality one-to-1) one-to-1
    :else cardinality))

(defn- cardinality-declared
  [kb slot]
  (when (kb/kb-object? slot)
    (let [found (read-vals kb slot (symbol "cardinality")
                           own-properties term/global-situation false)
          values (:value found)]
      (cond
        (nil? values) nil
        (not (term/singleton? values))
        (let [chosen (term/car values)]
          (if (contains? valid-cardinalities chosen) chosen n-to-n))
        (contains? valid-cardinalities (term/car values)) (term/car values)
        :else n-to-n))))

(defn invert-slot
  "The inverse of a slot.

  A built-in pair such as instance-of and instances is used first. A
  declared inverse in *Global is next. Otherwise the name gains or loses
  the suffix -of. A slot that is not a symbol has no inverse."
  [kb slot]
  (cond
    (not (kb/slot-object? slot)) nil
    (contains? built-in-inverses slot) (get built-in-inverses slot)
    :else
    (or (unique-stored kb slot (symbol "inverse"))
        (let [label (term/symbol-name slot)
              suffix (count inverse-suffix)]
          (if (and (> (count label) suffix)
                   (= inverse-suffix (subs label (- (count label) suffix))))
            (km-symbol (subs label 0 (- (count label) suffix)))
            (km-symbol (str label inverse-suffix)))))))

(defn cardinality-of
  "The cardinality of a slot.

  A built-in single-valued slot is N-to-1. A built-in multivalued slot
  is N-to-N. Otherwise the cardinality stored in *Global is used, then
  the inverse of the inverse slot's cardinality. The default is N-to-N.
  Two declarations use the first. An invalid declaration uses N-to-N.
  Those Lisp messages are not printed."
  [kb slot]
  (cond
    (contains? built-in-single-valued slot) n-to-1
    (contains? built-in-multivalued slot) n-to-n
    :else
    (or (cardinality-declared kb slot)
        (invert-cardinality (cardinality-declared kb (invert-slot kb slot)))
        n-to-n)))

(defn single-valued-slot?
  "True when the cardinality is 1-to-1 or N-to-1."
  [kb slot]
  (contains? single-cardinalities (cardinality-of kb slot)))

(defn- built-in-inertial
  [kb]
  (let [slots #{(symbol "nowexists")}]
    (if (:instance-of-is-fluent? (:runtime kb))
      (into slots [(symbol "instance-of") (symbol "instances")])
      slots)))

(defn- built-in-non-inertial
  []
  (syms ["add-list" "del-list" "pcs-list" "ncs-list" "block-projection-for"]))

(defn- universal-slot?
  "True for a built-in slot that is neither an inertial nor a plain fluent.

  This is universalp. A user-declared non-fluent is not universal. It is
  still stored in *Global through fluent?."
  [kb slot]
  (and (contains? built-in-slots slot)
       (not (contains? (built-in-inertial kb) slot))
       (not (contains? (built-in-non-inertial) slot))))

(defn- stored-fluent-status
  [kb slot]
  (when (and (kb/slot-object? slot) (kb/kb-object? slot))
    (:value (get-unique-val kb slot (symbol "fluent-status")
                            :situation term/global-situation
                            :dereference? true))))

(defn- check-fluent-status
  [status slot]
  (when (and (some? status) (not (contains? valid-fluent-statuses status)))
    (throw (ex-info (str "Invalid fluent-status " status " on slot " slot
                         ". It should be *Fluent, *Inertial-Fluent, or *Non-Fluent.")
                    {:slot slot :status status}))))

(defn fluent-status
  "The fluent status of a slot.

  A built-in inertial slot is *Inertial-Fluent. add-list and the other
  built-in plain fluents are *Fluent. Every other built-in slot is
  *Non-Fluent. A user slot uses the fluent-status stored in *Global, or
  the same slot on its inverse. The two must agree. Several stored
  values use the first. That message is not printed. An invalid status
  is an error."
  [kb slot]
  (cond
    (contains? (built-in-inertial kb) slot) fluent-status-inertial
    (contains? (built-in-non-inertial) slot) fluent-status-fluent
    (universal-slot? kb slot) fluent-status-non
    :else
    (let [direct (stored-fluent-status kb slot)
          inverse (stored-fluent-status kb (invert-slot kb slot))]
      (check-fluent-status direct slot)
      (check-fluent-status inverse (invert-slot kb slot))
      (when (and (some? direct) (some? inverse) (not (utils/eql? direct inverse)))
        (throw (ex-info (str "Inconsistent fluent-status. " slot " has " direct
                             " and " (invert-slot kb slot) " has " inverse ".")
                        {:slot slot :status direct :inverse-status inverse})))
      (or direct inverse))))

(defn runtime
  "The flags reset restores, and the default fluent status.

  :default-fluent-status starts as *Fluent. :instance-of-is-fluent?
  starts false, so instance-of is a non-fluent. The :are-some-* flags
  start false. A later query skips prototypes, constraints, subslots,
  definitions, and defaults while the matching flag is false.
  :classification-enabled? and :prototype-classification-enabled?
  start true. :max-padding-instances starts at 0.
  :use-prototypes? starts true. :recursive-prototypes? starts false.
  :eagerly-unify-prototypes?, :record-explanations?,
  :record-explanations-for-clones?, :add-cloned-from-links?, and
  :propagate-explanations? start true.
  :classes-using-assertions, :visible-theories, and :curr-prototype
  start empty. :situations-mode? starts false."
  [kb]
  (:runtime kb))

(defn default-fluent-status
  "The fluent status of a slot that does not declare one.

  A fresh knowledge base uses *Fluent. reset restores that."
  [kb]
  (:default-fluent-status (:runtime kb)))

(defn set-default-fluent-status
  "Make status the default fluent status.

  status must be *Fluent, *Inertial-Fluent, or *Non-Fluent. The Lisp
  prints a line. This returns the knowledge base and prints nothing."
  [kb status]
  (when-not (contains? valid-fluent-statuses status)
    (throw (ex-info (str "Invalid default fluent status " status
                         ". It should be *Fluent, *Inertial-Fluent, or *Non-Fluent.")
                    {:status status})))
  (assoc-in kb [:runtime :default-fluent-status] status))

(defn instance-of-is-fluent?
  "True when instance-of and instances are situational.

  The default is false, which is instance-of-is-nonfluent."
  [kb]
  (boolean (:instance-of-is-fluent? (:runtime kb))))

(defn set-instance-of-is-fluent
  "Choose whether instance-of and instances are fluent.

  false restores the built-in non-fluent lists. reset does that too."
  [kb on?]
  (assoc-in kb [:runtime :instance-of-is-fluent?] (boolean on?)))

(defn are-some?
  "True when one optimization flag has been set.

  flag is :definitions, :prototype-definitions, :prototypes, :subslots,
  :constraints, :tags, or :defaults. Each starts false."
  [kb flag]
  (let [key (get are-some-flags flag)]
    (when (nil? key)
      (throw (ex-info (str "An optimization flag is " flag
                           ". It should be definitions, prototype-definitions, prototypes, subslots, constraints, tags, or defaults.")
                      {:flag flag})))
    (boolean (get (:runtime kb) key))))

(defn set-are-some
  "Turn one optimization flag on or off. reset turns them all off."
  [kb flag on?]
  (let [key (get are-some-flags flag)]
    (when (nil? key)
      (throw (ex-info (str "An optimization flag is " flag
                           ". It should be definitions, prototype-definitions, prototypes, subslots, constraints, tags, or defaults.")
                      {:flag flag})))
    (assoc-in kb [:runtime key] (boolean on?))))

(defn classification-enabled?
  "True when classification is enabled. It starts enabled."
  [kb]
  (boolean (:classification-enabled? (:runtime kb))))

(defn set-classification
  "Turn classification and prototype classification on or off together.

  reset turns both on. This is enable-classification and
  disable-classification."
  [kb on?]
  (-> kb
      (assoc-in [:runtime :classification-enabled?] (boolean on?))
      (assoc-in [:runtime :prototype-classification-enabled?] (boolean on?))))

(defn curr-prototype
  "The prototype being built, or nil when prototype mode is off."
  [kb]
  (:curr-prototype (:runtime kb)))

(defn set-curr-prototype
  "Enter or leave prototype mode. nil leaves it.

  reset leaves it empty."
  [kb prototype]
  (assoc-in kb [:runtime :curr-prototype] prototype))

(defn use-prototypes?
  "True when a slot read may clone a prototype.

  The flag starts true. It is false while a prototype is being built,
  and while a prototype lookup is already running. A missing flag is
  treated as true."
  [kb]
  (and (get (:runtime kb) :use-prototypes? true)
       (nil? (curr-prototype kb))))

(defn set-use-prototypes
  "Turn prototype cloning on or off for later slot reads.

  false also covers the lookup that is already running. The previous
  value is what the caller restores."
  [kb on?]
  (assoc-in kb [:runtime :use-prototypes?] (boolean on?)))

(defn fluent?
  "True when a slot's values vary by situation.

  With the default *Fluent, every slot is fluent except one whose status
  is *Non-Fluent. With the default *Non-Fluent, only *Fluent and
  *Inertial-Fluent slots are fluent."
  [kb slot]
  (let [status (fluent-status kb slot)
        default (default-fluent-status kb)]
    (cond
      (utils/eql? default fluent-status-non)
      (or (utils/eql? status fluent-status-fluent)
          (utils/eql? status fluent-status-inertial))

      (or (utils/eql? default fluent-status-fluent)
          (utils/eql? default fluent-status-inertial))
      (not (utils/eql? status fluent-status-non))

      :else false)))

(defn ignore-slot-in-global?
  "True when a fluent read in *Global is refused.

  Situations mode is on, the current situation is *Global, and
  prototype mode is off. A cached answer is returned before this test."
  [kb slot]
  (and (situations-mode? kb)
       (utils/eql? (current-situation kb) term/global-situation)
       (nil? (curr-prototype kb))
       (fluent? kb slot)))

(defn inertial-fluent?
  "True when a slot keeps its value until an action changes it.

  With the default *Inertial-Fluent, a slot is inertial unless its
  status is *Fluent or *Non-Fluent. Otherwise only an explicit
  *Inertial-Fluent status counts."
  [kb slot]
  (let [status (fluent-status kb slot)
        default (default-fluent-status kb)]
    (cond
      (or (utils/eql? default fluent-status-non)
          (utils/eql? default fluent-status-fluent))
      (utils/eql? status fluent-status-inertial)

      (utils/eql? default fluent-status-inertial)
      (not (or (utils/eql? status fluent-status-non)
               (utils/eql? status fluent-status-fluent)))

      :else false)))

(defn- flag-on-slot?
  [kb slot flag built-ins]
  (or (contains? built-ins slot)
      (let [found (read-vals kb slot flag own-properties
                             term/global-situation false)]
        (some? (:value found)))))

(defn remove-subsumers-slot?
  "True when a more specific class on this slot drops a more general one.

  instance-of, classes, superclasses, and member-type count before a
  value is stored. A user slot counts when remove-subsumers is stored
  on it in *Global."
  [kb slot]
  (flag-on-slot? kb slot (symbol "remove-subsumers") remove-subsumer-slots))

(defn remove-subsumees-slot?
  "True when a more general class on this slot drops a more specific one.

  subclasses, prototype-of, domain, and range count before a value is
  stored. A user slot counts when remove-subsumees is stored on it in
  *Global."
  [kb slot]
  (flag-on-slot? kb slot (symbol "remove-subsumees") remove-subsumee-slots))

(defn appending-slot?
  "True when several value lists on this slot are appended.

  A built-in appending slot counts even before a value is stored. A
  user slot counts when combine-values-by-appending is stored on it in
  *Global."
  [kb slot]
  (flag-on-slot? kb slot (symbol "combine-values-by-appending") appending-slots))

(defn- non-inverse-slot?
  [kb slot]
  (flag-on-slot? kb slot (symbol "ignore-inverses") non-inverse-slots))

(defn- non-inverse-concept?
  [concept]
  (contains? built-in-instances concept))

(def ^{:dynamic true
       :doc "The value-list subsumption test the store calls.

  Nil means structural equality. som.km.subsumes installs the real test
  at load time. The var lives here so the frame store does not require
  that namespace."}
  *valset-subsumes*
  nil)

(defn- store-refused?
  [state]
  (= "not-ported" (:error state)))

(defn valset-subsumes-valset?
  "True when every value in newer is structurally equal to a distinct value in older.

  An existential does not cover a different value, so (a Dog) does not
  cover _Dog1. Two copies of (a Dog) still match, because they are
  structurally equal. The store uses *valset-subsumes* when it is set."
  [newer older]
  (loop [newer newer
         older older]
    (cond
      (nil? newer) true
      (nil? older) false
      (not (term/cons? newer)) (dotted! newer)
      (not (term/cons? older)) (dotted! older)
      (utils/member? (term/car newer) older utils/equal?)
      (recur (term/cdr newer)
             (utils/remove-items (term/car newer) older
                                 :test utils/equal? :count 1))
      :else false)))

(defn- absent?
  [coll banned test]
  (loop [coll coll
         acc []]
    (cond
      (nil? coll) (term/build-list acc nil)
      (not (term/cons? coll)) (dotted! coll)
      (utils/member? (term/car coll) banned test)
      (recur (term/cdr coll) acc)
      :else (recur (term/cdr coll) (conj acc (term/car coll))))))

(defn- append-element
  [coll item]
  (term/build-list (conj (vec (utils/elements coll)) item) nil))

(defn- equal-tail
  [item coll]
  (loop [coll coll]
    (cond
      (nil? coll) nil
      (not (term/cons? coll)) (dotted! coll)
      (utils/equal? item (term/car coll)) coll
      :else (recur (term/cdr coll)))))

(defn- length-of
  [coll]
  (loop [coll coll
         n 0]
    (cond
      (nil? coll) n
      (term/cons? coll) (recur (term/cdr coll) (inc n))
      :else (dotted! coll))))

(defn- every-constraint?
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) (dotted! values)
      (kb/constraint-expr? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- subsumes-valset
  "Whether newer covers older. :value is true or false.

  A bound *valset-subsumes* receives the state, so a slot read inside
  the test can update the knowledge base. Nil uses structural equality."
  [state newer older]
  (if (fn? *valset-subsumes*)
    (*valset-subsumes* state newer older)
    (assoc state :value (valset-subsumes-valset? newer older))))

(defn- some-subsumed?
  [state newer valsets]
  (loop [valsets valsets
         state state]
    (cond
      (nil? valsets) (assoc state :value false)
      (not (term/cons? valsets)) (dotted! valsets)
      :else
      (let [hit (subsumes-valset state newer (term/car valsets))]
        (cond
          (store-refused? hit) hit
          (:value hit) hit
          :else (recur (term/cdr valsets) hit))))))

(defn- drop-subsumed
  [state valsets newer]
  (loop [valsets valsets
         state state
         acc []]
    (cond
      (nil? valsets) (assoc state :value (term/build-list acc nil))
      (not (term/cons? valsets)) (dotted! valsets)
      :else
      (let [hit (subsumes-valset state (term/car valsets) newer)]
        (cond
          (store-refused? hit) hit
          (:value hit) (recur (term/cdr valsets) hit acc)
          :else (recur (term/cdr valsets) hit (conj acc (term/car valsets))))))))

(defn- dedup-earlier
  [classes]
  (utils/remove-duplicates classes :test utils/equal? :from-end? true))

(declare put-vals add-val install-inverses install-inverses0)

(defn- joined-vals
  [state old-values add-values]
  (kb/valsets-to-&&-exprs
   (utils/remove-duplicates
    (utils/append-lists
     (term/km-list old-values (kb/&&-exprs-to-valsets add-values)))
    :test utils/equal?
    :from-end? true)))

(defn- compute-new-vals
  "The values to store, or nil when the slot does not change.

  :value nil still returns the state, because a subsumption check can
  update the knowledge base and the query. A refusal is returned as it is."
  [state slot old-values0 add-values combine]
  (let [kb (:kb state)
        old-values (if (single-valued-slot? kb slot)
                     (kb/un-andify old-values0)
                     old-values0)
        extra (absent? add-values old-values utils/equal?)
        unchanged (fn [state values] (assoc state :value values))]
    (cond
      (remove-subsumers-slot? kb slot)
      (unchanged state
                 (if (some? extra)
                   (dedup-earlier (utils/append-lists (term/km-list old-values extra)))
                   old-values0))

      (remove-subsumees-slot? kb slot)
      (unchanged state
                 (if (some? extra)
                   (dedup-earlier (utils/append-lists (term/km-list old-values extra)))
                   old-values0))

      (appending-slot? kb slot)
      (unchanged state
                 (if (some? extra)
                   (kb/remove-dup-instances (utils/append-lists (term/km-list old-values extra)))
                   old-values0))

      (utils/eql? combine appending)
      (let [joined (kb/remove-dup-instances
                    (utils/append-lists (term/km-list old-values add-values)))]
        (unchanged state
                   (if (single-valued-slot? kb slot)
                     (kb/val-to-vals (kb/vals-to-&-expr joined))
                     joined)))

      (single-valued-slot? kb slot)
      (if (nil? (absent? add-values old-values utils/eql?))
        (assoc state :value nil)
        (let [covered (subsumes-valset state add-values old-values)]
          (cond
            (store-refused? covered) covered
            (:value covered) (assoc covered :value nil)
            :else (assoc covered :value
                         (kb/val-to-vals
                          (kb/vals-to-&-expr
                           (utils/append-lists (term/km-list old-values add-values))))))))

      :else
      (let [valsets (kb/&&-exprs-to-valsets old-values)
            n (length-of valsets)
            attach (fn [state reduced]
                     (assoc state :value (joined-vals state reduced add-values)))]
        (cond
          (utils/member? add-values valsets utils/equal?) (assoc state :value nil)
          (and (every-constraint? add-values) (term/singleton? valsets) (> n 10))
          (unchanged state
                     (utils/remove-duplicates
                      (utils/append-lists (term/km-list (term/car valsets) add-values))
                      :test utils/equal?))
          (> n 10) (attach state valsets)
          :else
          (let [covered (some-subsumed? state add-values valsets)]
            (cond
              (store-refused? covered) covered
              (:value covered) (assoc covered :value nil)
              (and (every-constraint? add-values) (term/singleton? valsets))
              (assoc covered :value
                     (utils/remove-duplicates
                      (utils/append-lists (term/km-list (term/car valsets) add-values))
                      :test utils/equal?))
              :else
              (let [reduced (drop-subsumed covered valsets add-values)]
                (if (store-refused? reduced)
                  reduced
                  (attach reduced (:value reduced)))))))))))

(defn- strip-sources
  "Drop a fully evaluated source or comment from the top of each value.

  :values is the list to store. :notes is a vector of [stripped original]
  pairs. The caller records each original as the explanation after the
  stripped value is stored. A value that is not fully evaluated after
  the strip is stored unchanged, tags included, and is not a note."
  [values]
  (loop [values values
         acc []
         notes []]
    (cond
      (nil? values) {:values (term/build-list acc nil) :notes notes}
      (not (term/cons? values)) (dotted! values)
      :else
      (let [original (term/car values)
            stripped (explain/desource-decomment-top-level original)
            record? (and (some? stripped)
                         (kb/fully-evaluated? stripped)
                         (not (utils/equal? stripped original)))]
        (recur (term/cdr values)
               (conj acc (if record? stripped original))
               (if record? (conj notes [stripped original]) notes))))))

(defn- write-facet
  [kb frame facet slotsvals]
  (let [record (or (frame-record kb frame) {:facets {}})
        facets (:facets record)]
    (cond
      (and (nil? slotsvals) (not (known-raw? kb frame))) kb
      (nil? slotsvals)
      (store-frame kb frame (assoc record :facets (dissoc facets facet)))
      :else
      (store-frame kb frame (assoc record :facets (assoc facets facet slotsvals))))))

(defn- maybe-active-stack
  [kb query frame values]
  (if (:active-obj-stack? kb)
    (push-all kb query (term/cons-cell frame values))
    query))

(defn protoinstance?
  "True when frame participates in a prototype.

  The test is a global prototype-participant-of value. Bindings inside
  that value are not followed. A prototype root participates in itself,
  so it is a protoinstance."
  [kb frame]
  (and (kb/kb-object? frame)
       (some? (:value (get-vals kb frame (symbol "prototype-participant-of")
                                :situation term/global-situation
                                :dereference? false)))))

(defn- description-parents
  "The class of a (the-class Class with ...) value, plus instance-of classes inside it."
  [expr]
  (let [class (when (term/cons? (term/cdr expr)) (term/car (term/cdr expr)))]
    (when (kb/kb-object? class)
      (let [after (term/cdr (term/cdr expr))
            slots (if (and (term/cons? after)
                           (utils/eql? (symbol "with") (term/car after)))
                    (term/cdr after)
                    nil)]
        (loop [slots slots
               acc [class]]
          (cond
            (or (nil? slots) (not (term/cons? slots))) acc
            :else
            (let [pair (term/car slots)
                  values (when (and (term/pair? pair)
                                    (utils/eql? (symbol "instance-of") (term/car pair)))
                           (term/car (term/cdr pair)))]
              (if (utils/lisp-list? values)
                (recur (term/cdr slots)
                       (into acc (filter kb/kb-object? (utils/elements values))))
                (recur (term/cdr slots) acc)))))))))

(defn- remember-defined-prototype
  "Append prototype on an existing class frame.

  The class frame is not created here. instance-of and prototype-of
  install their inverses first, and those inverses create the class.
  A scope written before that frame exists is not indexed."
  [kb parent prototype]
  (let [record (frame-record kb parent)]
    (if (nil? record)
      kb
      (let [existing (or (:defined-prototypes record) [])]
        (if (some #(utils/eql? % prototype) existing)
          kb
          (store-frame kb parent
                       (assoc record :defined-prototypes (conj existing prototype))))))))

(defn- register-prototype-scope
  "Point each parent of a prototype-scope value at this prototype.

  A class name is simple and does not mark prototype definitions.
  A (the-class ...) value does. Parents are appended. The read sorts
  nothing, so several prototypes of one class stay in storage order.
  A parent that is not already a frame is skipped, and this write does
  not create that frame."
  [kb prototype values]
  (loop [values values
         kb kb
         defined? false]
    (cond
      (nil? values)
      (if defined?
        (set-are-some kb :prototype-definitions true)
        kb)
      (not (term/cons? values)) kb
      :else
      (let [value (term/car values)]
        (cond
          (kb/kb-object? value)
          (recur (term/cdr values)
                 (remember-defined-prototype kb value prototype)
                 defined?)
          (kb/the-class? value)
          (if-let [parents (description-parents value)]
            (recur (term/cdr values)
                   (reduce #(remember-defined-prototype %1 %2 prototype) kb parents)
                   true)
            (recur (term/cdr values) kb defined?))
          :else (recur (term/cdr values) kb defined?))))))

(defn explanations-flag
  "Which explanations are recorded.

  True records every slot. False records none, except a cloned-from or
  added-at explanation while record-explanations-for-clones is on. A
  vector of slots records those slots and their inverses. A missing flag
  records every slot."
  [kb]
  (get-in kb [:runtime :record-explanations?] true))

(defn set-record-explanations
  "Replace the explanation flag. True, false, or a vector of slot names."
  [kb flag]
  (assoc-in kb [:runtime :record-explanations?] flag))

(defn explanations-on?
  "True when ordinary explanations are recorded."
  [kb]
  (let [flag (explanations-flag kb)]
    (not (or (false? flag) (nil? flag)))))

(defn- slot-list?
  [flag]
  (or (vector? flag) (term/cons? flag)))

(defn- listed-slot?
  [flag slot inverse]
  (let [names (if (term/cons? flag) (utils/elements flag) flag)]
    (boolean (some #(or (utils/eql? % slot) (utils/eql? % inverse)) names))))

(defn- should-record-expr?
  [kb expr]
  (or (explanations-on? kb)
      (and (get-in kb [:runtime :record-explanations-for-clones?] true)
           (term/cons? expr)
           (contains? #{(symbol "cloned-from") (symbol "added-at")}
                      (term/car expr)))))

(defn- set-of-terms?
  [expr]
  (loop [items (term/cdr expr)]
    (cond
      (nil? items) true
      (not (term/cons? items)) false
      (kb/is-km-term? (explain/desource (term/car items))) (recur (term/cdr items))
      :else false)))

(defn- projected-from
  [explanations]
  (loop [explanations explanations]
    (cond
      (nil? explanations) nil
      (not (term/cons? explanations)) nil
      :else
      (let [explanation (term/car explanations)]
        (if (and (term/cons? explanation)
                 (utils/eql? (term/car explanation) (symbol "projected-from")))
          (nth-value explanation 1)
          (recur (term/cdr explanations)))))))

(defn- drop-projected
  [explanations]
  (loop [explanations explanations
         acc []]
    (cond
      (nil? explanations) (term/build-list acc nil)
      (not (term/cons? explanations)) (term/build-list acc nil)
      :else
      (let [explanation (term/car explanations)]
        (recur (term/cdr explanations)
               (if (and (term/cons? explanation)
                        (utils/eql? (term/car explanation) (symbol "projected-from")))
                 acc
                 (conj acc explanation)))))))

(defn- matching-explanations
  [records slot value]
  (loop [records records
         acc []]
    (cond
      (nil? records) (term/build-list acc nil)
      (not (term/cons? records)) nil
      :else
      (let [record (term/car records)]
        (recur (term/cdr records)
               (if (and (utils/eql? (nth-value record 1) slot)
                        (utils/equal? (nth-value record 2) value))
                 (conj acc (nth-value record 3))
                 acc))))))

(defn explanation-records
  "Every explanation record for instance and slot. This is get-all-explanations.

  Each record is (instance slot value explanation), oldest first. The
  situation's own records come first, then the records in *Global.
  A repeated record keeps the earlier copy, in its original position.
  remove-clone-cycles is not run. slot may be nil, and then the current
  situation is the one read. An instance that is not a knowledge-base
  object has no records."
  [kb instance slot & {:keys [situation]}]
  (let [instance (if (kb/kb-object? instance) (dereference kb instance) instance)]
    (if-not (kb/kb-object? instance)
      {:kb kb :value nil}
      (let [situation (or situation (current-situation kb))
            target (if (some? slot)
                     (target-situation kb situation instance slot)
                     situation)
            global-name (explanation-property kb term/global-situation)
            kb (:kb global-name)
            global (explanation-vector (frame-record kb instance) (:value global-name))
            local (if (utils/eql? target term/global-situation)
                    {:kb kb :records []}
                    (let [named (explanation-property kb target)
                          kb-now (:kb named)]
                      {:kb kb-now
                       :records (explanation-vector (frame-record kb-now instance)
                                                    (:value named))}))
            kb (:kb local)
            combined (term/build-list (into (vec (:records local)) global) nil)
            followed (dereference kb combined)]
        {:kb kb
         :value (utils/remove-duplicates followed
                                         :test utils/equal?
                                         :from-end? true)}))))

(defn- direction-explanations
  [kb instance slot value situation seen]
  (let [instance (if (kb/kb-object? instance) (dereference kb instance) instance)
        value (dereference kb value)
        found (explanation-records kb instance slot :situation situation)
        explanations (matching-explanations (:value found) slot value)
        source (projected-from explanations)]
    (if (or (nil? source)
            (utils/eql? source situation)
            (contains? seen source))
      {:kb (:kb found)
       :value (utils/remove-duplicates explanations :test utils/equal?)}
      (let [kept (drop-projected explanations)
            deeper (direction-explanations (:kb found) instance slot value source
                                           (conj seen situation))
            combined (utils/append-lists
                      (term/km-list kept (:value deeper)))]
        {:kb (:kb deeper)
         :value (utils/remove-duplicates combined :test utils/equal?)}))))

(defn- one-direction
  [kb instance slot value situation]
  (let [instance (if (kb/kb-object? instance) (dereference kb instance) instance)
        value (dereference kb value)
        found (direction-explanations kb instance slot value situation #{})]
    (if (nil? (:value found))
      {:kb (:kb found) :structure nil}
      {:kb (:kb found)
       :structure (term/km-list instance slot value (:value found))})))

(defn explanations-for
  "The explanations for one triple, forward and then inverse.

  This is get-explanations. :value is a list of (instance slot value
  explanations) structures. A direction with nothing stored is left out.
  instance-of is read in *Global along with every other slot's global
  records. The caller passes the situation."
  [kb instance slot value & {:keys [situation]}]
  (let [situation (or situation (current-situation kb))
        forward (one-direction kb instance slot value situation)
        backward (if (nil? slot)
                   {:kb (:kb forward) :structure nil}
                   (one-direction (:kb forward) value (invert-slot (:kb forward) slot)
                                  instance situation))]
    {:kb (:kb backward)
     :value (cond
              (and (:structure forward) (:structure backward))
              (term/km-list (:structure forward) (:structure backward))
              (:structure forward) (term/km-list (:structure forward))
              (:structure backward) (term/km-list (:structure backward))
              :else nil)}))

(defn record-explanation-for
  "Store one explanation for (the slot of instance).

  target is that path. expr is the explanation. A duplicate is left as
  it is. A :set is not stored. A remove-subsumers or remove-subsumees
  slot whose value is not actually stored is left unrecorded, unless
  force? is set. An existential explanation also records the value's
  instance-of when that class is already stored. :program-error is set
  when a :set still holds something that is not a term."
  [kb target val expr & {:keys [situation force?]}]
  (let [slot (nth-value target 1)
        instance (nth-value target 3)
        flag (explanations-flag kb)
        expr (explain/desource-all-but-top-level expr)]
    (cond
      (not (should-record-expr? kb expr)) {:kb kb}
      (and (slot-list? flag)
           (not (listed-slot? flag slot (invert-slot kb slot))))
      {:kb kb}
      (not (kb/kb-object? instance)) {:kb kb}
      (and (kb/km-set? expr) (not (set-of-terms? expr)))
      {:kb kb :program-error true :target target :val val :expr expr}
      (or (nil? val) (not (term/cons? expr)) (kb/km-set? expr)) {:kb kb}
      (and (kb/km-triple? val) (nil? (nth-value val 2))) {:kb kb}
      (and (not force?)
           (or (remove-subsumers-slot? kb slot) (remove-subsumees-slot? kb slot))
           (not (utils/member? val
                               (:value (get-vals kb instance slot
                                                 :dereference? false)))))
      {:kb (:kb (get-vals kb instance slot :dereference? false))}
      :else
      (let [read (get-vals kb instance slot :dereference? false)
            entry (term/km-list instance slot val expr)
            kb (record-explanation (:kb read) instance entry :situation situation)
            class (when (and (not (utils/eql? slot (symbol "instance-of")))
                             (kb/kb-object? val)
                             (kb/existential? expr))
                    (nth-value (explain/desource expr) 1))
            classes (when (some? class)
                      (get-vals kb val (symbol "instance-of")))]
        (if (and (some? class) (utils/member? class (:value classes)))
          (record-explanation-for (:kb classes)
                                  (term/km-list (symbol "the") (symbol "instance-of")
                                                (symbol "of") val)
                                  class expr
                                  :situation situation
                                  :force? force?)
          {:kb (or (:kb classes) kb)})))))

(defn- situations-touched
  [kb]
  (into [] (concat (:situations kb) (:theories kb))))

(defn merge-explanations
  "Copy recessive's explanation records onto dominant.

  A record already stored on dominant stays where it is. The recessive
  frame keeps its records too. The Lisp drops a remove-subsumers record
  whose triple disappeared. That drop is not done here. The bound frame
  is left in place."
  [kb recessive dominant]
  (if-not (and (kb/kb-object? recessive) (kb/kb-object? dominant))
    kb
    (reduce (fn [kb situation]
              (let [lost (explanation-records kb recessive nil :situation situation)
                    kept (explanation-records (:kb lost) dominant nil :situation situation)
                    novel (loop [records (:value lost)
                                 acc []]
                            (cond
                              (nil? records) (term/build-list acc nil)
                              (not (term/cons? records)) (term/build-list acc nil)
                              (utils/member? (term/car records) (:value kept) utils/equal?)
                              (recur (term/cdr records) acc)
                              :else (recur (term/cdr records)
                                           (conj acc (term/car records)))))]
                (loop [records novel
                       kb (:kb kept)]
                  (cond
                    (nil? records) kb
                    (not (term/cons? records)) kb
                    :else
                    (recur (term/cdr records)
                           (record-explanation kb dominant (term/car records)
                                               :situation situation))))))
            kb
            (situations-touched kb))))

(defn- record-notes
  "Record each stripped original after its value is already stored."
  [kb frame slot situation notes]
  (reduce (fn [kb pair]
            (let [[val expr] pair]
              (:kb (record-explanation-for
                    kb
                    (term/km-list (symbol "the") slot (symbol "of") frame)
                    val expr
                    :situation situation))))
          kb
          notes))

(defn put-vals
  "Replace the values of one slot and return the frame.

  Nil values remove the slot. An equal replacement leaves the slot as
  it is. Own properties and own definitions drop a fully evaluated
  source or comment before they are stored, and that original value is
  recorded as the explanation. prototype-scope keeps its tags. Writing
  prototype-scope registers the frame on each parent. A fact about a
  prototype participant is stored in *Global. The Lisp warning for that
  redirect is not recorded. Inverses are installed for ground values
  that were not already on the slot. A reserved frame name, or a frame
  that is not a knowledge-base object, is an error and stores nothing."
  [kb frame slot values & {:keys [facet install-inverses? situation query]
                           :or {facet own-properties install-inverses? true
                                query empty-query}}]
  (require-slot slot frame)
  (when-not (contains? facet-set facet)
    (throw (ex-info "A facet is one of the four frame facets." {:facet facet})))
  (cond
    (contains? kb/reserved-keywords frame)
    (throw (ex-info (str "The keyword " frame " cannot name a frame.")
                    {:frame frame :slot slot}))

    (not (kb/kb-object? frame))
    (throw (ex-info (str frame " is not a knowledge-base object.")
                    {:frame frame :slot slot}))

    :else
    (let [requested (or situation (current-situation kb))
          situation (if (and (protoinstance? kb frame)
                             (not (utils/eql? requested term/global-situation)))
                      term/global-situation
                      situation)
          situation (chosen-situation kb situation frame slot)
          prepared (if (and (contains? own-facets facet)
                            (not (utils/eql? slot prototype-scope)))
                     (strip-sources values)
                     {:values values :notes []})
          values (:values prepared)
          notes (:notes prepared)
          query (maybe-active-stack kb query frame values)
          found (raw-slots kb frame facet situation)
          kb (:kb found)
          old (vals-in (find-slot (:slots found) slot))
          noted (fn [kb] (record-notes kb frame slot situation notes))]
      (if (utils/equal? values old)
        (result (noted kb) frame query)
        (let [query (if (known-raw? kb frame) query (push-to-obj-stack kb query frame))
              named (curr-situation-facet kb facet situation)
              kb (:kb named)
              slots (get-in kb [:frames frame :facets (:value named)])
              slots (if (nil? values)
                      (remove-slot slots slot)
                      (update-slot slots slot values))
              kb (write-facet kb frame (:value named) slots)
              added (absent? values old utils/eql?)]
          (let [installed (if (and install-inverses?
                                   (:installing-inverses? kb)
                                   (contains? own-facets facet)
                                   (some? added))
                            (let [linked (install-inverses kb frame slot added situation query)]
                              (assoc linked :value frame))
                            (result kb frame query))
                kb (if (and (utils/eql? slot prototype-scope) (some? values))
                     (register-prototype-scope (:kb installed) frame values)
                     (:kb installed))]
            (assoc installed :kb (noted kb))))))))

(defn- install-inverse-link
  [kb invframe invslot invval situation query install?]
  (add-val kb invframe invslot invval
           :install-inverses? install?
           :situation situation
           :query query))

(defn- arg-present?
  "Lisp treats a missing argument and the symbol nil as absent."
  [value]
  (not (kb/km-null? value)))

(defn- args-headed
  "(:args head . tail). tail is the rest of the list, not one element."
  [head tail]
  (term/cons-cell :args (term/cons-cell head tail)))

(defn- install-args
  "Inverse links for one (:args ...) value.

  The first argument is linked through invslot. A second argument is
  linked through inverse2 when that slot exists, and through inverse12
  by add-val. A third argument is linked through inverse3. classify is
  not called."
  [kb invframe invslot invval slot situation query]
  (let [step (install-inverses0 kb (kb/arg1 invframe) invslot
                                (args-headed invval (term/cdr (term/cdr invframe)))
                                slot situation query)
        kb (:kb step)
        query (:query step)
        second-arg (kb/arg2 invframe)
        declared2 (unique-stored kb slot (symbol "inverse2"))
        inv2 (or (get built-in-inverse2s slot) declared2)
        step (if (and (arg-present? second-arg) (some? inv2))
               (install-inverses0 kb second-arg inv2
                                  (args-headed (kb/arg1 invframe)
                                               (term/cons-cell
                                                invval
                                                (term/cdr (term/cdr (term/cdr invframe)))))
                                  slot situation query)
               step)
        kb (:kb step)
        query (:query step)
        inv12 (unique-stored kb slot (symbol "inverse12"))
        step (if (and (arg-present? second-arg) (some? inv12))
               (add-val kb invval inv12
                        (args-headed (kb/arg2 invframe)
                                     (term/cons-cell
                                      (kb/arg1 invframe)
                                      (term/cdr (term/cdr (term/cdr invframe)))))
                        :install-inverses? true
                        :situation situation
                        :query query)
               step)
        third-arg (kb/arg3 invframe)
        inv3 (unique-stored (:kb step) slot (symbol "inverse3"))]
    (if (and (arg-present? third-arg) (some? inv3))
      (install-inverses0 (:kb step) third-arg inv3
                         (args-headed (kb/arg1 invframe)
                                      (term/cons-cell
                                       (kb/arg2 invframe)
                                       (term/cons-cell
                                        invval
                                        (term/cdr (term/cdr (term/cdr (term/cdr invframe)))))))
                         slot situation (:query step))
      step)))

(defn- install-inverses0
  [kb invframe0 invslot invval slot situation query]
  (let [invframe (dereference kb invframe0)
        existing (read-vals kb invframe invslot own-properties situation true)]
    (cond
      (and (kb/kb-object? invframe)
           (not (non-inverse-concept? invframe))
           (not (utils/member? invval (:value existing) utils/equal?)))
      (install-inverse-link (:kb existing) invframe invslot invval situation query
                            (kb/km-args? invval))

      (kb/km-args? invframe)
      (install-args (:kb existing) invframe invslot invval slot situation query)

      :else (result (:kb existing) nil query))))

(defn install-inverses
  "Install the inverse link for each ground value.

  A knowledge-base object and an :args value are linked. An & expression
  is opened and its pieces are linked in this same situation. Anything
  else, including an existential, is left as data. A slot that ignores
  inverses is skipped. The Lisp opens an & expression and then leaves
  the situation argument outside that call. The pieces are installed
  here in the situation already chosen for the assertion."
  [kb frame slot values situation query]
  (cond
    (not (:installing-inverses? kb)) (result kb nil query)
    (not (utils/lisp-list? values))
    (throw (ex-info "Inverse installation expects a list of values."
                    {:values values :frame frame :slot slot}))
    (non-inverse-slot? kb slot) (result kb nil query)
    :else
    (let [invslot (invert-slot kb slot)]
      (loop [values values
             kb kb
             query query]
        (cond
          (nil? values) (result kb nil query)
          (not (term/cons? values)) (dotted! values)
          :else
          (let [value (term/car values)
                step (cond
                       (or (kb/kb-object? value) (kb/km-args? value))
                       (install-inverses0 kb value invslot frame slot situation query)

                       (kb/&-expr? value)
                       (install-inverses kb frame slot (kb/&-expr-to-vals value)
                                         situation query)

                       :else (result kb nil query))]
            (recur (term/cdr values) (:kb step) (:query step))))))))

(defn- but-last
  [coll]
  (loop [coll coll
         acc []]
    (cond
      (nil? coll) (term/build-list acc nil)
      (not (term/cons? coll)) (dotted! coll)
      (nil? (term/cdr coll)) (term/build-list acc nil)
      :else (recur (term/cdr coll) (conj acc (term/car coll))))))

(defn- last-element
  [coll]
  (loop [coll coll]
    (cond
      (nil? coll) nil
      (not (term/cons? coll)) (dotted! coll)
      (nil? (term/cdr coll)) (term/car coll)
      :else (recur (term/cdr coll)))))

(defn- first-matching-tail
  "The tail of the first group that contains item under equal?."
  [item groups]
  (loop [groups groups]
    (cond
      (nil? groups) nil
      (not (term/cons? groups)) (dotted! groups)
      :else
      (if-let [tail (equal-tail item (term/car groups))]
        tail
        (recur (term/cdr groups))))))

(defn add-val
  "Add one value to a slot.

  An ordinary slot appends. A subsumers or subsumees slot inserts at
  the front. A value that is structurally equal is left where it is,
  and the result is the tail of the values that starts at that value.
  1 and 1.0 are both kept. A single-valued slot joins the values with &
  and installs an inverse only for the new value. A more specific class
  is not removed: that filter is is-subclass-of, which waits for the
  taxonomy. When the values are themselves a && expression, a value
  already in some value list is left there and the result is that tail.
  Otherwise the value is appended to the last value list. The result is
  the frame when the slot changes."
  [kb frame slot value & {:keys [install-inverses? situation query]
                          :or {install-inverses? true query empty-query}}]
  (let [situation (chosen-situation kb situation frame slot)
        found (get-vals kb frame slot :situation situation :query query)
        kb (:kb found)
        old (if (single-valued-slot? kb slot) (kb/un-andify (:value found)) (:value found))
        tail (equal-tail value old)]
    (cond
      (nil? old)
      (put-vals kb frame slot (term/km-list value)
                :install-inverses? install-inverses?
                :situation situation
                :query query)

      (some? tail) (result kb tail query)

      (single-valued-slot? kb slot)
      (let [stored (put-vals kb frame slot
                             (kb/val-to-vals
                              (kb/vals-to-&-expr (append-element old value)))
                             :install-inverses? false
                             :situation situation
                             :query query)]
        (if install-inverses?
          (let [linked (install-inverses (:kb stored) frame slot
                                         (term/km-list value) situation (:query stored))]
            (assoc linked :value frame))
          stored))

      (or (remove-subsumers-slot? kb slot) (remove-subsumees-slot? kb slot))
      (put-vals kb frame slot (term/cons-cell value old)
                :install-inverses? install-inverses?
                :situation situation
                :query query)

      (kb/&&-expr? old)
      (let [valsets (kb/&&-exprs-to-valsets old)
            found (first-matching-tail value valsets)]
        (if (some? found)
          (result kb found query)
          (put-vals kb frame slot
                    (kb/valsets-to-&&-exprs
                     (utils/append-lists
                      (term/km-list (but-last valsets)
                                    (term/km-list
                                     (append-element (last-element valsets) value)))))
                    :install-inverses? install-inverses?
                    :situation situation
                    :query query)))

      :else
      (put-vals kb frame slot (append-element old value)
                :install-inverses? install-inverses?
                :situation situation
                :query query))))

(defn uninstall-inverses
  "Remove the inverse link for each ground value.

  A value is removed when it is a knowledge-base object and the inverse
  slot holds this frame under eql?. An & expression is left in place.
  Explanations are not recorded yet, so there is nothing to delete.
  The slot's new values are the dereferenced list without this frame."
  [kb frame slot values situation query]
  (cond
    (not (utils/lisp-list? values))
    (throw (ex-info "Inverse removal expects a list of values."
                    {:values values :frame frame :slot slot}))
    (non-inverse-slot? kb slot) (result kb nil query)
    :else
    (let [invslot (invert-slot kb slot)]
      (loop [values values
             kb kb
             query query]
        (cond
          (nil? values) (result kb nil query)
          (not (term/cons? values)) (dotted! values)
          :else
          (let [value (dereference kb (term/car values))]
            (if-not (and (kb/kb-object? value)
                         (not (non-inverse-concept? value)))
              (recur (term/cdr values) kb query)
              (let [found (get-vals kb value invslot
                                    :situation situation
                                    :query query)
                    existing (:value found)]
                (if-not (utils/member? frame existing)
                  (recur (term/cdr values) (:kb found) (:query found))
                  (let [stored (put-vals (:kb found) value invslot
                                         (utils/remove-items frame existing)
                                         :install-inverses? false
                                         :situation situation
                                         :query (:query found))]
                    (recur (term/cdr values) (:kb stored) (:query stored))))))))))))

(defn add-vals
  "Add each value, in order.

  The result is that list of values. This is add-vals."
  [kb frame slot values & {:keys [install-inverses? situation query]
                           :or {install-inverses? true query empty-query}}]
  (let [situation (chosen-situation kb situation frame slot)]
    (loop [pending values
           kb kb
           query query]
      (cond
        (nil? pending) (result kb values query)
        (not (term/cons? pending)) (dotted! pending)
        :else
        (let [step (add-val kb frame slot (term/car pending)
                            :install-inverses? install-inverses?
                            :situation situation
                            :query query)]
          (recur (term/cdr pending) (:kb step) (:query step)))))))

(defn delete-val
  "Remove one value from a slot.

  Stored values are dereferenced and then de-duplicated. A single-valued
  slot is split on & first and joined again afterwards. A value that is
  not a member under equal? is left in place: :value is nil and :message
  says so. Nothing is printed. 1 and 1.0 are different under equal?, so
  deleting one leaves the other. A later value that km-equal? would
  collapse is invisible to this membership test, because
  remove-dup-instances runs first. The inverse of a removed value is
  uninstalled. The result is true when a value was removed."
  [kb frame slot value & {:keys [uninstall-inverses? situation query]
                          :or {uninstall-inverses? true query empty-query}}]
  (let [situation (chosen-situation kb situation frame slot)
        found (get-vals kb frame slot :situation situation :query query)
        kb (:kb found)
        query (:query found)
        collapsed (kb/remove-dup-instances (:value found))
        old (if (single-valued-slot? kb slot) (kb/un-andify collapsed) collapsed)]
    (if-not (utils/member? value old utils/equal?)
      (assoc (result kb nil query)
             :message (str "Trying to delete non-existent value " value
                           " on (the " slot " of " frame ")."))
      (let [kept (utils/remove-items value old :test utils/equal?)
            replacement (if (single-valued-slot? kb slot)
                          (let [joined (kb/vals-to-&-expr kept)]
                            (when (some? joined) (term/km-list joined)))
                          kept)
            stored (put-vals kb frame slot replacement
                             :install-inverses? false
                             :situation situation
                             :query query)]
        (if uninstall-inverses?
          (assoc (uninstall-inverses (:kb stored) frame slot (term/km-list value)
                                     situation (:query stored))
                 :value true)
          (assoc stored :value true))))))

(defn delete-slot
  "Remove one slot, and its inverse links, from a frame.

  The frame name is followed when it is bound. An unknown frame is an
  error. A single-valued slot is split on & before the inverses are
  removed, so each piece is uninstalled."
  [kb frame0 slot & {:keys [delete-inverses? situation query]
                     :or {delete-inverses? true query empty-query}}]
  (let [situation (chosen-situation kb situation frame0 slot)
        frame (dereference kb frame0)]
    (if-not (known-frame? kb frame)
      (throw (ex-info (str frame " is not a known frame.") {:frame frame :slot slot}))
      (let [found (get-vals kb frame slot :situation situation :query query)
            values (if (single-valued-slot? (:kb found) slot)
                     (kb/un-andify (:value found))
                     (:value found))
            cleared (if delete-inverses?
                      (uninstall-inverses (:kb found) frame slot values
                                          situation (:query found))
                      found)
            stored (put-vals (:kb cleared) frame slot nil
                             :install-inverses? false
                             :situation situation
                             :query (:query cleared))]
        (assoc stored :value true)))))

(defn- uninstall-facet
  [kb frame situation facet query]
  (let [found (get-slotsvals kb frame :facet facet :situation situation :query query)]
    (loop [slots (:value found)
           kb (:kb found)
           query (:query found)]
      (cond
        (nil? slots) {:kb kb :query query}
        (not (term/cons? slots)) (dotted! slots)
        :else
        (let [pair (term/car slots)
              step (uninstall-inverses kb frame (slot-in pair) (vals-in pair)
                                       situation query)]
          (recur (term/cdr slots) (:kb step) (:query step)))))))

(defn- uninstall-frame-inverses
  [kb frame query]
  (loop [names (into [] (concat (:situations kb) (:theories kb)))
         kb kb
         query query]
    (if (empty? names)
      {:kb kb :query query}
      (let [situation (first names)
            own (uninstall-facet kb frame situation own-properties query)
            definition (uninstall-facet (:kb own) frame situation own-definition
                                        (:query own))]
        (recur (rest names) (:kb definition) (:query definition))))))

(defn delete-frame
  "Remove a known frame, its bindings, and its inverse links.

  The name is followed first, unless dereference? is false. An unknown
  frame is an error. Inverses are taken off own-properties and
  own-definition in every situation and theory, including a facet that
  has no values. The definition flag is not consulted and is not set by
  storage. The name stays on the situation and theory lists. It is
  recorded on the deleted list and taken off the object stack. It is
  not uninterned. Other frames keep bindings that point at it."
  [kb frame0 & {:keys [delete-inverses? query dereference?]
                :or {delete-inverses? true query empty-query dereference? true}}]
  (let [frame (if dereference? (dereference kb frame0) frame0)]
    (if-not (known-frame? kb frame)
      (throw (ex-info (str frame " is not a known frame.") {:frame frame}))
      (let [cleared (if delete-inverses?
                      (uninstall-frame-inverses kb frame query)
                      {:kb kb :query query})
            query (remove-from-stack (:kb cleared) (:query cleared) frame)]
        (result (forget-frame (:kb cleared) frame) true query)))))

(defn- reorder-slotsvals
  "Put an instance-of pair first, so later checks see the classes."
  [slotsvals]
  (let [instance-of (symbol "instance-of")
        found (find-slot slotsvals instance-of)]
    (if (nil? found)
      slotsvals
      (term/cons-cell found (remove-slot slotsvals instance-of)))))

(defn- delete-each
  [kb frame slot values situation query]
  (loop [values values
         kb kb
         query query]
    (cond
      (nil? values) {:kb kb :query query}
      (not (term/cons? values)) (dotted! values)
      :else
      (let [step (delete-val kb frame slot (term/car values)
                             :situation situation
                             :query query)]
        (recur (term/cdr values) (:kb step) (:query step))))))

(defn- overwrite-previous
  "Drop inverse links that an overwriting assertion replaces.

  Values that leave this slot lose their inverse. When the inverse slot
  is single-valued, other frames that hold one of the new values are
  deleted too."
  [kb instance slot add-values old-values situation query]
  (let [leaving (absent? old-values add-values utils/eql?)
        cleared (uninstall-inverses kb instance slot leaving situation query)
        kb (:kb cleared)
        query (:query cleared)
        invslot (invert-slot kb slot)]
    (if-not (single-valued-slot? kb invslot)
      {:kb kb :query query}
      (loop [values add-values
             kb kb
             query query]
        (cond
          (nil? values) {:kb kb :query query}
          (not (term/cons? values)) (dotted! values)
          :else
          (let [value (term/car values)]
            (if-not (kb/kb-object? value)
              (recur (term/cdr values) kb query)
              (let [found (get-vals kb value invslot
                                    :situation situation
                                    :query query)
                    others (utils/remove-items instance (:value found))
                    gone (delete-each (:kb found) value invslot others
                                      situation (:query found))]
                (recur (term/cdr values) (:kb gone) (:query gone))))))))))

(defn- copy-domain-and-range
  "Copy domain and range onto the inverse slot, in *Global.

  The pairs come from the assertion as it was written. Self has not
  been replaced. A slot that ignores inverses is left alone."
  [kb instance original facet query]
  (if-not (utils/eql? facet own-properties)
    (result kb instance query)
    (let [domain (find-slot original (symbol "domain"))
          range-pair (find-slot original (symbol "range"))
          inverse (invert-slot kb instance)
          copy? (not (non-inverse-slot? kb instance))
          step (if (and (some? domain) copy? (some? inverse))
                 (add-vals kb inverse (symbol "range") (vals-in domain)
                           :situation term/global-situation
                           :query query)
                 (result kb nil query))
          step (if (and (some? range-pair) copy? (some? inverse))
                 (add-vals (:kb step) inverse (symbol "domain") (vals-in range-pair)
                           :situation term/global-situation
                           :query (:query step))
                 step)]
      (assoc step :value instance))))

(defn add-slotsvals
  "Add slot values to a frame.

  Own facets replace Self, including Self inside quote, when bind-self?
  is true. instance-of is applied first. An ordinary slot merges through
  compute-new-vals. overwriting and appending are the Lisp symbols, not
  keywords. overwriting drops inverse links of values that leave and,
  when the inverse slot is single-valued, deletes other holders of the
  new value. Nil from the merge means the slot is left as it is, unless
  the combine symbol is overwriting. Inverses are installed for the
  added values on an own facet, not for the combined list. domain and
  range are copied onto the inverse in *Global from the pairs as
  written. The Lisp discards this return value. :value is the frame.
  A subsumption check can update the knowledge base even when the slot
  value does not change. :errors, :warnings, and :error-structures come
  back with that result. A refusal is returned unchanged."
  [kb instance slotsvals & {:keys [facet situation combine-values-by bind-self? query
                                   errors warnings error-structures]
                            :or {facet own-properties bind-self? true query empty-query
                                 errors [] warnings [] error-structures []}}]
  (when-not (contains? facet-set facet)
    (throw (ex-info "A facet is one of the four frame facets." {:facet facet})))
  (let [query (if (or (not (known-frame? kb instance))
                      (:active-obj-stack? kb))
                (push-to-obj-stack kb query instance)
                query)
        prepared (if (and (contains? own-facets facet) bind-self?)
                   (bind-self slotsvals instance)
                   slotsvals)
        carry (fn [kb query errors warnings structures]
                {:kb kb
                 :query query
                 :errors (vec (or errors []))
                 :warnings (vec (or warnings []))
                 :error-structures (vec (or structures []))})]
    (loop [pairs (reorder-slotsvals prepared)
           bag (carry kb query errors warnings error-structures)]
      (cond
        (nil? pairs)
        (assoc (copy-domain-and-range (:kb bag) instance slotsvals facet (:query bag))
               :errors (:errors bag)
               :warnings (:warnings bag)
               :error-structures (:error-structures bag))
        (not (term/cons? pairs)) (dotted! pairs)
        :else
        (let [pair (term/car pairs)
              slot (slot-in pair)
              kb (:kb bag)
              query (:query bag)
              add-values0 (vals-in pair)
              add-values (cond
                           (single-valued-slot? kb slot) (kb/un-andify add-values0)
                           (remove-subsumers-slot? kb slot) (dedup-earlier add-values0)
                           (remove-subsumees-slot? kb slot) (dedup-earlier add-values0)
                           :else add-values0)
              situation0 (target-situation kb
                                           (if (nil? situation)
                                             (current-situation kb)
                                             situation)
                                           instance slot add-values)
              old-found (get-vals kb instance slot
                                  :facet facet
                                  :situation situation0
                                  :query query)
              old-values (:value old-found)
              cleaned (if (and (utils/eql? combine-values-by overwriting)
                               (utils/eql? facet own-properties))
                        (overwrite-previous (:kb old-found) instance slot
                                            add-values old-values situation0
                                            (:query old-found))
                        {:kb (:kb old-found) :query (:query old-found)})
              base (carry (:kb cleaned) (:query cleaned)
                          (:errors bag) (:warnings bag) (:error-structures bag))
              merged (if (or (nil? old-values)
                             (utils/eql? combine-values-by overwriting))
                       (assoc base :value
                              (if (single-valued-slot? (:kb cleaned) slot)
                                (kb/val-to-vals (kb/vals-to-&-expr add-values))
                                add-values))
                       (compute-new-vals base slot old-values
                                         add-values combine-values-by))]
          (if (store-refused? merged)
            merged
            (let [new-values (:value merged)
                  kb (:kb merged)
                  query (if (:active-obj-stack? kb)
                          (push-all kb (:query merged) add-values)
                          (:query merged))
                  bag (carry kb query
                             (:errors merged) (:warnings merged)
                             (:error-structures merged))]
              (if (or (some? new-values)
                      (utils/eql? combine-values-by overwriting))
                (let [stored (put-vals kb instance slot new-values
                                       :facet facet
                                       :install-inverses? false
                                       :situation situation0
                                       :query query)
                      linked (if (contains? own-facets facet)
                               (install-inverses (:kb stored) instance slot add-values
                                                 situation0 (:query stored))
                               stored)]
                  (recur (term/cdr pairs)
                         (carry (:kb linked) (:query linked)
                                (:errors bag) (:warnings bag)
                                (:error-structures bag))))
                (recur (term/cdr pairs) bag)))))))))

(defn create-instance-name
  "The next anonymous name for parent.

  The counter starts at 0, and the first name for Person is _Person1.
  The name is not added to the knowledge base. A name that is already
  known is skipped. An unknown parent is accepted and draws no warning.
  prefix defaults to _."
  [kb parent & {:keys [prefix query] :or {prefix "_" query empty-query}}]
  (when-not (term/lisp-symbol? parent)
    (throw (ex-info "An instance name is built from a symbol." {:parent parent})))
  (loop [kb (update kb :counter inc)]
    (let [frame (symbol (str prefix (term/symbol-name parent) (:counter kb)))]
      (if (known-raw? kb frame)
        (recur (update kb :counter inc))
        (result kb frame query)))))

(defn- stored?
  [kb frame slot & {:keys [facet situation]}]
  (some? (:value (get-vals kb frame slot
                           :facet (or facet own-properties)
                           :situation situation))))

(defn- global-facet?
  "True when the global facet property is present.

  This is the Lisp get of member-properties or member-definition. It is
  not a situation facet, and the frame name is not followed."
  [kb frame facet]
  (some? (get-in kb [:frames frame :facets facet])))

(defn class?
  "True for a built-in class, or a frame with class structure.

  superclasses makes a class. So does instances, subclasses, or a global
  member facet, when the frame has no instance-of. Thing is a class
  before a frame is stored for it. thing, in lower case, is not."
  [kb class-name]
  (or (contains? built-in-classes class-name)
      (and (kb/kb-object? class-name)
           (or (stored? kb class-name (symbol "superclasses"))
               (and (not (stored? kb class-name (symbol "instance-of")))
                    (or (stored? kb class-name (symbol "instances"))
                        (global-facet? kb class-name member-properties)
                        (global-facet? kb class-name member-definition)
                        (stored? kb class-name (symbol "subclasses"))))))))

(defn slot?
  "True for a built-in slot, or a frame whose global instance-of includes Slot.

  Subclasses of Slot are not consulted. That walk waits for the taxonomy."
  [kb slot]
  (and (term/lisp-symbol? slot)
       (or (built-in-slot? slot)
           (and (kb/kb-object? slot)
                (utils/member?
                 (symbol "Slot")
                 (:value (get-vals kb slot (symbol "instance-of")
                                   :situation term/global-situation)))))))

(defn simple-slot?
  "True when Slot's global instances include this symbol.

  This is simple-slotp. It does not walk subclasses of Slot."
  [kb slot]
  (and (term/lisp-symbol? slot)
       (utils/member?
        slot
        (:value (get-vals kb (symbol "Slot") (symbol "instances")
                          :situation term/global-situation)))))

(defn anonymous-instance?
  "True when the dereferenced name starts with _.

  This is anonymous-instancep."
  [kb instance]
  (let [instance (dereference kb instance)]
    (and (term/km-symbol? instance)
         (let [label (term/symbol-name instance)]
           (and (pos? (count label))
                (= \_ (nth label 0)))))))

(defn named-instance?
  "True when the value is not an anonymous instance.

  This is named-instancep."
  [kb instance]
  (not (anonymous-instance? kb instance)))

(defn an-instance?
  "True when the value is an instance.

  An anonymous name, a number, a string, a function, a description, and
  a structured list are instances. A knowledge-base object with
  instance-of on an own facet is an instance too. The frame name is
  followed for that lookup. This is is-an-instance."
  [kb instance]
  (or (anonymous-instance? kb instance)
      (number? instance)
      (string? instance)
      (fn? instance)
      (kb/description? instance)
      (term/structured-list? instance)
      (and (kb/kb-object? instance)
           (or (stored? kb instance (symbol "instance-of") :facet own-properties)
               (stored? kb instance (symbol "instance-of") :facet own-definition)))))

(defn orphan?
  "True for a knowledge-base object with no taxonomic slot and no built-in name.

  A symbol that was never stored is an orphan. Thing is not, because
  the name is built in. This is orphanp."
  [kb concept]
  (and (kb/kb-object? concept)
       (not (stored? kb concept (symbol "superclasses")))
       (not (stored? kb concept (symbol "subclasses")))
       (not (stored? kb concept (symbol "instances")))
       (not (stored? kb concept (symbol "instance-of")))
       (not (built-in-concept? concept))))

(defn- note-frame
  [kb frame]
  (if (known-raw? kb frame)
    kb
    (store-frame kb frame {:facets {}})))

(defn- add-global
  [kb frame slot value]
  (:kb (add-val kb frame slot value
                :situation term/global-situation
                :query empty-query)))

(defn- built-in-slot-class
  [slot]
  (cond
    (contains? bag-aggregation-slots slot) (symbol "Bag-Aggregation-Slot")
    (contains? set-aggregation-slots slot) (symbol "Set-Aggregation-Slot")
    :else (symbol "Slot")))

(defn- add-instance-of
  [kb frame class-name]
  (if (contains? kb/reserved-keywords frame)
    ;; append is a built-in slot and a reserved keyword. put-vals refuses
    ;; that name. The vocabulary writes the frame directly and links the
    ;; inverse without calling put-vals on append.
    (let [written (write-facet kb frame own-properties
                               (update-slot (get-in kb [:frames frame :facets own-properties])
                                            (symbol "instance-of")
                                            (term/km-list class-name)))]
      (:kb (add-val written class-name (symbol "instances") frame
                    :install-inverses? false
                    :situation term/global-situation
                    :query empty-query)))
    (add-global kb frame (symbol "instance-of") class-name)))

(defn- install-vocabulary
  [kb]
  (let [kb (reduce (fn [kb [child parent]]
                     (add-global kb child (symbol "superclasses") parent))
                   kb
                   superclass-links)
        kb (reduce (fn [kb slot]
                     (add-instance-of kb slot (built-in-slot-class slot)))
                   kb
                   built-in-slot-order)
        kb (reduce (fn [kb [frame class-name]]
                     (add-instance-of kb frame class-name))
                   kb
                   instance-of-links)]
    (reduce note-frame kb unlinked-instances)))

(defn reset
  "Clear this knowledge base and rebuild the built-in vocabulary.

  Frames, bindings, and the situation and theory name lists are cleared.
  The gensym counter returns to 0. The current situation returns to
  *Global. The default fluent status returns to *Fluent, and instance-of
  returns to non-fluent. The optimization flags return to false.
  Classification returns to enabled. The deleted-name list is kept.
  Dereferencing, inverse installation, the active object stack, and the
  unstackable-instance list keep the settings they had. :value is true.
  The returned query has an empty object stack and an empty goal stack.
  Instances recorded as being unified, and the inference counters, stay
  on the query. The (reset-kb) command calls this and answers (t). A
  top-level evaluation has already cleared those counters. The Lisp
  prints a reset line. This prints nothing."
  [kb & {:keys [query] :or {query empty-query}}]
  (let [flags (select-keys kb [:dereferencing-on? :allow-ununify?
                                :installing-inverses? :active-obj-stack?
                                :unstackable-instances])
        deleted (or (:deleted kb) [])
        built (assoc (install-vocabulary (knowledge-base)) :deleted deleted)]
    (result (merge built flags) true
            (assoc (or query empty-query) :obj-stack nil :goal-stack nil))))
