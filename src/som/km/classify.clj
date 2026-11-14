(ns som.km.classify
  "Definitions and classification, from frame-io.lisp.

  has-definition stores a member or own definition and indexes it on
  the parent named by instance-of. classify tests an instance against
  those definitions and against a prototype's slotted scope. A success
  adds the class, or unifies a coreferential instance.

  The interpreter, the slot reader, and load pass km-int in. This
  namespace does not require them. Unification calls back through
  *classify-survivor*, which is installed when this namespace loads."
  (:require [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.stack :as stack]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.unify :as unify]
            [som.km.utils :as utils]))

(def ^:private neq-slot (symbol nil "/=="))
(def ^:private thing (symbol "Thing"))
(def ^:private self-symbol (symbol "Self"))
(def ^:private instance-of (symbol "instance-of"))
(def ^:private own-definition (symbol "own-definition"))
(def ^:private member-definition (symbol "member-definition"))

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- adopt
  "Take the store's knowledge base. A missing query or note list stays."
  [state stored]
  (cond-> (assoc state :kb (:kb stored))
    (contains? stored :query) (assoc :query (:query stored))
    (contains? stored :errors) (assoc :errors (vec (:errors stored)))
    (contains? stored :warnings) (assoc :warnings (vec (:warnings stored)))
    (contains? stored :error-structures)
    (assoc :error-structures (vec (:error-structures stored)))
    (contains? stored :text) (assoc :text (:text stored))))

(defn- bump
  [state key]
  (update-in state [:query key] (fnil inc 0)))

(defn- list-elements
  [value]
  (cond
    (nil? value) []
    (vector? value) value
    (term/cons? value) (utils/elements value)
    :else []))

(defn- triggers?
  "True when the changed slots can start a classification.

  :unspecified is a slot read or a bare classify. Nil, and a list that
  only names /==, do not. An empty list stays empty: the slotless flag
  starts true and does not override that."
  [slots]
  (cond
    (= slots :unspecified) true
    (nil? slots) false
    (vector? slots) (boolean (some #(not (utils/eql? % neq-slot)) slots))
    (term/cons? slots)
    (boolean (some #(not (utils/eql? % neq-slot)) (utils/elements slots)))
    :else true))

(defn- call-km
  "Evaluate expr. The answer list comes back beside the restored state.

  A refusal is returned as it is. An ordinary result keeps the caller's
  value, fail mode, target, and current expression."
  [state expr km-int]
  (let [saved (select-keys state [:fail-mode :target :current-expr :value])
        ran (km-int state expr)]
    (if (refused? ran)
      [ran nil]
      [(merge (dissoc ran :ok :slots :bindings :problem :equality-check?) saved)
       (:value ran)])))

(defn- child-key
  [facet]
  (cond
    (utils/eql? facet own-definition) :defined-instances
    (utils/eql? facet member-definition) :defined-subclasses
    :else (throw (ex-info "A definition facet is own-definition or member-definition."
                          {:facet facet}))))

(defn- child-list
  [kb parent key]
  (if (= key :defined-subclasses)
    (frame/defined-subclasses kb parent)
    (frame/defined-instances kb parent)))

(defn- most-general-first
  "The classes with the most general first.

  A class whose superclasses miss the rest of the list is emitted.
  The rest then starts again. A class that is not general moves to the
  end. When that class returns to the front, the remainder stays in
  that order."
  [kb classes]
  (loop [classes (vec classes)
         marker nil
         kb kb
         acc []]
    (cond
      (empty? classes) [kb acc]
      (and (some? marker) (utils/eql? (first classes) marker))
      [kb (into acc classes)]
      :else
      (let [class (first classes)
            rest (vec (rest classes))
            supers (taxonomy/all-superclasses0 kb class)
            kb (:kb supers)
            rest-list (term/build-list rest nil)
            general? (not (some #(utils/member? % rest-list)
                                (list-elements (:value supers))))]
        (if general?
          (recur rest nil kb (conj acc class))
          (recur (conj rest class) (or marker class) kb acc))))))

(defn- most-specific-first
  [kb classes]
  (let [[kb ordered] (most-general-first kb classes)]
    [kb (vec (reverse ordered))]))

(defn point-parents
  "Index frame on each parent's defined children, most specific first.

  An empty parent list records the instance-of error and indexes
  nothing. A parent that is not a frame yet becomes one. A frame
  already on the list stays where it is."
  [state frame parents facet]
  (if (nil? parents)
    (errors/report-error state :user-error
                         "%s:%nDefinition for %s must include an `instance-of' slot,%ndeclaring the most general superclass of %s.%nContinuing, but ignoring definition..."
                         (print/km-format frame)
                         (print/km-format frame)
                         (print/km-format frame))
    (let [key (child-key facet)]
      (loop [parents parents
             state state]
        (cond
          (or (nil? parents) (not (term/cons? parents))) state
          :else
          (let [parent (term/car parents)
                existing (list-elements (child-list (:kb state) parent key))]
            (if (some #(utils/eql? frame %) existing)
              (recur (term/cdr parents) state)
              (let [[kb ordered] (most-specific-first (:kb state)
                                                      (into [frame] existing))]
                (recur (term/cdr parents)
                       (assoc state :kb (frame/set-defined-children
                                         kb parent key ordered)))))))))))

(defn- unpoint
  [kb frame parents key]
  (loop [parents parents
         kb kb]
    (cond
      (or (nil? parents) (not (term/cons? parents))) kb
      :else
      (let [parent (term/car parents)]
        (if-not (and (kb/kb-object? parent) (frame/known-frame? kb parent))
          (recur (term/cdr parents) kb)
          (let [children (list-elements (child-list kb parent key))
                kept (filterv #(not (utils/eql? frame %)) children)]
            (recur (term/cdr parents)
                   (if (= (count kept) (count children))
                     kb
                     (frame/set-defined-children kb parent key kept)))))))))

(defn- situations-and-theories
  [kb]
  (into [] (concat (frame/situations kb) (frame/theories kb))))

(defn- clear-facet
  [state frame facet own?]
  (reduce (fn [state situation]
            (let [found (frame/get-slotsvals (:kb state) frame
                                             :facet facet
                                             :situation situation
                                             :query (:query state))
                  state (adopt state found)]
              (loop [pairs (:value found)
                     state state]
                (cond
                  (or (nil? pairs) (not (term/cons? pairs))) state
                  :else
                  (let [pair (term/car pairs)
                        slot (frame/slot-in pair)
                        values (frame/vals-in pair)
                        cleared (if own?
                                 (let [gone (frame/uninstall-inverses
                                             (:kb state) frame slot values
                                             situation (:query state))]
                                   (frame/put-vals (:kb gone) frame slot nil
                                                   :facet facet
                                                   :install-inverses? false
                                                   :situation situation
                                                   :query (:query gone)))
                                 (frame/put-vals (:kb state) frame slot nil
                                                 :facet facet
                                                 :install-inverses? false
                                                 :situation situation
                                                 :query (:query state)))]
                    (recur (term/cdr pairs) (adopt state cleared)))))))
          state
          (situations-and-theories (:kb state))))

(defn remove-definition
  "Delete the definition stored on frame's facet, in every situation.

  The parent index loses frame. An own definition also drops inverse
  links. A member definition does not. The definitions flag stays."
  [state frame facet]
  (let [key (child-key facet)
        found (frame/get-vals (:kb state) frame instance-of
                              :facet facet
                              :situation term/global-situation
                              :query (:query state))
        state (adopt state found)
        kb (unpoint (:kb state) frame (:value found) key)]
    (clear-facet (assoc state :kb kb) frame facet (utils/eql? facet own-definition))))

(defn- description-head
  "The class the description is tested as.

  The Lisp head is Thing. The head here is the instance's current
  class. The definition's own instance-of stays in the slot pairs."
  [kb instance]
  (let [classes (taxonomy/immediate-classes kb instance)]
    [(:kb classes) (or (term/car (:value classes)) thing)]))

(defn- quote-description
  [head slots]
  (term/km-list (symbol "quote")
                (term/build-list [(symbol "a") head (symbol "with")] slots)))

(defn- explanation-form
  [class slots]
  (term/build-list [(symbol "every") class (symbol "has-definition")] slots))

(defn- satisfied-definition
  [state instance class facet km-int]
  (let [found (frame/get-slotsvals (:kb state) class
                                   :facet facet
                                   :situation term/global-situation
                                   :query (:query state))
        slots (frame/bind-self (:value found) instance)
        [kb head] (description-head (:kb found) instance)
        state (bump (adopt state (assoc found :kb kb)) :classifications-attempted)
        [state value] (call-km state
                               (term/km-list instance (symbol "is")
                                             (quote-description head slots))
                               km-int)]
    [state (boolean (and (not (refused? state)) (some? value)))
     (explanation-form class slots)]))

(defn- any-isa?
  [state instance classes]
  (loop [classes classes
         state state]
    (cond
      (or (nil? classes) (not (term/cons? classes))) [state false]
      :else
      (let [hit (taxonomy/isa? (:kb state) instance (term/car classes))
            state (adopt state hit)]
        (if (:value hit)
          [state true]
          (recur (term/cdr classes) state))))))

(defn- add-immediate-class
  [state instance0 parent explanation]
  (let [instance (frame/dereference (:kb state) instance0)
        situation (frame/target-situation (:kb state)
                                          (frame/current-situation (:kb state))
                                          instance
                                          instance-of
                                          (term/km-list parent))]
    (try
      (let [added (frame/add-val (:kb state) instance instance-of parent
                                 :situation situation
                                 :query (:query state))
            state (adopt state added)
            recorded (frame/record-explanation-for
                      (:kb state)
                      (term/km-list (symbol "the") instance-of (symbol "of") instance)
                      parent
                      explanation
                      :situation term/global-situation)]
        [(assoc (adopt state recorded) :kb (frame/un-done (:kb recorded) instance))
         true])
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (throw thrown)
          [(errors/report-error state :user-error "%s" (.getMessage thrown))
           false])))))

(defn- try-classifying
  [state instance parent km-int]
  (let [[state satisfied? explanation]
        (satisfied-definition state instance parent member-definition km-int)]
    (cond
      (refused? state) [state false]
      (not satisfied?) [state false]
      :else
      (let [props (frame/get-slotsvals (:kb state) parent
                                       :facet (symbol "member-properties")
                                       :situation term/global-situation
                                       :query (:query state))
            state (adopt state props)
            form (term/build-list [(symbol "a") parent (symbol "with")]
                                  (:value props))
            [state value] (call-km state
                                   (term/km-list instance (symbol "&?") form)
                                   km-int)]
        (cond
          (refused? state) [state false]
          (nil? value) [state false]
          :else
          (let [state (bump state :classifications-succeeded)]
            (add-immediate-class state instance parent explanation)))))))

(defn- classify-as-member
  [state instance parent km-int]
  (if-not (frame/are-some? (:kb state) :definitions)
    [state false]
    (loop [defined (frame/defined-subclasses (:kb state) parent)
           state state]
      (cond
        (or (nil? defined) (not (term/cons? defined))) [state false]
        :else
        (let [possible (term/car defined)
              classes (taxonomy/immediate-classes (:kb state) instance)
              state (adopt state classes)
              apart (taxonomy/disjoint-class-sets (:kb state)
                                                  (:value classes)
                                                  (term/km-list possible))
              state (adopt state apart)]
          (if (some? (:value apart))
            (recur (term/cdr defined) state)
            (let [[state member?] (any-isa? state instance (term/km-list possible))]
              (if member?
                (recur (term/cdr defined) state)
                (let [[state added?] (try-classifying state instance possible km-int)]
                  (cond
                    (refused? state) [state false]
                    added? [state true]
                    :else (recur (term/cdr defined) state)))))))))))

(defn- try-equating
  [state instance coref km-int]
  (let [[state satisfied? _]
        (satisfied-definition state instance coref own-definition km-int)]
    (cond
      (refused? state) [state false]
      (not satisfied?) [state false]
      :else
      (let [state (bump state :classifications-succeeded)
            [state value] (call-km state
                                   (term/km-list instance (symbol "&") coref)
                                   km-int)]
        (cond
          (refused? state) [state false]
          (some? value)
          [(assoc state :kb (frame/un-done (:kb state) instance)) true]
          :else
          [(errors/report-error state :user-error
                                "%s satisfies definition of %s but won't unify with it!"
                                (print/km-format instance)
                                (print/km-format coref))
           false])))))

(defn- classify-as-coreferential
  [state instance0 parent km-int]
  (if-not (frame/are-some? (:kb state) :definitions)
    [state false]
    (let [instance (frame/dereference (:kb state) instance0)]
      (loop [defined (frame/defined-instances (:kb state) parent)
             state state]
        (cond
          (or (nil? defined) (not (term/cons? defined))) [state false]
          :else
          (let [coref (frame/dereference (:kb state) (term/car defined))]
            (if (utils/eql? instance coref)
              (recur (term/cdr defined) state)
              (let [[state added?] (try-equating state instance coref km-int)]
                (cond
                  (refused? state) [state false]
                  added? [state true]
                  :else (recur (term/cdr defined) state))))))))))

(defn- substitute
  "Replace from with to, including inside quote."
  [expr from to]
  (cond
    (and (term/km-symbol? expr) (utils/eql? expr from)) to
    (term/cons? expr)
    (term/cons-cell (substitute (term/car expr) from to)
                    (substitute (term/cdr expr) from to))
    :else expr))

(defn- class-and-slots
  "(the-class Class) or (the-class Class with slots)."
  [expr]
  (when (and (kb/the-class? expr) (term/cons? (term/cdr expr)))
    (let [class (term/car (term/cdr expr))
          after (term/cdr (term/cdr expr))]
      (if (and (term/cons? after) (utils/eql? (term/car after) (symbol "with")))
        [class (term/cdr after)]
        [class nil]))))

(defn- the-class-values
  [values]
  (loop [values values
         acc []]
    (cond
      (or (nil? values) (not (term/cons? values))) (term/build-list acc nil)
      (kb/the-class? (term/car values)) (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- prototype-explanation
  [instance protoclass class slots]
  (frame/bind-self
   (term/build-list [(symbol "every") protoclass (symbol "has-definition")
                     (term/km-list instance-of (term/km-list class))]
                    slots)
   instance))

(defn- add-protoclasses
  [state instance protoclasses explanation]
  (loop [protoclasses protoclasses
         state state
         added? false]
    (cond
      (or (nil? protoclasses) (not (term/cons? protoclasses))) [state added?]
      :else
      (let [[state one?] (add-immediate-class state instance
                                              (term/car protoclasses)
                                              explanation)]
        (if one?
          (recur (term/cdr protoclasses) state true)
          [state added?])))))

(defn- satisfies-class-definition
  [state instance class-definition protoclasses km-int]
  (let [state (bump state :classifications-attempted)
        [state value] (call-km state
                               (term/km-list instance (symbol "isa") class-definition)
                               km-int)]
    (cond
      (refused? state) [(dissoc state :error :message) false nil]
      (nil? value) [state false nil]
      :else
      (let [[class slots] (class-and-slots class-definition)
            slots (explain/desource-decomment slots)
            explanation (prototype-explanation instance
                                               (term/car protoclasses)
                                               class
                                               slots)]
        [state true explanation]))))

(defn- pop-goal
  [state]
  (let [popped (stack/pop-from-goal-stack (:kb state) (:query state))]
    (adopt state popped)))

(defn- try-classifying-as-prototype
  [state instance protoclasses class-definition km-int]
  (let [goal (term/km-list instance (symbol "isa") (term/car protoclasses))
        pushed (stack/push-to-goal-stack (:kb state) (:query state) goal)
        state (adopt state pushed)]
    (try
      (let [[state satisfied? explanation]
            (satisfies-class-definition state instance class-definition
                                        protoclasses km-int)
            [state added?] (if satisfied?
                             (let [state (bump state :classifications-succeeded)]
                               (add-protoclasses state instance protoclasses explanation))
                             [state false])]
        [(pop-goal state) added?])
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state (pop-goal (:state data)))
                            thrown)))
          (throw thrown))))))

(defn- classify-as-prototype0
  [state instance protoroot km-int]
  (let [scope (frame/get-vals (:kb state) protoroot (symbol "prototype-scope")
                              :situation term/global-situation
                              :query (:query state))
        state (adopt state scope)
        definitions (the-class-values (substitute (:value scope) protoroot self-symbol))
        classes (frame/get-vals (:kb state) protoroot instance-of
                                :situation term/global-situation
                                :dereference? false
                                :query (:query state))
        state (adopt state classes)
        removed (taxonomy/remove-subsumers (:kb state) (:value classes))
        state (adopt state removed)
        protoclasses (:value removed)]
    ;; An empty instance-of would still try the scopes and report
    ;; success without adding a class, and the next pass would try
    ;; again. Stop instead.
    (cond
      (or (nil? definitions) (nil? protoclasses)) [state false]
      :else
      (let [[state member?] (any-isa? state instance protoclasses)]
        (if member?
          [state false]
          (loop [definitions definitions
                 state state]
            (cond
              (or (nil? definitions) (not (term/cons? definitions))) [state false]
              :else
              (let [parsed (class-and-slots (term/car definitions))
                  class (when parsed (first parsed))]
                (if (or (nil? class) (utils/member? class protoclasses))
                  (recur (term/cdr definitions) state)
                  (let [immediate (taxonomy/immediate-classes (:kb state) instance)
                        state (adopt state immediate)
                        apart (taxonomy/disjoint-class-sets (:kb state)
                                                            (:value immediate)
                                                            protoclasses)
                        state (adopt state apart)]
                    (if (some? (:value apart))
                      (recur (term/cdr definitions) state)
                      (let [[state added?]
                            (try-classifying-as-prototype
                             state instance protoclasses
                             (term/car definitions) km-int)]
                        (cond
                          added? [state true]
                          :else (recur (term/cdr definitions) state))))))))))))))

(defn prototype-fits?
  "True when prototype applies to instance.

  Membership in the prototype's classes succeeds without a description
  test. While that same instance is already being classified, only that
  membership is used, so the description test does not clone the
  prototype it is reading."
  [state instance prototype km-int]
  (let [found (frame/get-vals (:kb state) prototype instance-of
                              :situation term/global-situation
                              :dereference? false
                              :query (:query state))
        removed (taxonomy/remove-subsumers (:kb found) (:value found))
        state (assoc (adopt state found) :kb (:kb removed))
        [state member?] (any-isa? state instance (:value removed))]
    (cond
      member? [state true]
      (or (nil? km-int)
          (utils/eql? (get-in state [:query :am-classifying]) instance))
      [state false]
      :else
      (let [[state added?] (classify-as-prototype0 state instance prototype km-int)]
        (if (refused? state)
          [(dissoc state :error :message) false]
          [state added?])))))

(defn- classify-as-prototype
  [state instance parent km-int]
  (if-not (and (frame/are-some? (:kb state) :prototypes)
               (get-in state [:kb :runtime :prototype-classification-enabled?]))
    [state false]
    (loop [prototypes (frame/defined-prototypes (:kb state) parent)
           state state]
      (cond
        (or (nil? prototypes) (not (term/cons? prototypes))) [state false]
        :else
        (let [[state added?] (classify-as-prototype0 state instance
                                                     (term/car prototypes)
                                                     km-int)]
          (cond
            (refused? state) [state false]
            added? [state true]
            :else (recur (term/cdr prototypes) state)))))))

(defn- classify-one-parent
  [state instance parent km-int]
  (let [[state added?] (classify-as-member state instance parent km-int)]
    (cond
      (or (refused? state) added?) [state added?]
      :else
      (let [[state added?] (classify-as-coreferential state instance parent km-int)]
        (cond
          (or (refused? state) added?) [state added?]
          :else (classify-as-prototype state instance parent km-int))))))

(defn- classify0
  [state instance km-int]
  (cond
    (not (kb/kb-object? instance))
    [(errors/report-error state :user-error
                          "Attempt to classify a non-kb-object %s!"
                          (print/km-format instance))
     false]
    (not (frame/an-instance? (:kb state) instance))
    [state false]
    :else
    (let [parents (taxonomy/all-classes (:kb state) instance)
          state (adopt state parents)]
      (loop [parents (:value parents)
             state state]
        (cond
          (or (nil? parents) (not (term/cons? parents))) [state false]
          :else
          (let [[state added?] (classify-one-parent state instance
                                                    (term/car parents)
                                                    km-int)]
            (cond
              (refused? state) [state false]
              added? (classify0 state instance km-int)
              :else (recur (term/cdr parents) state))))))))

(defn- classify?
  [state instance slots km-int]
  (and (some? km-int)
       (frame/classification-enabled? (:kb state))
       (triggers? slots)
       (or (frame/are-some? (:kb state) :definitions)
           (and (frame/are-some? (:kb state) :prototype-definitions)
                (get-in state [:kb :runtime :prototype-classification-enabled?])))
       (not (utils/eql? (get-in state [:query :am-classifying]) instance))
       (or (not (frame/protoinstance? (:kb state) instance))
           (some? (frame/curr-prototype (:kb state))))))

(defn- finish
  [entered done previous]
  (let [done (assoc-in done [:query :am-classifying] previous)]
    (if (refused? done)
      done
      (merge (dissoc done :ok :slots :bindings :problem :equality-check?)
             (select-keys entered [:fail-mode :target :current-expr :value])))))

(defn classify
  "Reclassify instance when a definition or a prototype scope might apply.

  slots-that-changed is :unspecified, nil, or the slots just written.
  Nil and a list that only names /== do nothing. The same instance is
  not entered again while its classification is already running. The
  caller's value, fail mode, target, and current expression come back
  unless a definition test is not ported yet."
  [state instance km-int & {:keys [slots-that-changed]
                            :or {slots-that-changed :unspecified}}]
  (if-not (classify? state instance slots-that-changed km-int)
    state
    (let [previous (get-in state [:query :am-classifying])
          entered (assoc-in state [:query :am-classifying] instance)]
      (try
        (let [[done _] (classify0 entered instance km-int)]
          (finish entered done previous))
        (catch clojure.lang.ExceptionInfo thrown
          (if (errors/abort-exception? thrown)
            (let [data (ex-data thrown)
                  aborted (:state data)]
              (throw (ex-info (.getMessage thrown)
                              (assoc data :state
                                     (assoc-in aborted [:query :am-classifying]
                                               previous))
                              thrown)))
            (throw thrown)))))))

(alter-var-root #'unify/*classify-survivor*
  (fn [_]
    (fn [state instance km-int]
      (classify state instance km-int))))
