(ns som.km.interpreter
  "The Knowledge Machine interpreter.

  km and km-int share one dispatcher. The handler table is the Lisp
  alist in its original order, and the first match wins. A form this
  step does not run is still in that table, and it returns the
  not-ported refusal. Literals, arithmetic, comparisons, local assert
  and lookup, constraint forms recorded as data, and the commands from
  the goal-stack step are evaluated. Unification, inheritance,
  prototypes, and embedded Lisp are not.

  :value is the answer list. :errors, :error-structures, and :warnings
  collect the notes the Lisp returns beside the answer. An error is
  recorded and reasoning continues. Nothing is printed, and the
  debugger is not entered."
  (:require [clojure.string :as str]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.minimatch :as match]
            [som.km.print :as print]
            [som.km.slotvals :as slotvals]
            [som.km.stack :as stack]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def stack-ceiling
  "How deep a query may go before it stops the way a set depth limit would.

  The Lisp limit starts unset. This ceiling still applies, so a runaway
  query stops near the point a set *km-depth-limit* would. The test is
  depth greater than the ceiling."
  400)

(def ^:private infinity 999999)

(declare km-int km-unique-int)

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- nth-value
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- proper-length
  [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else nil)))

(defn- error-structure
  [state]
  (let [goals (get-in state [:query :goal-stack])]
    (if (term/cons? goals)
      (stack/stacked-expr (term/car goals))
      (:current-expr state))))

(defn- report-error
  "Record one error and continue.

  user-warning is a warning. The other kinds are errors. The text is
  kept, and the expression on the goal stack is kept with it. :value
  is left as it is. Nothing is printed."
  [state kind template & args]
  (let [prefix (case kind
                 :user-warning "WARNING! "
                 :program-error "PROGRAM ERROR! "
                 "ERROR! ")
        text (str/trim (str prefix (apply format template args)))]
    (if (= kind :user-warning)
      (update state :warnings (fnil conj []) text)
      (-> state
          (update :errors (fnil conj []) text)
          (update :error-structures (fnil conj []) (error-structure state))))))

(defn- refuse-text
  [state message]
  (assoc state
         :error "not-ported"
         :value nil
         :message message))

(defn- refuse
  [state _]
  (refuse-text state (str "This form is not ported yet: "
                          (print/km-format (:current-expr state))
                          ".")))

(defn- embedded-refusal
  [state expr extra]
  (refuse-text state
               (str "Embedded Lisp is refused: " (print/km-format expr) "."
                    (when extra (str " " extra)))))

(defn- pat
  "A vector becomes a Knowledge Machine list. A string becomes a symbol."
  [form]
  (cond
    (vector? form) (term/build-list (mapv pat form) nil)
    (string? form) (symbol nil form)
    :else form))

(defn- head-name
  "The lower-case name of a list's head symbol."
  [expr]
  (when (and (term/cons? expr) (term/km-symbol? (term/car expr)))
    (str/lower-case (name (term/car expr)))))

(defn- showme-head?
  [expr]
  (and (term/cons? expr)
       (contains? #{(symbol "showme") (symbol "showme-all")} (term/car expr))))

(def ^:private assertion-words
  (set (map symbol ["a" "an" "some" "has" "has-definition" "now-has" "==" "&"])))

(def ^:private no-decomment-heads
  (set (map symbol ["comment" "show-comment" "explanation"])))

(def ^:private top-only-heads
  (into #{:set :seq :bag :args :triple :pair :function}
        (map symbol)
        ["if" "forall" "allof" "oneof" "theoneof" "forall-seq" "forall-bag"
         "forall2" "allof2" "oneof2" "theoneof2" "forall-seq2" "forall-bag2"]))

(def ^:private lisp-exprs
  #{"save-kb" "reset-kb" "write-kb" "fastsave-kb" "fastload-kb" "faslsave-kb"
    "load-newest-kb" "load-triples" "orphans" "show-context" "checkkbon"
    "checkkboff" "show-bindings" "version" "dereference-kb" "show-obj-stack"
    "clear-obj-stack" "reset-done" "kb-size" "clear-evaluation-cache"
    "install-all-subclasses" "clean-taxonomy" "scan-kb" "disable-classification"
    "enable-classification" "explain-all" "clear-explanations"
    "disable-installing-inverses" "enable-installing-inverses" "start-logging"
    "stop-logging" "set-checkpoint" "start-creations-logging"
    "stop-creations-logging" "set-creations-checkpoint" "undo-creations"
    "no-explanations" "explanations" "clear-situations" "sanity-checks"
    "no-sanity-checks" "store-kb" "restore-kb" "fail-quietly" "fail-noisily"
    "requires-km-version" "catch-explanations" "show-explanations"
    "show-explanations-xml" "instance-of-is-fluent" "instance-of-is-nonfluent"
    "eval" "setq" "tracekm" "untracekm" "license" "enable-slot-checking"
    "disable-slot-checking" "comments" "nocomments" "trace-to-file-on"
    "trace-to-file-off" "t2f-on" "t2f-off" "trace" "untrace"})

(def ^:private load-save-names
  #{"load-kb" "reload-kb" "save-kb" "fastsave-kb" "fastload-kb" "faslsave-kb"
    "write-kb" "load-newest-kb"})

(def ^:private trace-names
  #{"tracekm" "TRACEKM" "trace" "TRACE" "untracekm" "UNTRACEKM" "untrace" "UNTRACE"})

(def ^:private aggregation-slots
  (set (map symbol ["min" "max" "sum" "average" "difference" "product" "quotient"
                    "first" "second" "third" "fourth" "fifth" "last"
                    "unification" "set-unification" "append" "number"])))

(def ^:private constraint-slots
  #{(symbol "==") (symbol nil "/==") (symbol "<") (symbol ">")})

(defn- intersects?
  [expr words]
  (loop [expr expr]
    (cond
      (nil? expr) false
      (not (term/cons? expr)) false
      (contains? words (term/car expr)) true
      :else (recur (term/cdr expr)))))

(defn- assertion-expr?
  [expr]
  (and (term/cons? expr)
       (or (intersects? expr assertion-words)
           (and (utils/eql? (term/car expr) (symbol "in-situation"))
                (assertion-expr? (nth-value expr 2))))))

(defn- no-decomment?
  [expr]
  (and (term/cons? expr)
       (or (contains? no-decomment-heads (term/car expr))
           (and (utils/eql? (term/car expr) (symbol "in-situation"))
                (term/cons? (nth-value expr 2))
                (contains? no-decomment-heads (term/car (nth-value expr 2)))))))

(defn- strip-comments
  "The expression km-int actually dispatches, after one comment pass."
  [expr]
  (cond
    (assertion-expr? expr) (explain/desource-decomment-top-level expr)
    (no-decomment? expr) expr
    (and (term/cons? expr) (contains? top-only-heads (term/car expr)))
    (explain/desource-decomment-top-level expr)
    :else (explain/desource-top-level (explain/decomment expr))))

(defn- note-constraints
  [state expr]
  (if (and (not (frame/are-some? (:kb state) :constraints))
           (kb/constraint-expr? expr))
    (update state :kb #(frame/set-are-some % :constraints true))
    state))

(defn- use-result
  [state result]
  (cond-> (assoc state
                 :kb (:kb result)
                 :query (or (:query result) (:query state))
                 :value (:value result))
    (some? (:message result)) (assoc :message (:message result))
    (some? (:text result)) (assoc :text (:text result))))

(defn- too-deep?
  [query]
  (let [depth (or (:depth query) 0)
        limit (:km-depth-limit query)]
    (or (> depth stack-ceiling)
        (and (some? limit) (number? limit) (> depth limit)))))

(defn- drop-nil-elements
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      (nil? (term/car values)) (recur (term/cdr values) acc)
      :else (recur (term/cdr values) (conj acc (term/car values))))))

(defn- finish
  [state commented fail-mode]
  (let [answer (kb/remove-dup-instances (drop-nil-elements (:value state)))
        state (assoc state :value answer)]
    (if (and (nil? answer) (= fail-mode :error))
      (report-error state :user-error "No values found for %s!"
                    (print/km-format commented))
      state)))

(defn- unpush
  [state]
  (let [popped (stack/pop-from-goal-stack (:kb state) (:query state))]
    (assoc state :kb (:kb popped) :query (:query popped))))

(defn- reset-top
  "The part of a top-level call that clears the query's reasoning.

  The object stack, the knowledge base, the fail mode, and a caller's
  depth limit stay. Installing inverses is left as the caller set it."
  [query]
  (assoc (or query frame/empty-query)
         :goal-stack nil
         :instances-being-unified nil
         :classification-inferences 0
         :query-directed-inferences 0
         :depth 0
         :looping? false))

(defn- exact-trace?
  [expr]
  (and (term/singleton? expr)
       (term/km-symbol? (term/car expr))
       (contains? trace-names (name (term/car expr)))))

(defn- no-values-if-error
  [state expr fail-mode name]
  (if (and (nil? (:value state))
           (= fail-mode :error)
           (not (contains? #{"setq" "km-setq"} name)))
    (report-error state :user-error "No values found for %s!" (print/km-format expr))
    state))

(defn- show-stack-command
  [state expr fail-mode shown]
  (no-values-if-error
   (assoc state
          :kb (:kb shown)
          :query (:query shown)
          :value nil
          :text (:text shown))
   expr fail-mode "show-goal-stack"))

(defn- lisp-command
  [state expr name fail-mode]
  (cond
    (= name "reset-kb")
    (let [rebuilt (frame/reset (:kb state) :query (:query state))]
      (assoc state :kb (:kb rebuilt) :query (:query rebuilt)
             :value (term/km-list (symbol "t"))))

    (contains? #{"show-obj-stack" "show-context"} name)
    (let [shown ((if (= name "show-context") stack/show-context stack/show-obj-stack)
                 (:kb state) (:query state))]
      (assoc state :kb (:kb shown) :query (:query shown)
             :value (term/km-list (symbol "t"))
             :text (:text shown)))

    (= name "clear-obj-stack")
    (let [cleared (stack/clear-obj-stack (:query state))]
      (no-values-if-error (assoc state :query (:query cleared) :value nil)
                          expr fail-mode name))

    (= name "fail-noisily")
    (assoc state
           :query (assoc (:query state) :top-level-fail-mode :error)
           :value (term/km-list (symbol "t")))

    (= name "fail-quietly")
    (assoc state
           :query (assoc (:query state) :top-level-fail-mode :fail)
           :value (term/km-list (symbol "t")))

    (contains? #{"eval" "setq" "km-setq"} name)
    (embedded-refusal state expr (str name " is not evaluated."))

    :else
    (embedded-refusal state expr nil)))

(defn- command
  "A traced form, a load or save, or an embedded-Lisp name.

  These run before a goal is pushed, so they do not count as an
  inference. Extra arguments are ignored. nil means this expression is
  not one of those commands."
  [state expr fail-mode]
  (let [name (head-name expr)]
    (cond
      (exact-trace? expr)
      (refuse-text state (str "Tracing is not ported yet: " (print/km-format expr) "."))

      (contains? load-save-names name)
      (refuse-text state
                   (if (contains? #{"fastsave-kb" "faslsave-kb"} name)
                     (str "fastsave stays unported: " (print/km-format expr) ".")
                     (str "Loading and saving a knowledge base is not ported yet: "
                          (print/km-format expr) ".")))

      (= name "show-goal-stack")
      (show-stack-command state expr fail-mode
                          (stack/show-goal-stack (:kb state) (:query state)))

      (or (contains? lisp-exprs name) (= name "km-setq"))
      (lisp-command state expr name fail-mode)

      :else nil)))

(defn- reserved-hits
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values)) nil
      (contains? kb/reserved-keywords (term/car values))
      (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- no-reserved
  "A state whose keywords were reported, or nil when the list is clean."
  [state values]
  (when-let [hits (reserved-hits values)]
    (-> (report-error state :user-error
                      "Keyword(s) %s found where concept name(s) were expected, within a list of %s KM expressions: %s (Error = missing parentheses?)"
                      (print/km-format hits)
                      (or (proper-length values) 0)
                      (print/km-format values))
        (assoc :value nil))))

(defn- fast-value
  [state expr]
  (cond
    (kb/km-set? expr) (assoc state :value (kb/set-elements expr))
    (and (term/cons? expr)
         (= :triple (term/car expr))
         (not= 3 (proper-length (term/cdr expr))))
    (-> (report-error state :user-error
                      "%s: A triple should have exactly three elements!"
                      (print/km-format expr))
        (assoc :value (term/km-list expr)))
    (and (term/cons? expr)
         (= :pair (term/car expr))
         (not= 2 (proper-length (term/cdr expr))))
    (-> (report-error state :user-error
                      "%s: A pair should have exactly two elements!"
                      (print/km-format expr))
        (assoc :value (term/km-list expr)))
    :else (assoc state :value (term/km-list expr))))

(defn- early
  "A result that is known before the handler table, or nil to continue."
  [state commented cleaned fail-mode check-for-looping]
  (let [kb (:kb state)
        query (:query state)]
    (cond
      (kb/km-null? cleaned)
      (cond-> (assoc state :value nil)
        (= fail-mode :error)
        (report-error :user-error "No values found for %s!" (print/km-format cleaned)))

      (and (kb/constraint-expr? cleaned) (not (kb/retain-expr? cleaned)))
      (cond-> (assoc state :value nil)
        (= fail-mode :error)
        (report-error :user-error "No values found for %s!" (print/km-format cleaned)))

      (and (utils/lisp-atom? cleaned)
           (no-reserved state (term/km-list cleaned)))
      (no-reserved state (term/km-list cleaned))

      (kb/km-var? cleaned)
      (-> (report-error state :user-error "Unbound variable %s encountered!"
                        (print/km-format cleaned))
          (assoc :value nil))

      (and (kb/fully-evaluated? commented)
           (utils/eql? (frame/dereference kb cleaned) cleaned))
      (fast-value state cleaned)

      (explain/internal-comment? commented)
      (-> (report-error state :user-error
                        "Comment tag %s was encountered as a free-standing slot-value in the KB - not allowed! It should be embedded within a KM expression."
                        (print/km-format (nth-value commented 1)))
          (assoc :value nil))

      (and check-for-looping (stack/looping-on? kb query commented))
      (use-result state (stack/handle-looping kb query cleaned))

      (too-deep? query)
      (use-result state (stack/handle-looping kb query cleaned
                                              :reason :depth-limit-reached))

      :else nil)))

;;; ----------------------------------------------------------------------
;;; Handlers. Each one is [state pieces] and returns a state.

(defn- note-constraint
  [state _]
  (-> state
      (update :kb #(frame/set-are-some % :constraints true))
      (assoc :value nil)))

(defn- every-simple?
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (kb/is-simple-km-term? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- map-list
  [values f]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      :else (recur (term/cdr values) (conj acc (f (term/car values)))))))

(defn- keep-terms
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      (kb/is-km-term? (term/car values))
      (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- ordered-difference
  [values blocked]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      (utils/member? (term/car values) blocked utils/equal?)
      (recur (term/cdr values) acc)
      :else (recur (term/cdr values) (conj acc (term/car values))))))

(defn- structured-slot?
  [slot]
  (and (term/cons? slot) (utils/eql? (nth-value slot 1) (symbol "*"))))

(defn- follow0
  [state values slot depth start so-far]
  (cond
    (refused? state) state
    (or (<= depth 0) (nil? values)) (assoc state :value so-far)
    :else
    (let [probe (km-int state
                        (term/km-list (symbol "the") slot (symbol "of")
                                      (kb/vals-to-val values))
                        :fail-mode :fail)]
      (if (refused? probe)
        probe
        (let [novel (ordered-difference (:value probe)
                                        (utils/append-lists (term/km-list start so-far)))]
          (follow0 probe novel slot (dec depth) values
                   (utils/append-lists (term/km-list so-far novel))))))))

(defn- multidepth
  [state values slot-structure]
  (let [slot (term/car slot-structure)
        depth (or (nth-value slot-structure 2) 5)]
    (cond
      (nil? values) (assoc state :value nil)
      (not (integer? depth))
      (-> (report-error state :user-error
                        "Non-integer depth %s given for slot-structure %s in quoted path!"
                        (print/km-format depth)
                        (print/km-format slot-structure))
          (assoc :value nil))
      (< depth 1)
      (-> (report-error state :user-error
                        "Depth %s given for slot-structure %s in quoted path must be >= 1!"
                        (print/km-format depth)
                        (print/km-format slot-structure))
          (assoc :value nil))
      :else (follow0 state values slot depth values nil))))

(defn- the-handler
  [state pieces]
  (let [[slot frameadd] pieces
        fail0 (:fail-mode state)]
    (cond
      (structured-slot? slot)
      (let [start (km-int state frameadd :fail-mode fail0)]
        (if (refused? start)
          start
          (multidepth start (:value start) slot)))

      (kb/path? slot)
      (let [evaluated (km-unique-int state slot :fail-mode :error)]
        (if (refused? evaluated)
          evaluated
          (let [retry (km-int evaluated
                              (term/km-list (symbol "the") (:value evaluated)
                                            (symbol "of") frameadd)
                              :fail-mode fail0)]
            (if (refused? retry) retry (update retry :value keep-terms)))))

      :else
      (let [mode (if (contains? aggregation-slots slot) :fail fail0)
            simple (kb/val-to-vals frameadd)
            frames-state (if (every-simple? simple)
                           (assoc state :value
                                  (kb/remove-dup-instances
                                   (map-list simple #(frame/dereference (:kb state) %))))
                           (km-int state frameadd
                                   :fail-mode mode
                                   :check-for-looping false))]
        (if (refused? frames-state)
          frames-state
          (let [frames (:value frames-state)
                answer (if (utils/equal? frames simple)
                         (slotvals/multi-slotvals frames-state frames slot km-int
                                                  :fail-mode mode)
                         (km-int frames-state
                                 (term/km-list (symbol "the") slot (symbol "of")
                                               (kb/vals-to-val frames))
                                 :fail-mode mode))]
            (if (refused? answer) answer (update answer :value keep-terms))))))))

(defn- slotsvals-ok?
  "True when every pair is (slot (values)). Flags are set as the pairs pass.

  The first bad pair stops the walk. Flags from earlier pairs stay."
  [state slotsvals]
  (if-not (utils/lisp-list? slotsvals)
    [(-> (report-error state :user-error
                       "Bad structure %s for list of slot-values! Should be of form (s1 (v1 ... vn)) (s2 (...)) ...)"
                       (print/km-format slotsvals))
         (assoc :value nil))
     false]
    (loop [pairs slotsvals
           state state]
      (cond
        (nil? pairs) [state true]
        (not (term/cons? pairs))
        [(-> (report-error state :user-error "This list is dotted.")
             (assoc :value nil))
         false]
        :else
        (let [pair (term/car pairs)
              slot (when (term/cons? pair) (term/car pair))
              values (nth-value pair 1)
              bad (cond
                    (not (term/pair? pair))
                    (report-error state :user-error
                                  "Bad structure %s for slot+values! Slot+values should be of the form (slot (v1 ... vn))"
                                  (print/km-format pair))
                    (not (term/lisp-symbol? slot))
                    (report-error state :user-error
                                  "Bad structure %s for slot+values! Slot `%s' should be a symbol!"
                                  (print/km-format pair) (print/km-format slot))
                    (not (utils/lisp-list? values))
                    (report-error state :user-error
                                  "Bad structure %s for slot+values! Values %s for slot %s should be a list!"
                                  (print/km-format pair) (print/km-format values) (print/km-format slot))
                    (contains? kb/reserved-keywords slot)
                    (report-error state :user-error
                                  "Bad structure %s for slot+values! The slot `%s' is a reserved KM keyword, and cannot be used as a slot name!"
                                  (print/km-format pair) (print/km-format slot))
                    :else (no-reserved state values))]
          (if (some? bad)
            [(assoc bad :value nil) false]
            (let [state (cond-> state
                          (or (loop [values values
                                     found false]
                                (cond
                                  found true
                                  (nil? values) false
                                  (not (term/cons? values)) false
                                  (and (term/cons? (term/car values))
                                       (kb/constraint-expr? (term/car values))) true
                                  :else (recur (term/cdr values) false)))
                              (contains? constraint-slots slot))
                          (update :kb #(frame/set-are-some % :constraints true))
                          (loop [values values]
                            (cond
                              (nil? values) false
                              (not (term/cons? values)) false
                              (kb/km-default? (term/car values)) true
                              :else (recur (term/cdr values))))
                          (update :kb #(frame/set-are-some % :defaults true))
                          (utils/eql? slot (symbol "called"))
                          (update :kb #(frame/set-are-some % :tags true))
                          (utils/eql? slot (symbol "uniquely-called"))
                          (-> (update :kb #(frame/set-are-some % :tags true))
                              (update :kb #(frame/set-are-some % :constraints true)))
                          (or (utils/eql? slot (symbol "subslots"))
                              (utils/eql? slot (symbol "superslots")))
                          (update :kb #(frame/set-are-some % :subslots true))
                          (utils/eql? slot (symbol "prototype-of"))
                          (update :kb #(frame/set-are-some % :prototypes true)))]
              (recur (term/cdr pairs) state))))))))

(defn- has-handler
  [state pieces]
  (let [[instance-expr slotsvals] pieces
        unique (km-unique-int state instance-expr :fail-mode :error)
        instance (:value unique)]
    (cond
      (refused? unique) unique
      (not (kb/kb-object? instance))
      (-> (report-error unique :user-error
                        "%s%n%s isn't/doesn't evaluate to a KB object name."
                        (print/km-format (term/build-list [instance-expr (symbol "has")] slotsvals))
                        (print/km-format instance-expr))
          (assoc :value nil))
      :else
      (let [[checked ok?] (slotsvals-ok? unique slotsvals)]
        (if-not ok?
          checked
          (try
            (let [stored (frame/add-slotsvals (:kb checked) instance
                                              (explain/convert-comments slotsvals)
                                              :query (:query checked))]
              (assoc checked :kb (:kb stored) :query (:query stored)
                     :value (term/km-list instance)))
            (catch clojure.lang.ExceptionInfo thrown
              (-> (report-error checked :user-error "%s" (.getMessage thrown))
                  (assoc :value nil)))))))))

(defn- assert-handler
  [state pieces]
  (let [expr (first pieces)
        unique (km-unique-int state expr)
        triple (:value unique)]
    (cond
      (refused? unique) unique
      (not (kb/km-triple? triple))
      (-> (report-error unique :user-error
                        "(assert %s): %s should evaluate to a triple! (evaluated to %s instead)!"
                        (print/km-format expr)
                        (print/km-format expr)
                        (print/km-format triple))
          (assoc :value nil))
      :else
      (km-int unique
              (term/km-list (kb/arg1 triple)
                            (symbol "has")
                            (term/km-list (kb/arg2 triple)
                                          (kb/val-to-vals (kb/arg3 triple))))
              :fail-mode :error))))

(defn- delete-one
  "Remove one frame. A missing frame is recorded and the rest continue."
  [current value]
  (try
    (let [gone (frame/delete-frame (:kb current) value :query (:query current))]
      [(assoc current :kb (:kb gone) :query (:query gone)) false])
    (catch clojure.lang.ExceptionInfo thrown
      [(-> (report-error current :user-error "%s" (.getMessage thrown))
           (assoc :value nil))
       true])))

(defn- delete-handler
  [state pieces]
  (let [expr (first pieces)
        found (km-int state expr
                      :fail-mode (:fail-mode state)
                      :target (:target state)
                      :rewrite? true)]
    (if (refused? found)
      found
      (loop [values (:value found)
             current found
             failed? false]
        (cond
          (nil? values)
          (assoc current :value (when-not failed? (term/km-list (symbol "t"))))
          (not (term/cons? values))
          (throw (ex-info "This list is dotted." {:tail values}))
          :else
          (let [[next failed-one?] (delete-one current (term/car values))]
            (recur (term/cdr values) next (or failed? failed-one?))))))))

(defn- set-equal-handler
  [negate?]
  (fn [state pieces]
    (let [[x y] pieces
          mode (:fail-mode state)
          xs (km-int state x :fail-mode mode)]
      (if (refused? xs)
        xs
        (let [ys (km-int xs y :fail-mode mode)]
          (if (refused? ys)
            ys
            (let [same? (kb/km-set-equal?
                         (frame/dereference (:kb ys) (:value xs))
                         (:value ys))]
              (assoc ys :value (when (if negate? (not same?) same?)
                                 (term/km-list (symbol "t")))))))))))

(defn- compare-numbers
  [op x y]
  (and (number? x) (number? y)
       (if (or (float? x) (float? y))
         (op (double x) (double y))
         (op x y))))

(defn- km-abs
  [n]
  (if (neg? n) (-' n) n))

(defn- compare-handler
  [op]
  (fn [state pieces]
    (let [[x y] pieces
          xs (km-unique-int state x :fail-mode :error)]
      (if (refused? xs)
        xs
        (let [ys (km-unique-int xs y :fail-mode :error)]
          (if (refused? ys)
            ys
            (assoc ys :value (when (compare-numbers op (:value xs) (:value ys))
                               (term/km-list (symbol "t"))))))))))

(defn- three-numbers
  [state pieces]
  (let [[x y z] pieces
        xs (km-unique-int state x :fail-mode :error)]
    (if (refused? xs)
      [xs nil]
      (let [ys (km-unique-int xs y :fail-mode :error)]
        (if (refused? ys)
          [ys nil]
          (let [zs (km-unique-int ys z :fail-mode :error)]
            [zs (when (and (number? (:value xs))
                           (number? (:value ys))
                           (number? (:value zs)))
                  [(:value xs) (:value ys) (:value zs)])]))))))

(defn- approx-handler
  [state pieces]
  (let [[current numbers] (three-numbers state pieces)]
    (if (or (refused? current) (nil? numbers))
      (if (refused? current) current (assoc current :value nil))
      (let [[x y z] numbers]
        (assoc current :value
               (when (<= (km-abs (-' x y)) (km-abs z))
                 (term/km-list (symbol "t"))))))))

(defn- percent-handler
  [state pieces]
  (let [[current numbers] (three-numbers state pieces)]
    (if (or (refused? current) (nil? numbers))
      (if (refused? current) current (assoc current :value nil))
      (let [[x y z] numbers
            xd (double x)
            yd (double y)
            limit (* (max (Math/abs xd) (Math/abs yd)) (Math/abs (double z)) 0.01)]
        (assoc current :value
               (when (<= (Math/abs (- xd yd)) limit)
                 (term/km-list (symbol "t"))))))))

(defn- and-handler
  [state pieces]
  (let [[x rest] pieces]
    (if (and (term/triple? x) (utils/eql? (nth-value x 1) (symbol "==")))
      (refuse state pieces)
      (let [left (km-int state x)]
        (cond
          (refused? left) left
          (nil? (:value left)) left
          :else (km-int left rest))))))

(defn- or-handler
  [state pieces]
  (let [[x y] pieces]
    (if (stack/on-goal-stack? (:kb state) (:query state) x)
      (km-int state y)
      (let [left (km-int state x)]
        (cond
          (refused? left) left
          (some? (:value left)) left
          :else (km-int left y))))))

(defn- not-handler
  [state pieces]
  (let [found (km-int state (first pieces))]
    (cond
      (refused? found) found
      (nil? (:value found)) (assoc found :value (term/km-list (symbol "t")))
      :else (assoc found :value nil))))

(defn- numberp-handler
  [state pieces]
  (let [found (km-unique-int state (first pieces))]
    (cond
      (refused? found) found
      (number? (:value found)) (assoc found :value (term/km-list (symbol "t")))
      :else (assoc found :value nil))))

(defn- rewrite-handler
  [op next-op]
  (fn [state pieces]
    (let [[x y rest] pieces]
      (km-int state
              (term/build-list [(term/km-list x op y) next-op] rest)
              :fail-mode (:fail-mode state)))))

(defn- divide
  [x y]
  (cond
    (and (zero? x) (zero? y)) 1
    (zero? x) 0
    (zero? y) infinity
    (or (float? x) (float? y)) (/ (double x) (double y))
    :else (/ x y)))

(defn- km-expt
  "An exact power for an integer exponent. Any other power is a double.

  A float exponent, or a float base, uses Math/pow. 0^0 is 1."
  [x y]
  (cond
    (and (integer? y) (not (float? x)) (not (neg? y)))
    (loop [n y
           acc 1]
      (if (zero? n) acc (recur (dec' n) (*' acc x))))
    (and (integer? y) (not (float? x)))
    (/ 1 (km-expt x (-' y)))
    :else (Math/pow (double x) (double y))))

(defn- numeric-handler
  [op]
  (fn [state pieces]
    (let [[left right] pieces
          mode (:fail-mode state)
          target (:target state)
          xs (km-unique-int state left :fail-mode mode :target target :rewrite? true)]
      (if (refused? xs)
        xs
        (let [ys (km-unique-int xs right :fail-mode mode :target target :rewrite? true)]
          (if (refused? ys)
            ys
            (if (and (number? (:value xs)) (number? (:value ys)))
              (assoc ys :value (term/km-list (op (:value xs) (:value ys))))
              (assoc ys :value nil))))))))

(defn- splice
  [state exprs]
  (loop [exprs exprs
         current state
         acc []]
    (cond
      (refused? current) current
      (nil? exprs) (assoc current :value (term/build-list acc nil))
      (not (term/cons? exprs))
      (throw (ex-info "This list is dotted." {:tail exprs}))
      :else
      (let [next (km-int current (term/car exprs))]
        (if (refused? next)
          next
          (recur (term/cdr exprs)
                 next
                 (into acc (utils/elements (:value next)))))))))

(defn- map-one
  [state exprs]
  (loop [exprs exprs
         current state
         acc []]
    (cond
      (refused? current) current
      (nil? exprs) (assoc current :value (term/build-list acc nil))
      (not (term/cons? exprs))
      (throw (ex-info "This list is dotted." {:tail exprs}))
      :else
      (let [next (km-int current (term/car exprs))]
        (if (refused? next)
          next
          (recur (term/cdr exprs)
                 next
                 (conj acc (kb/vals-to-val (:value next)))))))))

(defn- wrap-handler
  [head]
  (fn [state pieces]
    (let [exprs (first pieces)]
      (if (nil? exprs)
        (assoc state :value nil)
        (let [built (map-one state exprs)]
          (if (refused? built)
            built
            (assoc built :value (term/km-list (term/cons-cell head (:value built))))))))))

(defn- pair-handler
  [state pieces]
  (let [exprs (first pieces)]
    (if-not (term/pair? exprs)
      (-> (report-error state :user-error
                        "%s: A pair should have exactly two elements!"
                        (print/km-format (term/cons-cell :pair exprs)))
          (assoc :value nil))
      (let [built (map-one state exprs)]
        (if (or (refused? built) (nil? (:value built)))
          built
          (assoc built :value (term/km-list (term/cons-cell :pair (:value built)))))))))

(defn- triple-handler
  [state pieces]
  (let [[frame-expr slot-expr val-expr] pieces
        slot-state (if (kb/comparison-operator? slot-expr)
                     (assoc state :value slot-expr)
                     (km-unique-int state slot-expr :fail-mode :error))
        slot (:value slot-state)]
    (if (refused? slot-state)
      slot-state
      (let [frame-state (if (and (kb/comparison-operator? slot)
                                 (match/minimatch frame-expr
                                                  (pat ["the" "?x" "of" "?y"])))
                          (assoc slot-state :value frame-expr)
                          (km-unique-int slot-state frame-expr :fail-mode :error))
            frame (:value frame-state)
            val0 (explain/desource-decomment val-expr)]
        (if (refused? frame-state)
          frame-state
          (let [val-state (if (or (kb/constraint-expr? val0)
                                  (kb/existential? val0)
                                  (kb/comparison-operator? slot))
                            (assoc frame-state :value val0)
                            (let [evaluated (km-int frame-state val-expr)]
                              (if (refused? evaluated)
                                evaluated
                                (assoc evaluated :value (kb/vals-to-val (:value evaluated))))))]
            (if (refused? val-state)
              val-state
              (assoc val-state :value
                     (term/km-list (term/km-list :triple frame slot (:value val-state)))))))))))

(defn- process-unquotes
  [state expr]
  (cond
    (refused? state) state
    (nil? expr) (assoc state :value nil)
    (not (term/cons? expr)) (assoc state :value expr)
    (utils/eql? (term/car expr) (symbol "unquote"))
    (if-not (term/pair? expr)
      (-> (report-error state :user-error "Unquoted structure %s should be a pair!"
                        (print/km-format expr))
          (assoc :value nil))
      (let [inner (km-int state (nth-value expr 1) :fail-mode :fail)]
        (if (refused? inner)
          inner
          (assoc inner :value (kb/vals-to-val (:value inner))))))
    :else
    (let [head (process-unquotes state (term/car expr))]
      (if (refused? head)
        head
        (let [tail (process-unquotes head (term/cdr expr))]
          (if (refused? tail)
            tail
            (assoc tail :value (term/cons-cell (:value head) (:value tail)))))))))

(defn- quote-handler
  [state pieces]
  (let [processed (process-unquotes state (first pieces))]
    (if (refused? processed)
      processed
      (if (nil? (:value processed))
        (assoc processed :value nil)
        (assoc processed :value
               (term/km-list (term/km-list (symbol "quote") (:value processed))))))))

(defn- unquote-handler
  [state pieces]
  (-> (report-error state :user-error
                    "Doing #,%s: You can't unquote something without it first being quoted!"
                    (print/km-format (first pieces)))
      (assoc :value nil)))

(defn- default-handler
  [state _]
  (-> state
      (update :kb #(frame/set-are-some % :defaults true))
      (assoc :value nil)))

(defn- sanity-handler
  [state _]
  (assoc state :value (term/km-list (symbol "t"))))

(defn- new-context-handler
  [state _]
  (let [cleared (stack/clear-obj-stack (:query state))]
    (assoc state :query (:query cleared) :value (term/km-list (symbol "t")))))

(defn- function-handler
  [state _]
  (embedded-refusal state (:current-expr state) "function is not evaluated."))

(defn- path-handler
  [state pieces]
  (let [path (first pieces)]
    (cond
      (utils/lisp-atom? path)
      (or (no-reserved state (term/km-list path))
          (assoc state :value (term/km-list path)))
      (not (utils/lisp-list? path))
      (-> (report-error state :program-error "Failed to find km handler for %s!"
                        (print/km-format path))
          (assoc :value nil))
      (term/singleton? path)
      (km-int state (term/car path) :fail-mode (:fail-mode state))
      :else
      (-> (report-error state :user-error
                        "KM Syntax error: %s is not a valid KM expression"
                        (print/km-format path))
          (assoc :value nil)))))

(defn- entry
  [pattern handler]
  [(pat pattern) handler])

(defn- later
  [pattern]
  (entry pattern refuse))

(def ^:private op-symbol
  {"+" (symbol "+") "-" (symbol "-") "*" (symbol "*")
   "/" (symbol "/") "^" (symbol "^")})

(defn- rewrite
  [op next-op]
  (entry ["?x" op "?y" next-op "&rest"]
         (rewrite-handler (op-symbol op) (op-symbol next-op))))

(def ^:private handlers
  (into
   [(entry ["the" "?slot" "of" "?frameadd"] the-handler)
    (later ["a" "?class"])
    (later ["a" "?class" "called" "?tag"])
    (later ["a" "?class" "uniquely-called" "?tag"])
    (later ["a" "?class" "with" "&rest"])
    (later ["a" "?class" "uniquely-called" "?tag" "with" "&rest"])
    (later ["a" "?class" "called" "?tag" "with" "&rest"])
    (later ["a-prototype" "?class"])
    (later ["a-prototype" "?class" "with" "&rest"])
    (later ["end-prototype"])
    (later ["clone" "?expr"])
    (later ["evaluate-paths"])
    (later ["default-fluent-status" "&rest"])
    (entry ["must-be-a" "?class"] note-constraint)
    (entry ["possible-values" "?values"] note-constraint)
    (entry ["excluded-values" "?values"] note-constraint)
    (entry ["must-be-a" "?class" "with" "&rest"] note-constraint)
    (entry ["mustnt-be-a" "?class"] note-constraint)
    (entry ["mustnt-be-a" "?class" "with" "&rest"] note-constraint)
    (entry ["<>" "?val"] note-constraint)
    (entry ["no-inheritance"] note-constraint)
    (entry ["constraint" "?expr"] note-constraint)
    (entry ["set-constraint" "?expr"] note-constraint)
    (entry ["set-filter" "?expr"] note-constraint)
    (entry ["at-least" "?n" "?class"] note-constraint)
    (entry ["at-most" "?n" "?class"] note-constraint)
    (entry ["exactly" "?n" "?class"] note-constraint)
    (entry ["sanity-check" "?expr"] sanity-handler)
    (later ["retain-expr" "?expr"])
    (later ["every" "?cexpr" "has" "&rest"])
    (later ["every" "?cexpr" "also-has" "&rest"])
    (later ["every" "?cexpr" "now-has" "&rest"])
    (entry ["?instance-expr" "has" "&rest"] has-handler)
    (later ["?instance-expr" "also-has" "&rest"])
    (later ["every" "?instance-expr" "also-hasnt" "&rest"])
    (later ["?instance-expr" "also-hasnt" "&rest"])
    (later ["?instance-expr" "now-has" "&rest"])
    (later ["?xs" "&&" "&rest"])
    (later ["?x" "&" "&rest"])
    (later ["?xs" "===" "&rest"])
    (later ["?x" "==" "?y"])
    (entry ["?x" (symbol nil "/==") "?y"] refuse)
    (later ["?xs" "&&!" "&rest"])
    (later ["?x" "&!" "&rest"])
    (later ["?x" "&?" "?y"])
    (later ["?x" "&+?" "?y"])
    (later ["?x" "&+" "?y"])
    (later ["?x" "&+!" "?y"])
    (entry ["?x" "=" "?y"] (set-equal-handler false))
    (entry ["?x" "/=" "?y"] (set-equal-handler true))
    (later ["the" "?class" "?slot" "of" "?frameadd"])
    (later ["in-theory" "?theory-expr"])
    (later ["in-theory" "?theory-expr" "?km-expr"])
    (later ["hide-theory" "?theory-expr"])
    (later ["see-theory" "?theory-expr"])
    (later ["end-theory"])
    (later ["visible-theories"])
    (later ["in-situation" "?situation-expr"])
    (later ["in-situation" "?situation" ["the" "?slot" "of" "?frame"]])
    (later ["in-situation" "?situation-expr" "?km-expr"])
    (later ["end-situation"])
    (later ["global-situation"])
    (later ["new-situation"])
    (later ["do" "?action-expr"])
    (later ["do" "?action-expr" "?next-situation"])
    (later ["do-and-next" "?action-expr"])
    (later ["do-and-next" "?action-expr" "?next-situation"])
    (later ["try-do" "?action-expr"])
    (later ["try-do" "?action-expr" "?next-situation"])
    (later ["try-do-and-next" "?action-expr"])
    (later ["try-do-and-next" "?action-expr" "?next-situation"])
    (later ["do-concurrently" "?action-expr"])
    (later ["do-concurrently" "?action-expr" "?next-situation"])
    (later ["do-concurrently-and-next" "?action-expr"])
    (later ["do-concurrently-and-next" "?action-expr" "?next-situation"])
    (later ["do-script" "?script"])
    (later ["do-plan" "?plan-instance-expr"])
    (entry ["assert" "?triple-expr"] assert-handler)
    (later ["is-true" "?triple-expr"])
    (later ["all-true" "?triples-expr"])
    (later ["some-true" "?triples-expr"])
    (later ["next-situation"])
    (later ["curr-situation"])
    (later ["ignore-result" "?expr"])
    (later ["ignore" "?expr"])
    (later ["in-every-situation" "?situation-class" "?expr"])
    (entry ["new-context"] new-context-handler)
    (later ["thelast" "?frame"])
    (later ["every" "?frame"])
    (later ["every" "?frame" "with" "&rest"])
    (later ["the" "?frame"])
    (later ["the" "?frame" "with" "&rest"])
    (later ["the+" "?slot" "of" "?frameadd"])
    (later ["the+" "?class" "?slot" "of" "?frameadd"])
    (later ["the+" "?frame"])
    (later ["the+" "?frame" "with" "&rest"])
    (later ["a+" "&rest"])
    (later ["every" "?cexpr" "has-definition" "&rest"])
    (later ["every" "?cexpr" "now-has-definition" "&rest"])
    (later ["?instance-expr" "has-definition" "&rest"])
    (later ["?instance-expr" "now-has-definition" "&rest"])
    (later ["if" "?condition" "then" "?action"])
    (later ["if" "?condition" "then" "?action" "else" "?altaction"])
    (entry ["?x" ">" "?y"] (compare-handler >))
    (entry ["?x" "<" "?y"] (compare-handler <))
    (entry ["?x" ">=" "?y"] (compare-handler >=))
    (entry ["?x" "<=" "?y"] (compare-handler <=))
    (entry ["?x" "=" "?y" "+/-" "?z"] approx-handler)
    (entry ["?x" "=" "?y" "+/-" "?z" "%"] percent-handler)
    (entry ["?x" "and" "&rest"] and-handler)
    (entry ["?x" "or" "&rest"] or-handler)
    (entry ["not" "?x"] not-handler)
    (entry ["numberp" "?x"] numberp-handler)
    (later ["?x" "is-subsumed-by" "?y"])
    (later ["?x" "subsumes" "?y"])
    (later ["?x" "is-covered-by" "?y"])
    (later ["?x" "covers" "?y"])
    (later ["?y" "isa" "?x"])
    (later ["?x" "is" "?y"])
    (later ["?xs" "includes" "?y"])
    (later ["?xs" "is-superset-of" "?ys"])
    (later ["?seq-expr1" "append" "?seq-expr2"])
    (later ["?expr" "called" "?tag"])
    (later ["?expr" "uniquely-called" "?tag"])
    (later ["allof" "?set" "where" "?test"])
    (later ["allof" "?set" "must" "?test"])
    (later ["allof" "?set" "where" "?test2" "must" "?test"])
    (later ["oneof" "?set" "where" "?test"])
    (later ["theoneof" "?set" "where" "?test"])
    (later ["forall" "?set" "?value"])
    (later ["forall-seq" "?seq" "?value"])
    (later ["forall-bag" "?bag" "?value"])
    (later ["forall" "?set" "where" "?constraint" "?value"])
    (later ["forall-seq" "?seq" "where" "?constraint" "?value"])
    (later ["forall-seq2" "?seq" "where" "?constraint" "?value"])
    (later ["forall-bag" "?bag" "where" "?constraint" "?value"])
    (later ["forall-bag2" "?bag" "where" "?constraint" "?value"])
    (later ["allof2" "?set" "where" "?test"])
    (later ["allof2" "?set" "must" "?test"])
    (later ["allof2" "?set" "where" "?test2" "must" "?test"])
    (later ["oneof2" "?set" "where" "?test"])
    (later ["forall2" "?set" "?value"])
    (later ["forall-seq2" "?seq" "?value"])
    (later ["forall-bag2" "?bag" "?value"])
    (later ["theoneof2" "?set" "where" "?test"])
    (later ["forall2" "?set" "where" "?constraint" "?value"])
    (later ["allof" "?var" "in" "?set" "where" "?test"])
    (later ["allof" "?var" "in" "?set" "must" "?test"])
    (later ["allof" "?var" "in" "?set" "where" "?test2" "must" "?test"])
    (later ["oneof" "?var" "in" "?set" "where" "?test"])
    (later ["theoneof" "?var" "in" "?set" "where" "?test"])
    (later ["forall" "?var" "in" "?set" "?value"])
    (later ["forall-seq" "?var" "in" "?seq" "?value"])
    (later ["forall-bag" "?var" "in" "?bag" "?value"])
    (later ["forall" "?var" "in" "?set" "where" "?constraint" "?value"])
    (later ["forall-bag" "?var" "in" "?bag" "where" "?constraint" "?value"])
    (later ["forall-seq" "?var" "in" "?seq" "where" "?constraint" "?value"])
    (entry ["function" "?lispcode"] function-handler)
    (later ["the1" "?slot" "of" "?frameadd"])
    (later ["the2" "?slot" "of" "?frameadd"])
    (later ["the3" "?slot" "of" "?frameadd"])
    (later ["the1" "of" "?frameadd"])
    (later ["the2" "of" "?frameadd"])
    (later ["the3" "of" "?frameadd"])
    (later ["theN" "?nexpr" "of" "?frameadd"])
    (later ["theNth" "?nexpr" "of" "?frameadd"])
    (rewrite "^" "^")
    (rewrite "^" "+")
    (rewrite "^" "-")
    (rewrite "^" "/")
    (rewrite "^" "*")
    (rewrite "/" "+")
    (rewrite "/" "-")
    (rewrite "/" "/")
    (rewrite "/" "*")
    (rewrite "*" "+")
    (rewrite "*" "-")
    (rewrite "*" "/")
    (rewrite "-" "-")
    (rewrite "-" "+")
    (rewrite "+" "-")
    (entry ["?expr" "+" "&rest"] (numeric-handler +'))
    (entry ["?expr" "-" "&rest"] (numeric-handler -'))
    (entry ["?expr" "*" "&rest"] (numeric-handler *'))
    (entry ["?expr" "/" "&rest"] (numeric-handler divide))
    (entry ["?expr1" "^" "?expr2"] (numeric-handler km-expt))
    [(symbol "nil") (fn [state _] (assoc state :value nil))]
    [nil (fn [state _] (assoc state :value nil))]
    (entry [:set "&rest"] (fn [state pieces] (splice state (first pieces))))
    (entry [:seq "&rest"] (wrap-handler :seq))
    (entry [:bag "&rest"] (wrap-handler :bag))
    (entry [:function "&rest"] (wrap-handler :function))
    (entry [:pair "&rest"] pair-handler)
    (entry [:triple "?frame-expr" "?slot-expr" "?val-expr"] triple-handler)
    (entry [:args "&rest"] (wrap-handler :args))
    (later ["showme" "?km-expr"])
    (later ["showme" "?km-expr" "?file"])
    (later ["showme-all" "?km-expr"])
    (later ["evaluate-all" "?km-expr"])
    (later ["showme-here" "?km-expr"])
    (later ["the-class" "?class"])
    (later ["the-class" "?class" "with" "&rest"])
    (later ["constraints-for" ["the" "?slot" "of" "?frameadd"]])
    (later ["rules-for" ["the" "?slot" "of" "?frameadd"]])
    (later ["why"])
    (later ["why" "?triple"])
    (later ["justify"])
    (later ["justify" "?triple"])
    (later ["get-justification"])
    (later ["get-justification" "?triple"])
    (later ["explanation" [:triple "?f0" "?s" "?v0"] "?explanations"])
    (later ["explained-by" "?instance" "?expr"])
    (later ["comment" "?comment-tag" "&rest"])
    (later ["show-comment" "?comment-tag"])
    (entry ["quote" "?expr"] quote-handler)
    (entry ["unquote" "?expr"] unquote-handler)
    (entry ["delete" "?km-expr"] delete-handler)
    (later ["evaluate" "?expr"])
    (later ["exists" "?frame"])
    (later ["has-value" "?frame"])
    (later ["print" "?expr"])
    (later ["format" "?flag" "?string" "&rest"])
    (later ["km-format" "?flag" "?string" "&rest"])
    (later ["andify" "?expr"])
    (later ["make-sentence" "?expr"])
    (later ["make-phrase" "?expr"])
    (later ["pluralize" "?expr"])
    (later ["spy" "?expr"])
    (later ["spy"])
    (later ["unspy"])
    (later ["profile" "?expr"])
    (later ["profile-report"])
    (later ["profile-report" "?n"])
    (later ["taxonomy" "&rest"])
    (later ["checkpoint"])
    (later ["checkpoint" "?checkpoint-id"])
    (later ["undo"])
    (later ["an" "instance" "of" "?expr"])
    (later ["an" "instance" "of" "?expr" "with" "&rest"])
    (later ["reverse" "?seq-expr"])
    (entry [:default "?expr"] default-handler)
    (entry ["sometimes" "?expr"] note-constraint)
    (later ["anonymous-instancep" "?expr"])]
   [[(symbol "?path") path-handler]]))

(defn- dispatch
  [state expr]
  (if-let [found (match/find-handler expr handlers)]
    (let [pieces (if (nil? (:bindings found)) [] (utils/elements (:bindings found)))]
      ((:handler found) state pieces))
    (-> (report-error state :program-error "Failed to find km handler for %s!"
                      (print/km-format expr))
        (assoc :value nil))))

(defn- km1
  [state expr commented fail-mode target]
  (let [state (-> state
                  (update-in [:query :depth] (fnil inc 0))
                  (update-in [:query :query-directed-inferences] (fnil inc 0))
                  (assoc :fail-mode fail-mode :target target :current-expr commented))
        dispatched (if (utils/lisp-atom? expr)
                     (assoc state :value (term/km-list expr))
                     (dispatch state expr))
        finished (if (refused? dispatched)
                   dispatched
                   (finish dispatched commented fail-mode))]
    (update-in finished [:query :depth] (fnil dec 0))))

(defn km-int
  "Evaluate one expression inside a query that is already running.

  fail-mode defaults to :fail when the caller does not pass one. That
  is the reasoning default, including when the top-level mode is :error.
  A refusal is returned unchanged. The goal is popped either way."
  [state expr & {:keys [fail-mode target check-for-looping rewrite?]
                 :or {check-for-looping true}}]
  (let [fail-mode (or fail-mode :fail)
        _ rewrite?
        commented expr
        cleaned (strip-comments expr)
        state (-> state
                  (assoc :current-expr commented :fail-mode fail-mode :target target)
                  (note-constraints cleaned))]
    (or (command state cleaned fail-mode)
        (early state commented cleaned fail-mode check-for-looping)
        (let [pushed (stack/push-to-goal-stack (:kb state) (:query state) commented
                                               :target target)
              state (assoc state :kb (:kb pushed) :query (:query pushed))]
          (try
            (unpush (km1 state cleaned commented fail-mode target))
            (catch Throwable thrown
              (unpush state)
              (throw thrown)))))))

(defn km-unique-int
  "The one value of an expression.

  :value is that element, not a list. Several values record an error
  and keep the first. No value in :error mode records an error. No
  value in :fail mode is nil."
  [state expr & {:keys [fail-mode target rewrite?] :or {fail-mode :fail}}]
  (let [_ rewrite?
        found (km-int state expr :fail-mode fail-mode :target target :rewrite? rewrite?)]
    (cond
      (refused? found) found
      (term/singleton? (:value found)) (assoc found :value (term/car (:value found)))
      (some? (:value found))
      (-> (report-error found :user-error
                        "Expression %s was expected to return a single value,%nbut it returned multiple values %s!%nJust taking the first...(%s) "
                        (print/km-format expr)
                        (print/km-format (:value found))
                        (print/km-format (term/car (:value found))))
          (assoc :value (term/car (:value found))))
      (= fail-mode :error)
      (report-error found :user-error "Expression %s didn't return a value!"
                    (print/km-format expr))
      :else found)))

(defn interpret
  "Evaluate one expression from the top level.

  The query's goal stack, the instances being unified, both inference
  counters, the depth, and the looping flag are cleared first. The
  object stack and the knowledge base stay. fail-mode is the argument,
  or the mode stored on the query, or :fail. :value is the answer list.
  A form that is not ported yet has :error \"not-ported\"."
  [kb query expr & {:keys [fail-mode]}]
  (let [query (reset-top query)
        fail-mode (or fail-mode (:top-level-fail-mode query) :fail)
        expr (if (showme-head? expr) expr (frame/dereference kb expr))
        state {:kb kb
               :query query
               :errors []
               :error-structures []
               :warnings []
               :fail-mode fail-mode}
        result (km-int state expr :fail-mode fail-mode)]
    (if (refused? result)
      result
      (update result :value explain/desource))))
