(ns som.km.interpreter
  "The Knowledge Machine interpreter.

  km and km-int share one dispatcher. The handler table is the Lisp
  alist in its original order, and the first match wins. A form this
  step does not run is still in that table, and it returns the
  not-ported refusal. Literals, arithmetic, comparisons, local assert
  and lookup, unification, constraint checks, subsumption, and the
  commands from the goal-stack step are evaluated. (the Class with ...)
  searches instances already stored. (the+ Class with ...) searches and
  then tries to create, which is still refused. (every Class has ...)
  stores a rule that a slot read inherits. (a-prototype Class) builds a
  prototype, and a later slot read clones it. (a Class) does that only
  while a prototype is being built, except (a Situation) and (a Theory),
  which create an instance either way. (why) prints a stored
  explanation as a KM form. (justify) prints that form too, unless
  justify-leaves is on, in which case a leaf is one English sentence.
  (get-justification) returns the same text. (make-sentence),
  (make-phrase), and (andify) build English. (pluralize) records that
  it is no longer defined. (taxonomy) prints the subclass tree.
  Situations, actions, and theories run. (do-plan) walks a chain of
  events. (evaluate) runs a quoted expression. (trace), (untrace), spy,
  and profile run. (license) prints the licence text. do-script and the
  is-true commands stay refused. load-kb, save-kb, write-kb, checkpoint,
  and undo run. fastsave-kb stays refused.
  Embedded Lisp is not evaluated.

  :value is the answer list. :errors, :error-structures, and :warnings
  collect the notes the Lisp returns beside the answer. An error is
  recorded and reasoning continues, unless the query's :on-error is
  :abort or :abort-silently. A trace line is recorded on :text. The
  interactive debugger is not entered."
  (:require [clojure.string :as str]
            [som.km.anglify :as anglify]
            [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.license :as license]
            [som.km.loadkb :as loadkb]
            [som.km.minimatch :as match]
            [som.km.print :as print]
            [som.km.prototypes :as prototypes]
            [som.km.sadl :as sadl]
            [som.km.situations :as situations]
            [som.km.slotvals :as slotvals]
            [som.km.stack :as stack]
            [som.km.stats :as stats]
            [som.km.subsumes :as subsumes]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.trace :as trace]
            [som.km.unify :as unify]
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

(defn- report-error
  "Record one error and continue, unless the query says to abort.

  user-warning is a warning. The other kinds are errors. The text is
  kept, and the expression on the goal stack is kept with it. :value
  is left as it is. Nothing is printed."
  [state kind template & args]
  (apply errors/report-error state kind template args))

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
    "eval" "setq" "tracekm" "untracekm" "license" "licence" "enable-slot-checking"
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

(defn- prepare-top
  "The part of a top-level call that clears the query's reasoning.

  The stacks, the depth, the trace depth, and the looping flag are
  always cleared. The counters, including knowledge-base accesses, are
  zeroed only when reset statistics is enabled. Tracing is reset either
  way, so a trace left on comes back on. The object stack, the fail
  mode, a caller's depth limit, and a caller's :on-error stay.
  Installing inverses is left as the caller set it."
  [kb query]
  (let [kb (trace/reset-trace kb)
        base (assoc (or query frame/empty-query)
                    :goal-stack nil
                    :instances-being-unified nil
                    :depth 0
                    :trace-depth 0
                    :looping? false
                    :profiling? false)
        now (System/nanoTime)]
    (if (stats/reset-enabled? kb)
      {:kb (assoc-in kb [:runtime :kb-accesses] 0)
       :query (assoc base
                     :classification-inferences 0
                     :query-directed-inferences 0
                     :skolems 0
                     :unifications 0
                     :max-depth 0
                     :classifications-attempted 0
                     :classifications-succeeded 0
                     :statistics-cpu-start now
                     :spot-runtime now)}
      {:kb kb :query base})))

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
          :text (str (:text state) (:text shown)))
   expr fail-mode "show-goal-stack"))

(defn- lisp-command
  [state expr name fail-mode]
  (or (loadkb/logging-command state expr name)
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
             :text (str (:text state) (:text shown))))

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

    (= name "no-explanations")
    (assoc state
           :kb (frame/set-record-explanations (:kb state) false)
           :value (term/km-list (symbol "t")))

    (= name "explanations")
    (let [slots (term/cdr expr)]
      (assoc state
             :kb (frame/set-record-explanations
                  (:kb state)
                  (if (nil? slots) true (vec (utils/elements slots))))
             :value (term/km-list (symbol "t"))))

    (contains? #{"license" "licence"} name)
    (if (term/singleton? expr)
      (no-values-if-error
       (assoc state :text (str (:text state) (license/text)) :value nil)
       expr fail-mode name)
      (embedded-refusal state expr nil))

    (contains? #{"comments" "nocomments"} name)
    (if (term/singleton? expr)
      (if (= name "comments")
        (trace/comments-command state)
        (trace/nocomments-command state))
      (embedded-refusal state expr nil))

    (contains? #{"trace-to-file-on" "t2f-on"} name)
    (let [tail (term/cdr expr)]
      (cond
        (nil? tail) (trace/trace-to-file-on state nil)
        (term/singleton? tail) (trace/trace-to-file-on state (term/car tail))
        :else (embedded-refusal state expr nil)))

    (contains? #{"trace-to-file-off" "t2f-off"} name)
    (if (term/singleton? expr)
      (trace/trace-to-file-off state)
      (embedded-refusal state expr nil))

    (contains? #{"eval" "setq" "km-setq"} name)
    (embedded-refusal state expr (str name " is not evaluated."))

    :else
    (embedded-refusal state expr nil))))

(defn- command
  "A trace command, a load or save, or an embedded-Lisp name.

  These run before a goal is pushed, so they do not count as an
  inference. A trace command is the exact singleton. Extra arguments do
  not match it. nil means this expression is not one of those commands."
  [state expr fail-mode]
  (let [name (head-name expr)]
    (cond
      (exact-trace? expr)
      (if (str/starts-with? name "untrace")
        (trace/untrace-command state)
        (trace/trace-command state))

      (= name "undo")
      (loadkb/undo-command state
                           (when (term/cons? (term/cdr expr))
                             (term/car (term/cdr expr))))

      (contains? load-save-names name)
      (cond
        (contains? #{"fastsave-kb" "faslsave-kb" "fastload-kb"} name)
        (refuse-text state (str "fastsave stays unported: " (print/km-format expr) "."))

        (= name "load-newest-kb")
        (refuse-text state
                     (str "Loading and saving a knowledge base is not ported yet: "
                          (print/km-format expr) "."))

        (contains? #{"load-kb" "reload-kb"} name)
        (loadkb/load-command state expr km-int (= name "reload-kb"))

        (= name "save-kb")
        (loadkb/save-command state expr)

        (= name "write-kb")
        (loadkb/write-command state expr)

        :else
        (refuse-text state
                     (str "Loading and saving a knowledge base is not ported yet: "
                          (print/km-format expr) ".")))

      (= name "show-goal-stack")
      (show-stack-command state expr fail-mode
                          (stack/show-goal-stack (:kb state) (:query state)))

      (or (contains? lisp-exprs name) (= name "km-setq"))
      (lisp-command state expr name fail-mode)

      :else nil)))

(defn- reserved-name?
  "True when value is a reserved keyword and not an existing frame.

  append is both a keyword and a built-in slot. A saved instances list
  names it. A keyword that is not a frame is still refused."
  [state value]
  (and (contains? kb/reserved-keywords value)
       (not (and (kb/kb-object? value)
                 (frame/known-frame? (:kb state) value)))))

(defn- reserved-hits
  [state values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values)) nil
      (reserved-name? state (term/car values))
      (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- no-reserved
  "A state whose keywords were reported, or nil when the list is clean."
  [state values]
  (when-let [hits (reserved-hits state values)]
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
      (let [traced (trace/km-trace state :comment "Looping on ~a!" [cleaned])
            handled (stack/handle-looping (:kb traced) (:query traced) cleaned)]
        (use-result traced handled))

      (too-deep? query)
      (let [traced (trace/km-trace state :comment
                                   "Maximum depth limit reached, doing ~a!"
                                   [cleaned])
            handled (stack/handle-looping (:kb traced) (:query traced) cleaned
                                          :reason :depth-limit-reached)]
        (use-result traced handled))

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
                frames-state (if (= 1 (get-in frames-state [:query :depth]))
                               (assoc-in frames-state [:query :last-question]
                                         (term/km-list (symbol "the") slot (symbol "of")
                                                       (kb/vals-to-val frames)))
                               frames-state)
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

(defn- listed
  "Wrap one created name as an answer list.

  A refusal is returned unchanged. A nil answer stays nil."
  [state]
  (cond
    (refused? state) state
    (nil? (:value state)) state
    :else (assoc state :value (term/km-list (:value state)))))

(defn- expand-prototype-paths
  "Evaluate paths while a prototype is open, and keep the created name.

  The command answers (t). A refusal from a nested form is returned.
  A recorded user error stays with the created name."
  [state instance]
  (let [expanded (km-int state (term/km-list (symbol "evaluate-paths")))]
    (if (refused? expanded)
      expanded
      (assoc expanded :value (term/km-list instance)))))

(defn- situation-or-theory?
  [class]
  (and (kb/kb-object? class)
       (or (utils/eql? class (symbol "Situation"))
           (utils/eql? class (symbol "Theory")))))

(defn- a-handler
  "Create a participant while a prototype is open.

  (a Situation) and (a Theory) create an instance outside that mode.
  (a Cat) stays refused."
  [state pieces]
  (cond
    (frame/curr-prototype (:kb state))
    (listed (prototypes/create-instance state (first pieces) nil))
    (situation-or-theory? (first pieces))
    (listed (prototypes/create-instance state (first pieces) nil))
    :else (refuse state pieces)))

(defn- a-with-handler
  "Create a participant and evaluate the paths in its slots.

  (a Situation with ...) and (a Theory with ...) create an instance
  outside prototype mode and do not evaluate those paths. (a Cat with
  ...) stays refused. called stays refused."
  [state pieces]
  (let [[class slotsvals] pieces]
    (cond
      (frame/curr-prototype (:kb state))
      (let [created (prototypes/create-instance state class slotsvals)]
        (cond
          (refused? created) created
          (nil? (:value created)) created
          :else (expand-prototype-paths created (:value created))))
      (situation-or-theory? class)
      (let [[checked ok?] (slotsvals-ok? state slotsvals)]
        (if-not ok?
          checked
          (listed (prototypes/create-instance checked class slotsvals))))
      :else (refuse state pieces))))

(defn- a-prototype-handler
  "(a-prototype Class) is (a-prototype Class with)."
  [state pieces]
  (km-int state
          (term/km-list (symbol "a-prototype") (first pieces) (symbol "with"))
          :rewrite? true))

(defn- a-prototype-with-handler
  "Enter prototype mode after the situation and the slot pairs are checked.

  The slot pairs are checked only when the situation allows entry.
  (a-prototype Class with ...) does not evaluate an (a ...) in those pairs."
  [state pieces]
  (let [[class slotsvals] pieces]
    (if-let [blocked (prototypes/reject-prototype-entry state class slotsvals)]
      blocked
      (let [[checked ok?] (slotsvals-ok? state slotsvals)]
        (if-not ok?
          checked
          (prototypes/enter-prototype checked class slotsvals))))))

(defn- end-prototype-handler
  [state _]
  (prototypes/end-prototype state))

(defn- clone-handler
  [state pieces]
  (let [unique (km-unique-int state (first pieces) :fail-mode :error)]
    (cond
      (refused? unique) unique
      (nil? (:value unique)) unique
      :else (listed (prototypes/clone unique (:value unique))))))

(defn- evaluate-paths-handler
  "Expand the object stack. The answer is (t), including after a user error."
  [state _]
  (let [expanded (prototypes/evaluate-paths state km-int)]
    (if (refused? expanded)
      expanded
      (assoc expanded :value (term/km-list (symbol "t"))))))

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
                                              :query (:query checked)
                                              :errors (:errors checked)
                                              :warnings (:warnings checked)
                                              :error-structures (:error-structures checked))]
              (if (refused? stored)
                stored
                ;; A has-definition is still refused, so classification
                ;; does not reassign an instance's class. The flags stay
                ;; on for the step that stores definitions.
                (let [done (assoc checked
                                  :kb (frame/un-done (:kb stored) instance)
                                  :query (:query stored)
                                  :errors (vec (or (:errors stored) []))
                                  :warnings (vec (or (:warnings stored) []))
                                  :error-structures (vec (or (:error-structures stored) []))
                                  :value (term/km-list instance))]
                  (if (frame/curr-prototype (:kb done))
                    (expand-prototype-paths done instance)
                    done))))
            (catch clojure.lang.ExceptionInfo thrown
              (-> (report-error checked :user-error "%s" (.getMessage thrown))
                  (assoc :value nil)))))))))

(defn- every-slots
  "Store member rules on a class. has, also-has, and now-has share this.

  combine is nil, appending, or overwriting. Each instance of the class
  drops its cached answers. The assertions slot is not recorded."
  [head combine]
  (fn [state pieces]
    (let [[cexpr slotsvals] pieces
          unique (km-unique-int state cexpr :fail-mode :error)
          class (:value unique)]
      (cond
        (refused? unique) unique
        (not (kb/kb-object? class))
        (-> (report-error unique :user-error
                          "%s%n%s isn't/doesn't evaluate to a class name."
                          (print/km-format (term/build-list [cexpr head] slotsvals))
                          (print/km-format cexpr))
            (assoc :value nil))
        :else
        (let [[checked ok?] (slotsvals-ok? unique slotsvals)]
          (if-not ok?
            checked
            (try
              (let [annotated (explain/annotate-slotsvals
                               slotsvals (explain/make-source class))
                    stored (frame/add-slotsvals (:kb checked) class
                                                (explain/convert-comments annotated)
                                                :facet (symbol "member-properties")
                                                :bind-self? false
                                                :combine-values-by combine
                                                :query (:query checked)
                                                :errors (:errors checked)
                                                :warnings (:warnings checked)
                                                :error-structures (:error-structures checked))]
                (if (refused? stored)
                  stored
                  (let [instances (taxonomy/all-instances (:kb stored) class)
                        cleared (loop [rest (:value instances)
                                       kb (:kb instances)]
                                  (if (nil? rest)
                                    kb
                                    (recur (term/cdr rest)
                                           (frame/un-done kb (term/car rest)))))]
                    (assoc checked
                           :kb cleared
                           :query (:query stored)
                           :errors (vec (or (:errors stored) []))
                           :warnings (vec (or (:warnings stored) []))
                           :error-structures (vec (or (:error-structures stored) []))
                           :value (term/km-list class)))))
              (catch clojure.lang.ExceptionInfo thrown
                (-> (report-error checked :user-error "%s" (.getMessage thrown))
                    (assoc :value nil))))))))))

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

(defn- subst-symbol
  "Replace old with new through a cons tree. Atoms stay as they are."
  [new old expr]
  (cond
    (utils/eql? expr old) new
    (term/cons? expr)
    (term/cons-cell (subst-symbol new old (term/car expr))
                    (subst-symbol new old (term/cdr expr)))
    :else expr))

(defn- strip-trial
  "Drop the keys a unification trial uses internally."
  [state]
  (dissoc state :unification-reported :ok :problem :bindings :slots))

(defn- rollback-unify
  "Keep a successful unification. A failure restores the entry state.

  Errors from the attempt stay. A refusal is returned as it is. The
  snapshot is the state the handler received, after the outer goal was
  pushed."
  [snapshot attempt]
  (let [attempt (strip-trial attempt)]
    (cond
      (refused? attempt) attempt
      (some? (:value attempt)) attempt
      :else (assoc attempt :kb (:kb snapshot) :query (:query snapshot) :value nil))))

(defn- unify-handler
  [state pieces joiner]
  (let [[x rest] pieces
        expr (term/build-list [x joiner] rest)]
    (rollback-unify state
                    (unify/lazy-unify-&-expr state expr km-int
                                             :joiner joiner
                                             :fail-mode :error
                                             :target (:target state)))))

(defn- eq-handler
  [state pieces]
  (let [[x y] pieces]
    (rollback-unify state
                    (unify/lazy-unify-&-expr state
                                             (term/km-list x (symbol "==") y)
                                             km-int
                                             :joiner (symbol "==")
                                             :fail-mode :error
                                             :target (:target state)))))

(defn- neq-handler
  "Store (/== (other)) on a knowledge-base object.

  Two equal values are an error. Two other non-objects answer (t)."
  [state pieces]
  (let [[x y] pieces
        left (km-unique-int state x :fail-mode :error)]
    (if (refused? left)
      left
      (let [right (km-unique-int left y :fail-mode :error)
            xv (:value left)
            yv (:value right)]
        (cond
          (refused? right) right
          (utils/equal? xv yv)
          (-> (report-error right :user-error
                            "(%s /== %s): %s and %s are the same object!"
                            (print/km-format x)
                            (print/km-format y)
                            (print/km-format x)
                            (print/km-format y))
              (assoc :value nil))
          (kb/kb-object? xv)
          (km-int right
                  (term/km-list xv
                                (symbol "has")
                                (term/km-list (symbol nil "/==")
                                              (term/km-list yv)))
                  :fail-mode :error)
          (kb/kb-object? yv)
          (km-int right
                  (term/km-list yv
                                (symbol "has")
                                (term/km-list (symbol nil "/==")
                                              (term/km-list xv)))
                  :fail-mode :error)
          :else (assoc right :value (term/km-list (symbol "t"))))))))

(defn- truth
  [state]
  (assoc (strip-trial state) :value (term/km-list (symbol "t"))))

(defn- existential-test
  [state value expr classes-subsumep]
  (let [hit (unify/unifiable-with-existential state value expr km-int
                                              :classes-subsumep classes-subsumep
                                              :fail-mode :fail)]
    (if (refused? hit) hit (strip-trial hit))))

(defn- test-handler
  "Whether x and y can unify. The trial is discarded.

  &? treats a null argument as success before evaluation. &+? does not.
  Evaluating an argument still commits. The test itself does not."
  [state pieces classes-subsumep]
  (let [[x y] pieces]
    (cond
      (and (not classes-subsumep) (or (nil? x) (nil? y)))
      (truth state)
      (kb/existential? y)
      (let [found (km-unique-int state x)]
        (cond
          (refused? found) found
          (nil? (:value found)) (truth found)
          :else (existential-test found (:value found) y classes-subsumep)))
      (kb/existential? x)
      (let [found (km-unique-int state y)]
        (cond
          (refused? found) found
          (nil? (:value found)) (truth found)
          :else (existential-test found (:value found) x classes-subsumep)))
      :else
      (let [left (km-unique-int state x)]
        (cond
          (refused? left) left
          (nil? (:value left)) (truth left)
          :else
          (let [right (km-unique-int left y)]
            (cond
              (refused? right) right
              (nil? (:value right)) (truth right)
              :else
              (let [hit (unify/try-lazy-unify right
                                              (:value left)
                                              (:value right)
                                              km-int
                                              :classes-subsumep classes-subsumep)]
                (if (refused? hit) hit (strip-trial hit))))))))))

(defn- plus-handler
  "Unify with class subsumption. A failure restores the entry state.

  The caller's fail mode is used. :error adds one sentence when the
  attempt did not already record a specific problem."
  [state pieces]
  (let [[x y] pieces
        mode (:fail-mode state)
        attempt (unify/lazy-unify-exprs state x y km-int
                                        :classes-subsumep true
                                        :fail-mode mode
                                        :target (:target state))
        reported? (:unification-reported attempt)]
    (cond
      (refused? attempt) (strip-trial attempt)
      (some? (:value attempt))
      (strip-trial (assoc attempt :value (term/km-list (:value attempt))))
      :else
      (let [rolled (assoc (strip-trial attempt)
                          :kb (:kb state)
                          :query (:query state)
                          :value nil)]
        (if (and (= mode :error) (not reported?))
          (-> (report-error rolled :user-error "Unification (%s &+ %s) failed!"
                            (print/km-format x)
                            (print/km-format y))
              (assoc :value nil))
          rolled)))))

(defn- plus-eager-handler
  "Test with &+?, then perform &! when the test succeeds.

  A quiet failure is allowed. Argument evaluation from the test stays."
  [state pieces]
  (let [[x y] pieces
        mode (:fail-mode state)
        tested (km-int state (term/km-list x (symbol "&+?") y)
                       :target (:target state)
                       :fail-mode mode)]
    (cond
      (refused? tested) tested
      (some? (:value tested))
      (km-int tested (term/km-list x (symbol "&!") y)
              :target (:target state)
              :fail-mode :error)
      (= mode :error)
      (-> (report-error tested :user-error "Unification (%s &+! %s) failed!"
                        (print/km-format x)
                        (print/km-format y))
          (assoc :value nil))
      :else (assoc tested :value nil))))

(defn- and-handler
  [state pieces]
  (let [[x rest] pieces]
    (if-not (and (term/triple? x) (utils/eql? (nth-value x 1) (symbol "==")))
      (let [left (km-int state x)]
        (cond
          (refused? left) left
          (nil? (:value left)) left
          :else (km-int left rest)))
      ;; The packaged source writes the literal symbol yy. The third
      ;; element is the value that was meant.
      (let [xx (term/car x)
            yy (nth-value x 2)]
        (cond
          (and (kb/km-var? xx) (kb/km-var? yy))
          (km-int state (subst-symbol xx yy rest))
          (kb/km-var? xx)
          (let [found (km-int state yy)]
            (if (refused? found)
              found
              (km-int found (subst-symbol (kb/vals-to-val (:value found)) xx rest))))
          (kb/km-var? yy)
          (let [found (km-int state xx)]
            (if (refused? found)
              found
              (km-int found (subst-symbol (kb/vals-to-val (:value found)) yy rest))))
          :else
          (let [unified (eq-handler state [xx yy])]
            (cond
              (refused? unified) unified
              (nil? (:value unified)) unified
              :else (km-int unified rest))))))))

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

(defn- in-situation-handler
  [state pieces]
  (situations/in-situation state (first pieces) nil km-int))

(defn- in-situation-body-handler
  [state pieces]
  (situations/in-situation state (first pieces) (second pieces) km-int))

(defn- in-situation-fast-handler
  "Read a slot that is already computed, without entering the situation.

  A miss evaluates (the slot of frame) in that situation and restores."
  [state pieces]
  (let [[situation slot frame] pieces
        body (term/km-list (symbol "the") slot (symbol "of") frame)]
    (if-not (kb/kb-object? situation)
      (situations/in-situation state situation body km-int)
      (let [hit (slotvals/cached-situation-lookup state situation frame slot)]
        (if (:hit hit)
          (:state hit)
          (situations/in-situation (:state hit) situation body km-int))))))

(defn- in-theory-handler
  [state pieces]
  (situations/in-situation state (first pieces) nil km-int :theory? true))

(defn- in-theory-body-handler
  [state pieces]
  (situations/in-situation state (first pieces) (second pieces) km-int :theory? true))

(defn- end-situation-handler
  [state _]
  (situations/in-situation state term/global-situation nil km-int))

(defn- visible-theories-handler
  [state _]
  (assoc state :value (frame/visible-theories (:kb state))))

(defn- see-theory-handler
  [state pieces]
  (situations/revise-visible-theories state (first pieces) km-int false))

(defn- hide-theory-handler
  [state pieces]
  (situations/revise-visible-theories state (first pieces) km-int true))

(defn- new-situation-handler
  [state _]
  (situations/new-situation state km-int))

(defn- do-handler
  [state pieces]
  (situations/do-form state (first pieces) nil km-int))

(defn- do-next-handler
  [state pieces]
  (situations/do-form state (first pieces) (second pieces) km-int))

(defn- do-and-next-handler
  [state pieces]
  (situations/do-form state (first pieces) nil km-int :change-to-next? true))

(defn- do-and-next-at-handler
  [state pieces]
  (situations/do-form state (first pieces) (second pieces) km-int :change-to-next? true))

(defn- try-do-handler
  [state pieces]
  (situations/do-form state (first pieces) nil km-int :test? true))

(defn- try-do-at-handler
  [state pieces]
  (situations/do-form state (first pieces) (second pieces) km-int :test? true))

(defn- try-do-and-next-handler
  [state pieces]
  (situations/do-form state (first pieces) nil km-int :change-to-next? true :test? true))

(defn- try-do-and-next-at-handler
  [state pieces]
  (situations/do-form state (first pieces) (second pieces) km-int
                     :change-to-next? true :test? true))

(defn- do-concurrently-handler
  [state pieces]
  (situations/do-concurrently state (first pieces) km-int))

(defn- do-concurrently-at-handler
  [state pieces]
  (situations/do-concurrently state (first pieces) km-int :next (second pieces)))

(defn- do-concurrently-and-next-handler
  [state pieces]
  (situations/do-concurrently state (first pieces) km-int :change-to-next? true))

(defn- do-concurrently-and-next-at-handler
  [state pieces]
  (situations/do-concurrently state (first pieces) km-int
                              :next (second pieces)
                              :change-to-next? true))

(defn- next-situation-handler
  [state _]
  (let [result (situations/next-command state km-int)]
    (if (nil? (:value result))
      result
      (situations/answer-one result))))

(defn- curr-situation-handler
  [state _]
  (assoc state :value (term/km-list (frame/current-situation (:kb state)))))

(defn- later
  [pattern]
  (entry pattern refuse))

(defn- sentence-command
  [state pieces capitalize? terminator]
  (let [evaluated (km-int state (first pieces))]
    (if (refused? evaluated)
      evaluated
      (let [built (anglify/make-sentence evaluated (:value evaluated) km-int
                                         :capitalize? capitalize?
                                         :terminator terminator
                                         :unique km-unique-int)]
        (cond
          (refused? built) built
          (refused? (:state built)) (:state built)
          :else (assoc (:state built) :value (term/km-list (:text built))))))))

(defn- andify-command
  [state pieces]
  (let [evaluated (km-int state (first pieces) :rewrite? true)]
    (if (refused? evaluated)
      evaluated
      (assoc evaluated
             :value (term/km-list
                     (term/cons-cell :seq (anglify/andify (:value evaluated))))))))

(defn- pluralize-command
  [state pieces]
  (-> (report-error state :user-error
                    "(pluralize %s): pluralize is no longer defined in KM1.4 - use \"-s\" suffix instead!"
                    (print/km-format (first pieces)))
      (assoc :value nil)))

(defn- finish-taxonomy
  [state node relation]
  (let [printed (taxonomy/taxonomy-text state node relation km-int)]
    (if (refused? (:state printed))
      (:state printed)
      (assoc (:state printed) :value (term/km-list (symbol "t"))))))

(defn- taxonomy-command
  [state pieces]
  (let [args (first pieces)]
    (cond
      (nil? args)
      (finish-taxonomy state (symbol "Thing") (symbol "subclasses"))

      (term/singleton? args)
      (let [node (km-unique-int state (term/car args))]
        (if (refused? node)
          node
          (finish-taxonomy node (:value node) (symbol "subclasses"))))

      (term/pair? args)
      (let [node (km-unique-int state (term/car args))]
        (if (refused? node)
          node
          (let [relation (km-unique-int node (term/car (term/cdr args)))]
            (if (refused? relation)
              relation
              (finish-taxonomy relation (:value node) (:value relation))))))

      :else
      (-> (report-error state :user-error
                        "Too many arguments to the taxonomy function! Format is (taxonomy <top-node> <relation-to-descend>)")
          (assoc :value nil)))))

(defn- keeping-kb-handler
  [state pieces]
  (loadkb/keeping-kb state (first pieces) km-int))

(defn- checkpoint-id-handler
  [state pieces]
  (let [found (km-unique-int state (first pieces))]
    (if (refused? found)
      found
      (loadkb/checkpoint-command found (:value found)))))

(def ^:private op-symbol
  {"+" (symbol "+") "-" (symbol "-") "*" (symbol "*")
   "/" (symbol "/") "^" (symbol "^")})

(defn- rewrite
  [op next-op]
  (entry ["?x" op "?y" next-op "&rest"]
         (rewrite-handler (op-symbol op) (op-symbol next-op))))

(defn- existential-for
  "The (a Class with ...) a search uses. A bare path becomes that description."
  [state frame slotsvals]
  (if (and (nil? slotsvals) (utils/lisp-list? frame))
    (subsumes/path-to-existential-expr (:kb state) frame)
    (term/build-list [(symbol "a") frame (symbol "with")] slotsvals)))

(defn- flag
  "Wrap a truthy subsumption result as (t)."
  [state]
  (if (refused? state)
    state
    (assoc state :value (when (:value state) (term/km-list (symbol "t"))))))

(defn- every-frame-handler
  [state pieces]
  (km-int state (term/km-list (symbol "every") (first pieces) (symbol "with"))
          :fail-mode (:fail-mode state)
          :target (:target state)
          :rewrite? true))

(defn- every-with-handler
  [state pieces]
  (let [[frame slotsvals] pieces
        [checked ok?] (slotsvals-ok? state slotsvals)]
    (if-not ok?
      checked
      (subsumes/find-subsumees checked (existential-for checked frame slotsvals)))))

(defn- demand-one
  [state answer expr]
  (cond
    (refused? answer) answer
    (nil? (:value answer))
    (-> (report-error answer :user-error
                      "No values found for expression %s!%n"
                      (print/km-format expr))
        (assoc :value nil))
    (not (term/singleton? (:value answer)))
    (-> (report-error answer :user-error
                      "Expected a single value for expression %s, but found multiple values %s!%n"
                      (print/km-format expr)
                      (print/km-format (:value answer)))
        (assoc :value nil))
    :else answer))

(defn- the-frame-handler
  [state pieces]
  (let [frame (first pieces)]
    (demand-one state
                (km-int state (term/km-list (symbol "every") frame))
                (term/km-list (symbol "the") frame))))

(defn- the-with-handler
  [state pieces]
  (let [[frame slotsvals] pieces]
    (demand-one state
                (km-int state (term/build-list [(symbol "every") frame (symbol "with")] slotsvals))
                (term/build-list [(symbol "the") frame (symbol "with")] slotsvals))))

(defn- the-plus-slot-handler
  [state pieces]
  (let [[slot frameadd] pieces]
    (km-int state
            (term/km-list (symbol "the+") (symbol "Thing") (symbol "with")
                          (term/km-list (frame/invert-slot (:kb state) slot)
                                        (term/km-list frameadd)))
            :fail-mode :error
            :target (:target state)
            :rewrite? true)))

(defn- the-plus-class-handler
  [state pieces]
  (let [[class slot frameadd] pieces]
    (km-int state
            (term/km-list (symbol "the+") class (symbol "with")
                          (term/km-list (frame/invert-slot (:kb state) slot)
                                        (term/km-list frameadd)))
            :fail-mode :error
            :target (:target state)
            :rewrite? true)))

(defn- the-plus-frame-handler
  [state pieces]
  (km-int state (term/km-list (symbol "the+") (first pieces) (symbol "with"))
          :fail-mode (:fail-mode state)
          :target (:target state)
          :rewrite? true))

(defn- the-plus-with-handler
  [state pieces]
  (let [[frame slotsvals] pieces
        found (km-unique-int state
                             (term/build-list [(symbol "every") frame (symbol "with")] slotsvals))]
    (cond
      (refused? found) found
      (some? (:value found)) (assoc found :value (term/km-list (:value found)))
      :else
      (let [[checked ok?] (slotsvals-ok? found slotsvals)]
        (if-not ok?
          checked
          (km-int checked (existential-for checked frame slotsvals)
                  :fail-mode :error
                  :target (:target state)))))))

(defn- a-plus-handler
  [state pieces]
  (km-int state (term/cons-cell (symbol "the+") (first pieces))
          :fail-mode (:fail-mode state)
          :target (:target state)
          :rewrite? true))

(defn- subsumed-by-handler
  [state pieces]
  (let [[x y] pieces]
    (km-int state (term/km-list y (symbol "subsumes") x)
            :fail-mode (:fail-mode state)
            :target (:target state)
            :rewrite? true)))

(defn- subsumes-handler
  [state pieces]
  (let [[x y] pieces
        yv (km-int state y)]
    (cond
      (refused? yv) yv
      (nil? (:value yv)) (assoc yv :value (term/km-list (symbol "t")))
      :else
      (let [xv (km-int yv x)]
        (cond
          (refused? xv) xv
          (nil? (:value xv)) (assoc xv :value nil)
          :else (flag (subsumes/subsumes-values xv (:value xv) (:value yv) km-int)))))))

(defn- covered-by-handler
  [state pieces]
  (let [[x y] pieces]
    (km-int state (term/km-list y (symbol "covers") x)
            :fail-mode (:fail-mode state)
            :target (:target state)
            :rewrite? true)))

(defn- covers-handler
  [state pieces]
  (let [[x y] pieces]
    (km-int state (term/km-list y (symbol "isa") x)
            :fail-mode (:fail-mode state)
            :target (:target state)
            :rewrite? true)))

(defn- isa-handler
  [state pieces]
  (let [[y x] pieces
        expr (term/km-list y (symbol "isa") x)
        yvals (km-int state y)]
    (cond
      (refused? yvals) yvals
      (nil? (:value yvals))
      (-> (report-error yvals :user-error
                        "Doing %s:%n %s evaluates to nil (should evaluate to an instance!)~%"
                        (print/km-format expr)
                        (print/km-format y))
          (assoc :value nil))
      (not (term/singleton? (:value yvals)))
      (-> (report-error yvals :user-error
                        "Doing %s:%n %s evaluates to multiple values %s (should evaluate to a single instance!)~%"
                        (print/km-format expr)
                        (print/km-format y)
                        (print/km-format (:value yvals)))
          (assoc :value nil))
      :else
      (let [xvals (km-int yvals x)
            yv (term/car (:value yvals))]
        (cond
          (refused? xvals) xvals
          (nil? (:value xvals))
          (-> (report-error xvals :user-error
                            "Doing %s:%n %s evaluates to nil (should evaluate to something!)~%"
                            (print/km-format expr)
                            (print/km-format x))
              (assoc :value nil))
          (not (term/singleton? (:value xvals)))
          (-> (report-error xvals :user-error
                            "Doing %s:%n %s evaluates to multiple values %s (should evaluate to a single object!)~%"
                            (print/km-format expr)
                            (print/km-format x)
                            (print/km-format (:value xvals)))
              (assoc :value nil))
          (kb/kb-object? (term/car (:value xvals)))
          (let [hit (taxonomy/isa? (:kb xvals) yv (term/car (:value xvals)))]
            (assoc xvals :kb (:kb hit)
                   :value (when (:value hit) (term/km-list (symbol "t")))))
          :else
          (flag (subsumes/covers-value xvals
                                      (term/km-list (term/car (:value xvals)))
                                      yv
                                      km-int)))))))

(defn- is-handler
  [state pieces]
  (let [[x y] pieces
        xv (km-unique-int state x)]
    (cond
      (refused? xv) xv
      (nil? (:value xv)) (assoc xv :value nil)
      :else
      (let [yv (km-unique-int xv y)]
        (cond
          (refused? yv) yv
          (nil? (:value yv)) (assoc yv :value nil)
          :else (flag (subsumes/is-value yv (:value xv) (:value yv) km-int)))))))

(defn- subset-of?
  [items coll]
  (loop [items items]
    (cond
      (nil? items) true
      (not (term/cons? items)) false
      (utils/member? (term/car items) coll utils/equal?) (recur (term/cdr items))
      :else false)))

(defn- includes-handler
  [state pieces]
  (let [[xs y] pieces
        xs-vals (km-int state xs)]
    (if (refused? xs-vals)
      xs-vals
      (let [y-val (km-unique-int xs-vals y)]
        (if (refused? y-val)
          y-val
          (assoc y-val :value
                 (when (utils/member? (:value y-val)
                                      (frame/dereference (:kb y-val) (:value xs-vals))
                                      utils/equal?)
                   (term/km-list (symbol "t")))))))))

(defn- superset-handler
  [state pieces]
  (let [[xs ys] pieces
        xs-vals (km-int state xs)]
    (if (refused? xs-vals)
      xs-vals
      (let [ys-vals (km-int xs-vals ys)]
        (if (refused? ys-vals)
          ys-vals
          (assoc ys-vals :value
                 (when (subset-of? (:value ys-vals)
                                   (frame/dereference (:kb ys-vals) (:value xs-vals)))
                   (term/km-list (symbol "t")))))))))

(defn- append-text
  [state text]
  (assoc state :text (str (:text state) text)))

(defn- report-set-explanation
  [state recorded]
  (report-error (assoc state :kb (:kb recorded))
                :program-error
                "A not-fully-evaluated :set was unexpectedly passed as an explanation to %s."
                (print/km-format
                 (term/km-list (symbol "record-explanation-for")
                               (:target recorded) (:val recorded) (:expr recorded)))))

(defn- why-direction
  [state structure situation]
  (let [instance (term/car structure)
        slot (nth-value structure 1)
        value (nth-value structure 2)
        explanations (nth-value structure 3)
        state (append-text state (str "(:triple " (print/km-format instance) " "
                                      (print/km-format slot) " "
                                      (print/km-format value)
                                      " [in " (print/km-format situation) "]) because:\n"))]
    (append-text
     (reduce (fn [state explanation]
               (let [rule (explain/desource-for-printing (explain/build-rule explanation))]
                 (append-text state (str "   RULE: " (print/km-format rule) "\n"))))
             state
             (utils/elements explanations))
     "\n")))

(defn- why0
  "Print the explanations of one triple. The answer is (t)."
  [state triple situation]
  (let [instance0 (kb/arg1 triple)
        slot (kb/arg2 triple)
        value0 (kb/arg3 triple)
        instance (frame/dereference (:kb state) instance0)
        value (frame/dereference (:kb state) value0)
        found (frame/explanations-for (:kb state) instance slot value :situation situation)
        state (assoc state :kb (:kb found))
        state (cond-> state
                (not (utils/equal? instance instance0))
                (append-text (str "(" (print/km-format instance0) " is bound to "
                                  (print/km-format instance) ")\n"))
                (not (utils/equal? value value0))
                (append-text (str "(" (print/km-format value0) " is bound to "
                                  (print/km-format value) ")\n")))]
    (if (nil? (:value found))
      (-> (append-text state (str "(:triple " (print/km-format instance) " "
                                  (print/km-format slot) " "
                                  (print/km-format value)
                                  " [in " (print/km-format situation)
                                  "]) because:\n  (no explanation available)\n"))
          (assoc :value (term/km-list (symbol "t"))))
      (assoc (reduce (fn [state structure]
                       (why-direction state structure situation))
                     state
                     (utils/elements (:value found)))
             :value (term/km-list (symbol "t"))))))

(defn- why-pairs
  [state slot instances values situation]
  (loop [instances instances
         state state]
    (cond
      (or (nil? instances) (not (term/cons? instances)))
      (assoc state :value (term/km-list (symbol "t")))
      :else
      (let [instance (term/car instances)]
        (recur (term/cdr instances)
               (loop [values values
                      state state]
                 (if (or (nil? values) (not (term/cons? values)))
                   state
                   (recur (term/cdr values)
                          (why0 state
                                (term/km-list :triple instance slot (term/car values))
                                situation)))))))))

(def ^:private why-which
  "Which conclusion are you asking about? (Here, I can't guess). Enter in the form\n   \t(why (:triple <instance> <slot> <value>))\ne.g.\n   KM> (why (:triple _Car1 parts _Engine1))\n")

(defn- why-from-last
  [state]
  (let [answer (get-in state [:query :last-answer])]
    (if (nil? answer)
      (-> (append-text state "There are no answers to explain!\n")
          (assoc :value nil))
      (let [question (get-in state [:query :last-question])
            matched (match/minimatch question (pat ["the" "?slot" "of" "?frameadd"]))
            situation (frame/current-situation (:kb state))]
        (if-not (term/cons? matched)
          (-> (append-text state why-which)
              (assoc :value nil))
          (let [slot (term/car matched)
                frameadd (nth-value matched 1)
                instances (km-int state frameadd)]
            (if (refused? instances)
              instances
              (let [state (append-text instances
                                       (str "I'll assume you're asking me:\nWhy "
                                            (print/km-format question) " = "
                                            (print/km-format answer) "...\n\n"))]
                (why-pairs state slot (:value instances) answer situation)))))))))

(defn- why-command
  [state _]
  (why-from-last state))

(defn- why-triple
  [state pieces]
  (let [triple (first pieces)]
    (if (kb/km-triple? triple)
      (why0 state triple (frame/current-situation (:kb state)))
      (-> (report-error state :user-error
                        "Bad argument to (why ...)! Should be of form (why (:triple <f> <s> <v>))!")
          (assoc :value nil)))))

(defn- subgoal-text
  [state triple situation]
  (let [found (frame/explanations-for (:kb state)
                                      (kb/arg1 triple)
                                      (kb/arg2 triple)
                                      (kb/arg3 triple)
                                      :situation situation)
        explanations (utils/mapcan-list #(nth-value % 3) (:value found))
        rules (loop [items explanations
                     acc []]
                (cond
                  (or (nil? items) (not (term/cons? items))) acc
                  :else
                  (let [rule (explain/build-rule (term/car items))]
                    (recur (term/cdr items) (if (some? rule) (conj acc rule) acc)))))
        head (str "\nsubgoal " (print/km-format triple) ": Computed from:")]
    {:state (assoc state :kb (:kb found))
     :text (if (seq rules)
             (apply str head "\n" (map #(str "  " (print/km-format %) "\n") rules))
             (str head " (unrecorded!)"))}))

(defn- phrase-of
  "expand-text, then make-phrase, which expands again.

  A not-ported lookup is returned as the state."
  [state item]
  (let [expanded (anglify/expand-text state item km-int :unique km-unique-int)]
    (cond
      (refused? expanded) {:state expanded :text nil}
      (refused? (:state expanded)) {:state (:state expanded) :text nil}
      :else
      (let [phrased (anglify/make-phrase (:state expanded) (:value expanded)
                                         km-int :unique km-unique-int)]
        (if (refused? (:state phrased))
          {:state (:state phrased) :text nil}
          {:state (:state phrased) :text (:text phrased)})))))

(defn- english-leaf
  "One sentence for a leaf. Source classes are not ported, so the
  sentence names this triple and omits the (from ...) suffix."
  [state triple]
  (let [instance (phrase-of state (kb/arg1 triple))]
    (if (refused? (:state instance))
      {:state (:state instance) :text nil}
      (let [value (phrase-of (:state instance) (kb/arg3 triple))]
        {:state (:state value)
         :text (str "The " (print/km-format (kb/arg2 triple))
                    " of " (:text instance)
                    " = " (:text value) ".")}))))

(defn- leaf-text
  "The line (justify) prints for one triple.

  developer-mode prints the KM rule. justify-leaves, when that mode is
  off and the slot is not instance-of, prints one English sentence.
  Otherwise the KM rule is printed, which is the step 11 text."
  [state triple situation]
  (let [developer? (get-in state [:kb :runtime :developer-mode?] false)
        justify? (get-in state [:kb :runtime :justify-leaves?] false)
        slot (kb/arg2 triple)]
    (if (and (not developer?)
             justify?
             (not (utils/eql? slot (symbol "instance-of"))))
      (english-leaf state triple)
      (subgoal-text state triple situation))))

(defn- lines-for-triples
  [state triples situation depth]
  (if (> depth 20)
    {:state (append-text state
                         "(depth limit for justification reached...no further details below this)\n")
     :lines []}
    (loop [triples triples
           seen []
           state state
           lines []]
      (cond
        (or (nil? triples) (not (term/cons? triples)))
        {:state state :lines lines}
        (some #(utils/equal? % (term/car triples)) seen)
        (recur (term/cdr triples) seen state lines)
        :else
        (let [leaf (leaf-text state (term/car triples) situation)]
          (if (refused? (:state leaf))
            {:state (:state leaf) :lines []}
            (recur (term/cdr triples)
                   (conj seen (term/car triples))
                   (:state leaf)
                   (conj lines (:text leaf)))))))))

(defn- compute-triples
  "The triples a justification explains. A side-effect sentence is on :text."
  [state triple0]
  (if (some? triple0)
    (let [unique (km-unique-int state triple0)]
      (if (or (refused? unique) (nil? (:value unique)))
        {:state unique :triples nil}
        (let [triple (:value unique)
              instance (kb/arg1 triple)
              slot (kb/arg2 triple)
              value0 (kb/arg3 triple)]
          (if (utils/eql? value0 (symbol "*"))
            (let [vals (km-int unique
                               (term/km-list (symbol "the") slot (symbol "of") instance))]
              {:state vals
               :triples (term/build-list
                         (mapv #(term/km-list :triple instance slot %)
                               (utils/elements (:value vals)))
                         nil)})
            {:state unique
             :triples (term/build-list
                       (mapv #(term/km-list :triple instance slot %)
                             (utils/elements (kb/val-to-vals value0)))
                       nil)}))))
    (let [answer (get-in state [:query :last-answer])]
      (if (nil? answer)
        {:state (append-text state
                             "There's no recorded last answer, so I'm not sure what you're asking me to justify!\n")
         :triples nil}
        (let [question (get-in state [:query :last-question])
              matched (match/minimatch question (pat ["the" "?slot" "of" "?frameadd"]))]
          (if-not (term/cons? matched)
            {:state (append-text state
                                 "Which conclusion are you asking about? (Here, I can't guess). Enter in the form\n               (justify (:triple <instance> <slot> <value>))\n")
             :triples nil}
            (let [slot (term/car matched)
                  frameadd (nth-value matched 1)
                  instances (km-int state frameadd)]
              (if (refused? instances)
                {:state instances :triples nil}
                {:state (append-text instances
                                     (str "I'll assume you're asking me to justify:\n   "
                                          (print/km-format question) " = "
                                          (print/km-format answer) "...\n\n"))
                 :triples (loop [instances (:value instances)
                                 acc []]
                            (if (or (nil? instances) (not (term/cons? instances)))
                              (term/build-list acc nil)
                              (recur (term/cdr instances)
                                     (into acc
                                           (map #(term/km-list :triple
                                                               (term/car instances)
                                                               slot
                                                               %)
                                                (utils/elements answer))))))}))))))))

(defn- restoring-question
  [before produced]
  (assoc produced :query
         (assoc (:query produced)
                :last-question (get-in before [:query :last-question])
                :last-answer (get-in before [:query :last-answer]))))

(defn- justification-lines
  [state triple]
  (if (and (some? triple) (not (kb/km-triple? triple)))
    {:state (report-error state :user-error
                          "(justify %s): Argument should be a triple (justify (:triple <f> <s> <v>))!"
                          (print/km-format triple))
     :lines []}
    (let [computed (compute-triples state triple)]
      (if (refused? (:state computed))
        {:state (:state computed) :lines []}
        (let [walked (lines-for-triples (:state computed)
                                        (:triples computed)
                                        (frame/current-situation (:kb state))
                                        0)]
          {:state (:state walked) :lines (:lines walked)})))))

(defn- justify-command
  [state pieces]
  (let [before state
        found (justification-lines state (first pieces))]
    (if (refused? (:state found))
      (restoring-question before (:state found))
      (-> (restoring-question before (:state found))
          (as-> restored
              (reduce (fn [state line] (append-text state (str line "\n")))
                      restored
                      (:lines found)))
          (assoc :value (term/km-list (symbol "t")))))))

(defn- get-justification-command
  [state pieces]
  (let [before state
        found (justification-lines state (first pieces))
        restored (restoring-question before (:state found))
        joined (when (seq (:lines found)) (str/join "\n" (:lines found)))]
    (if (refused? restored)
      restored
      (assoc restored :value (when (some? joined) (term/km-list joined))))))

(defn- explanation-command
  [state pieces]
  (let [[f0 slot v0 explanations] pieces
        frame (frame/dereference (:kb state) f0)
        value (frame/dereference (:kb state) v0)
        explained (frame/dereference (:kb state) explanations)
        state (reduce (fn [state explanation]
                        (let [recorded (frame/record-explanation-for
                                        (:kb state)
                                        (term/km-list (symbol "the") slot (symbol "of") frame)
                                        value explanation
                                        :situation term/global-situation)]
                          (if (:program-error recorded)
                            (report-set-explanation state recorded)
                            (assoc state :kb (:kb recorded)))))
                      state
                      (utils/elements explained))]
    (assoc state :value (term/km-list (symbol "t")))))

(defn- do-plan-handler
  [state pieces]
  (let [found (km-unique-int state (first pieces))]
    (if (refused? found)
      found
      (sadl/do-plan found (:value found) km-int km-unique-int))))

(defn- splice-present
  [acc values]
  (loop [values values
         acc acc]
    (cond
      (nil? values) acc
      (not (term/cons? values)) acc
      (nil? (term/car values)) (recur (term/cdr values) acc)
      :else (recur (term/cdr values) (conj acc (term/car values))))))

(defn- evaluate-one
  "One result of evaluate. f and F contribute nothing. A quote is run.

  Anything else records the Lisp sentence and contributes nothing."
  [state quoted fail-mode]
  (cond
    (or (utils/eql? quoted (symbol "f"))
        (utils/eql? quoted (symbol "F")))
    {:state state :extra []}

    (utils/quote? quoted)
    (let [ran (km-int state (term/car (term/cdr quoted)) :fail-mode fail-mode)]
      (if (refused? ran)
        ran
        {:state ran :extra (splice-present [] (:value ran))}))

    :else
    {:state (report-error state :user-error
                          "(evaluate %s)%nevaluate should be given a quoted expression to evaluate!"
                          (print/km-format quoted))
     :extra []}))

(defn- evaluate-handler
  [state pieces]
  (let [fail-mode (:fail-mode state)
        quoted (km-int state (first pieces)
                       :fail-mode fail-mode
                       :target (:target state)
                       :rewrite? true)]
    (if (refused? quoted)
      quoted
      (loop [items (:value quoted)
             state quoted
             acc []]
        (cond
          (nil? items) (assoc state :value (term/build-list acc nil))
          (not (term/cons? items)) (assoc state :value (term/build-list acc nil))
          :else
          (let [step (evaluate-one state (term/car items) fail-mode)]
            (if (refused? step)
              step
              (recur (term/cdr items) (:state step) (into acc (:extra step))))))))))

(defn- profile-report-command
  [state n]
  (if (and (some? n) (not (number? n)))
    (-> (report-error state :user-error
                      "profile-report expected a number, and got %s."
                      (print/km-format n))
        (assoc :value nil))
    (-> state
        (update :text #(str % (stats/profile-report-text (:kb state)
                                                         (if (number? n) (long n) 100))))
        (assoc :value (term/km-list (symbol "t"))))))

(defn- profile-handler
  "Profile the nested expression only.

  The outer (profile ...) goal is entered before this flag is set, and
  it is left after the flag is cleared, so that goal is not in the table.
  The answer is the nested answer. The table is printed on :text."
  [state pieces]
  (let [state (-> state
                  (assoc-in [:query :profiling?] true)
                  (update :kb stats/profile-reset))
        ran (km-int state (first pieces))]
    (if (refused? ran)
      (assoc-in ran [:query :profiling?] false)
      (-> ran
          (update :text #(str % (print/km-format (:value ran)) "\n"
                              (stats/profile-report-text (:kb ran) 100)))
          (assoc-in [:query :profiling?] false)))))

(def ^:private handlers
  (into
   [(entry ["the" "?slot" "of" "?frameadd"] the-handler)
    (entry ["a" "?class"] a-handler)
    (later ["a" "?class" "called" "?tag"])
    (later ["a" "?class" "uniquely-called" "?tag"])
    (entry ["a" "?class" "with" "&rest"] a-with-handler)
    (later ["a" "?class" "uniquely-called" "?tag" "with" "&rest"])
    (later ["a" "?class" "called" "?tag" "with" "&rest"])
    (entry ["a-prototype" "?class"] a-prototype-handler)
    (entry ["a-prototype" "?class" "with" "&rest"] a-prototype-with-handler)
    (entry ["end-prototype"] end-prototype-handler)
    (entry ["clone" "?expr"] clone-handler)
    (entry ["evaluate-paths"] evaluate-paths-handler)
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
    (entry ["every" "?cexpr" "has" "&rest"] (every-slots (symbol "has") nil))
    (entry ["every" "?cexpr" "also-has" "&rest"]
           (every-slots (symbol "also-has") (symbol "appending")))
    (entry ["every" "?cexpr" "now-has" "&rest"]
           (every-slots (symbol "now-has") (symbol "overwriting")))
    (entry ["?instance-expr" "has" "&rest"] has-handler)
    (later ["?instance-expr" "also-has" "&rest"])
    (later ["every" "?instance-expr" "also-hasnt" "&rest"])
    (later ["?instance-expr" "also-hasnt" "&rest"])
    (later ["?instance-expr" "now-has" "&rest"])
    (entry ["?xs" "&&" "&rest"] #(unify-handler %1 %2 (symbol "&&")))
    (entry ["?x" "&" "&rest"] #(unify-handler %1 %2 (symbol "&")))
    (entry ["?xs" "===" "&rest"] #(unify-handler %1 %2 (symbol "===")))
    (entry ["?x" "==" "?y"] eq-handler)
    (entry ["?x" (symbol nil "/==") "?y"] neq-handler)
    (entry ["?xs" "&&!" "&rest"] #(unify-handler %1 %2 (symbol "&&!")))
    (entry ["?x" "&!" "&rest"] #(unify-handler %1 %2 (symbol "&!")))
    (entry ["?x" "&?" "?y"] #(test-handler %1 %2 false))
    (entry ["?x" "&+?" "?y"] #(test-handler %1 %2 true))
    (entry ["?x" "&+" "?y"] plus-handler)
    (entry ["?x" "&+!" "?y"] plus-eager-handler)
    (entry ["?x" "=" "?y"] (set-equal-handler false))
    (entry ["?x" "/=" "?y"] (set-equal-handler true))
    (later ["the" "?class" "?slot" "of" "?frameadd"])
    (entry ["in-theory" "?theory-expr"] in-theory-handler)
    (entry ["in-theory" "?theory-expr" "?km-expr"] in-theory-body-handler)
    (entry ["hide-theory" "?theory-expr"] hide-theory-handler)
    (entry ["see-theory" "?theory-expr"] see-theory-handler)
    (entry ["end-theory"] end-situation-handler)
    (entry ["visible-theories"] visible-theories-handler)
    (entry ["in-situation" "?situation-expr"] in-situation-handler)
    (entry ["in-situation" "?situation" ["the" "?slot" "of" "?frame"]] in-situation-fast-handler)
    (entry ["in-situation" "?situation-expr" "?km-expr"] in-situation-body-handler)
    (entry ["end-situation"] end-situation-handler)
    (entry ["global-situation"] end-situation-handler)
    (entry ["new-situation"] new-situation-handler)
    (entry ["do" "?action-expr"] do-handler)
    (entry ["do" "?action-expr" "?next-situation"] do-next-handler)
    (entry ["do-and-next" "?action-expr"] do-and-next-handler)
    (entry ["do-and-next" "?action-expr" "?next-situation"] do-and-next-at-handler)
    (entry ["try-do" "?action-expr"] try-do-handler)
    (entry ["try-do" "?action-expr" "?next-situation"] try-do-at-handler)
    (entry ["try-do-and-next" "?action-expr"] try-do-and-next-handler)
    (entry ["try-do-and-next" "?action-expr" "?next-situation"] try-do-and-next-at-handler)
    (entry ["do-concurrently" "?action-expr"] do-concurrently-handler)
    (entry ["do-concurrently" "?action-expr" "?next-situation"] do-concurrently-at-handler)
    (entry ["do-concurrently-and-next" "?action-expr"] do-concurrently-and-next-handler)
    (entry ["do-concurrently-and-next" "?action-expr" "?next-situation"] do-concurrently-and-next-at-handler)
    (later ["do-script" "?script"])
    (entry ["do-plan" "?plan-instance-expr"] do-plan-handler)
    (entry ["assert" "?triple-expr"] assert-handler)
    (later ["is-true" "?triple-expr"])
    (later ["all-true" "?triples-expr"])
    (later ["some-true" "?triples-expr"])
    (entry ["next-situation"] next-situation-handler)
    (entry ["curr-situation"] curr-situation-handler)
    (later ["ignore-result" "?expr"])
    (later ["ignore" "?expr"])
    (later ["in-every-situation" "?situation-class" "?expr"])
    (entry ["new-context"] new-context-handler)
    (later ["thelast" "?frame"])
    (entry ["every" "?frame"] every-frame-handler)
    (entry ["every" "?frame" "with" "&rest"] every-with-handler)
    (entry ["the" "?frame"] the-frame-handler)
    (entry ["the" "?frame" "with" "&rest"] the-with-handler)
    (entry ["the+" "?slot" "of" "?frameadd"] the-plus-slot-handler)
    (entry ["the+" "?class" "?slot" "of" "?frameadd"] the-plus-class-handler)
    (entry ["the+" "?frame"] the-plus-frame-handler)
    (entry ["the+" "?frame" "with" "&rest"] the-plus-with-handler)
    (entry ["a+" "&rest"] a-plus-handler)
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
    (entry ["?x" "is-subsumed-by" "?y"] subsumed-by-handler)
    (entry ["?x" "subsumes" "?y"] subsumes-handler)
    (entry ["?x" "is-covered-by" "?y"] covered-by-handler)
    (entry ["?x" "covers" "?y"] covers-handler)
    (entry ["?y" "isa" "?x"] isa-handler)
    (entry ["?x" "is" "?y"] is-handler)
    (entry ["?xs" "includes" "?y"] includes-handler)
    (entry ["?xs" "is-superset-of" "?ys"] superset-handler)
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
    (entry ["why"] why-command)
    (entry ["why" "?triple"] why-triple)
    (entry ["justify"] justify-command)
    (entry ["justify" "?triple"] justify-command)
    (entry ["get-justification"] get-justification-command)
    (entry ["get-justification" "?triple"] get-justification-command)
    (entry ["explanation" [:triple "?f0" "?s" "?v0"] "?explanations"] explanation-command)
    (later ["explained-by" "?instance" "?expr"])
    (later ["comment" "?comment-tag" "&rest"])
    (later ["show-comment" "?comment-tag"])
    (entry ["quote" "?expr"] quote-handler)
    (entry ["unquote" "?expr"] unquote-handler)
    (entry ["delete" "?km-expr"] delete-handler)
    (entry ["evaluate" "?expr"] evaluate-handler)
    (later ["exists" "?frame"])
    (later ["has-value" "?frame"])
    (later ["print" "?expr"])
    (later ["format" "?flag" "?string" "&rest"])
    (later ["km-format" "?flag" "?string" "&rest"])
    (entry ["andify" "?expr"] andify-command)
    (entry ["make-sentence" "?expr"] #(sentence-command %1 %2 true "."))
    (entry ["make-phrase" "?expr"] #(sentence-command %1 %2 false ""))
    (entry ["pluralize" "?expr"] pluralize-command)
    (entry ["spy" "?expr"] #(trace/spy-command %1 (first %2)))
    (entry ["spy"] (fn [state _] (trace/spy-command state nil)))
    (entry ["unspy"] (fn [state _] (trace/unspy-command state)))
    (entry ["profile" "?expr"] profile-handler)
    (entry ["profile-report"] (fn [state _] (profile-report-command state nil)))
    (entry ["profile-report" "?n"] #(profile-report-command %1 (first %2)))
    (entry ["taxonomy" "&rest"] taxonomy-command)
    (entry ["keeping-kb" "&rest"] keeping-kb-handler)
    (entry ["checkpoint"] (fn [state _]
                            (loadkb/checkpoint-command state (symbol "t"))))
    (entry ["checkpoint" "?checkpoint-id"] checkpoint-id-handler)
    (entry ["undo"] (fn [state _] (loadkb/undo-command state nil)))
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

(defn- record-later?
  "True when the explanation is recorded by a later writer, not here.

  A :set whose elements are not all atoms, and a unification, wait.
  The commented expression is the one tested."
  [kb expr]
  (and (frame/explanations-on? kb)
       (or (and (kb/km-set? expr)
                (boolean (some #(not (utils/lisp-atom? %))
                               (utils/elements (term/cdr expr)))))
           (and (term/cons? expr)
                (kb/unification-operator? (nth-value expr 1))))))

(defn- record-one-explanation
  [state target val expr]
  (let [recorded (frame/record-explanation-for (:kb state) target val expr)]
    (if (:program-error recorded)
      (report-set-explanation state recorded)
      (assoc state :kb (:kb recorded)))))

(defn- record-km1-result
  "Store an explanation for each answer when a target is known.

  The commented expression is the explanation. A rewrite is not
  recorded. An existential also records the value's instance-of when
  the answer is one value. A refusal is left as it is."
  [state expr commented rewrite?]
  (let [target (:target state)
        record? (and (some? target)
                     (not rewrite?)
                     (frame/explanations-on? (:kb state))
                     (not (record-later? (:kb state) commented)))
        state (if-not record?
                state
                (loop [vals (:value state)
                       state state]
                  (if (or (nil? vals) (not (term/cons? vals)))
                    state
                    (recur (term/cdr vals)
                           (record-one-explanation state target
                                                   (term/car vals)
                                                   commented)))))]
    (if (and (not rewrite?)
             (frame/explanations-on? (:kb state))
             (kb/existential? expr)
             (term/singleton? (:value state)))
      (record-one-explanation state
                              (term/km-list (symbol "the") (symbol "instance-of")
                                            (symbol "of") (term/car (:value state)))
                              (nth-value expr 1)
                              commented)
      state)))

(defn- trace-exit
  "The exit or fail line for one km1 result.

  Fail is only a nil answer of a boolean expression. Any other nil
  answer is an exit whose value prints as nil."
  [state expr commented target]
  (let [fail? (and (nil? (:value state)) (kb/km-boolean? expr))]
    (trace/km-trace state
                    (if fail? :fail :exit)
                    (cond
                      (and target fail?) "<- FAIL!~40T [~a, for ~a]"
                      fail? "<- FAIL!~40T [~a]"
                      target "<- ~a~40T [~a, for ~a]"
                      :else "<- ~a~40T [~a]")
                    (cond
                      (and target fail?) [commented target]
                      fail? [commented]
                      target [(:value state) commented target]
                      :else [(:value state) commented]))))

(defn- km1
  [state expr commented fail-mode target rewrite?]
  (let [state (-> state
                  (update-in [:query :depth] (fnil inc 0))
                  (update-in [:query :query-directed-inferences] (fnil inc 0))
                  (assoc :fail-mode fail-mode :target target :current-expr commented))
        state (stats/maybe-spot state)
        profile-key (explain/desource expr)
        state (stats/profile-call state profile-key)
        state (trace/km-trace state :call
                              (if (some? target)
                                "-> ~a~40T [for ~a]"
                                "-> ~a")
                              (if (some? target) [commented target] [commented]))
        dispatched (if (utils/lisp-atom? expr)
                     (assoc state :value (term/km-list expr))
                     (dispatch state expr))
        finished (if (refused? dispatched)
                   dispatched
                   (finish dispatched commented fail-mode))
        recorded (if (refused? finished)
                   finished
                   (record-km1-result finished expr commented rewrite?))
        recorded (stats/profile-exit recorded profile-key)
        recorded (trace-exit recorded expr commented target)]
    (update-in recorded [:query :depth] (fnil dec 0))))

(defn km-int
  "Evaluate one expression inside a query that is already running.

  fail-mode defaults to :fail when the caller does not pass one. That
  is the reasoning default, including when the top-level mode is :error.
  A refusal is returned unchanged. The goal is popped either way.
  Subsumption reads slots through this same function."
  [state expr & {:keys [fail-mode target check-for-looping rewrite?]
                 :or {check-for-looping true}}]
  (binding [subsumes/*km-int* km-int]
  (let [fail-mode (or fail-mode :fail)
        commented expr
        cleaned (strip-comments expr)
        state (-> state
                  (assoc :current-expr commented :fail-mode fail-mode :target target)
                  (note-constraints cleaned)
                  (trace/check-spy cleaned))]
    (or (command state cleaned fail-mode)
        (early state commented cleaned fail-mode check-for-looping)
        (let [pushed (stack/push-to-goal-stack (:kb state) (:query state) commented
                                               :target target)
              state (assoc state :kb (:kb pushed) :query (:query pushed))]
          (try
            (unpush (km1 state cleaned commented fail-mode target rewrite?))
            (catch Throwable thrown
              (unpush state)
              (throw thrown))))))))

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

  The query's goal stack, the instances being unified, the depth, the
  trace depth, and the looping flag are cleared first. The counters are
  cleared with them unless reset statistics is disabled. The object
  stack stays. fail-mode is the argument, or the mode stored on the
  query, or :fail. :value is the answer list. A form that is not ported
  yet has :error \"not-ported\" and no statistics line. A form that ran
  carries :statistics. While a prototype is open, this expression is
  recorded on it before it runs. The expression that opens the prototype
  is recorded by that command. reset-statistics? does this clear first.
  It is true when the caller does not pass it. checkpoint? records this
  expression on the undo log when logging is on, except for showme,
  undo, and why. A load passes both as false by calling km-int directly."
  [kb query expr & {:keys [fail-mode reset-statistics? checkpoint?]
                    :or {reset-statistics? true checkpoint? true}}]
  (let [prepared (if reset-statistics? (prepare-top kb query) {:kb kb :query query})
        kb (:kb prepared)
        query (:query prepared)
        fail-mode (or fail-mode (:top-level-fail-mode query) :fail)
        original expr
        kb (if (and checkpoint? (not (loadkb/skip-checkpoint? original)))
             (loadkb/set-checkpoint kb original)
             kb)
        expr (if (showme-head? original) original (frame/dereference kb original))
        kb (if-let [root (frame/curr-prototype kb)]
             (frame/add-definition kb root original)
             kb)
        state {:kb kb
               :query query
               :errors []
               :error-structures []
               :warnings []
               :fail-mode fail-mode}
        result (try
                 (km-int state expr :fail-mode fail-mode)
                 (catch clojure.lang.ExceptionInfo thrown
                   (if (errors/abort-exception? thrown)
                     (:state (ex-data thrown))
                     (throw thrown))))]
    (if (refused? result)
      result
      (let [answered (assoc (update result :value explain/desource)
                            :statistics (stats/report (:kb result) (:query result)))
            matched (match/minimatch original (pat ["the" "?slot" "of" "?frameadd"]))]
        (if (term/cons? matched)
          (assoc-in answered [:query :last-answer] (:value answered))
          answered)))))
