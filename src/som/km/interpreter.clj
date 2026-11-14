(ns som.km.interpreter
  "The Knowledge Machine interpreter.

  km and km-int share one dispatcher. The handler table is the Lisp
  alist in its original order, and the first match wins. A form this
  step does not run is still in that table, and it returns the
  not-ported refusal. Literals, arithmetic, comparisons, local assert
  and lookup, unification, constraint checks, subsumption, and the
  commands from the goal-stack step are evaluated. (the Class with ...)
  searches instances already stored. (the+ Class with ...) searches and
  then creates an instance when the search misses. (every Class has ...)
  stores a rule that a slot read inherits. (a-prototype Class) builds a
  prototype, and a later slot read clones it. (a Class) creates an
  anonymous instance. In prototype mode that instance is a participant.
  (every Class has-definition ...) stores a definition, and an instance
  is classified against it. (if ...) chooses a branch. allof, oneof,
  forall, and the sequence and bag forms walk a collection. called
  keeps the values that carry that tag. (the Class slot of frame)
  keeps the values of that class. An instance also-has, also-hasnt, and
  now-has edit that instance. (the1 ...), (theNth ...), append, and
  reverse read or build a sequence. (the-class Class) answers that
  description.
  (why) prints a stored
  explanation as a KM form, then the entry text and the exit text of a
  comment on that explanation. (justify) prints nothing for a leaf when
  developer-mode and justify-leaves are both off. developer-mode prints
  the KM rule. justify-leaves prints one English sentence and the
  classes it came from. A comment tag is walked before that leaf.
  (comment) and (show-comment) store and return comment text.
  (explain-all) and (clear-explanations) run. (get-justification)
  returns the same text. (make-sentence),
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
            [som.km.classify :as classify]
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

(declare km-int km-unique-int explain-all-command clear-explanations-command
         justify-one)

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

(defn- recover-loop
  "Evaluate a residue that is not the current goal, and store it.

  dont-cache-values on the slot leaves the stored expression in place.
  A refusal from the residue is returned as it is. A nil answer is
  stored. :errors from that evaluation stay on the result."
  [state handled]
  (if-not (contains? handled :evaluate)
    (use-result state handled)
    (let [base (assoc state
                      :kb (:kb handled)
                      :query (or (:query handled) (:query state)))
          evaluated (km-int base (:evaluate handled)
                            :fail-mode :fail
                            :check-for-looping true)]
      (if (refused? evaluated)
        evaluated
        (let [flag (frame/get-vals (:kb evaluated)
                                   (:slot handled)
                                   (symbol "dont-cache-values")
                                   :situation term/global-situation
                                   :dereference? false
                                   :query (:query evaluated))
              written (if (some? (:value flag))
                        flag
                        (frame/put-vals (:kb flag)
                                        (:instance handled)
                                        (:slot handled)
                                        (:value evaluated)
                                        :query (:query evaluated)))]
          (assoc evaluated
                 :kb (:kb written)
                 :query (or (:query written) (:query evaluated))
                 :value (:value evaluated)))))))

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
  zeroed only when reset statistics is enabled. Inverse installation
  is turned on with those counters. When reset statistics is disabled,
  the caller's inverse flag stays. Tracing is reset either way, so a
  trace left on comes back on. The object stack, the fail mode, a
  caller's depth limit, and a caller's :on-error stay. reset and a
  direct store do not come through here, so they leave the flag."
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
      {:kb (frame/set-installing-inverses (assoc-in kb [:runtime :kb-accesses] 0) true)
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

    (= name "explain-all")
    (explain-all-command state expr)

    (= name "clear-explanations")
    (clear-explanations-command state expr)

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

      ;; sometimes is a constraint, and its body is evaluated.
      (and (kb/constraint-expr? cleaned)
           (not (kb/retain-expr? cleaned))
           (not (kb/sometimes? cleaned)))
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
        (recover-loop traced handled))

      (too-deep? query)
      (let [traced (trace/km-trace state :comment
                                   "Maximum depth limit reached, doing ~a!"
                                   [cleaned])
            handled (stack/handle-looping (:kb traced) (:query traced) cleaned
                                          :reason :depth-limit-reached)]
        (recover-loop traced handled))

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

(defn- changed-slot-names
  "The slot names in slotsvals, or nil when that list is empty.

  Dropping instance-of leaves nil for a bare (a Class), so that
  creation does not classify."
  [slotsvals drop-instance-of?]
  (loop [pairs slotsvals
         acc []]
    (cond
      (or (nil? pairs) (not (term/cons? pairs)))
      (when (seq acc) (term/build-list acc nil))
      :else
      (let [slot (frame/slot-in (term/car pairs))]
        (recur (term/cdr pairs)
               (if (and drop-instance-of?
                        (utils/eql? slot (symbol "instance-of")))
                 acc
                 (conj acc slot)))))))

(defn- after-create
  "Classify a new instance, then keep the created name as the value.

  A refusal is returned as it is. A bare (a Class) passes no slot names."
  [state slotsvals]
  (cond
    (or (refused? state) (nil? (:value state))) state
    :else
    (let [instance (:value state)
          classed (classify/classify state instance km-int
                                     :slots-that-changed
                                     (changed-slot-names slotsvals true))]
      (if (refused? classed)
        classed
        (assoc classed :value instance)))))

(defn- a-handler
  "Create an anonymous instance of class.

  The name is a Skolem. Storing it puts that name on the object stack.
  In prototype mode the instance is a participant. A bare (a Class)
  does not classify. called is its own form."
  [state pieces]
  (listed (after-create (prototypes/create-instance state (first pieces) nil) nil)))

(defn- a-with-handler
  "Create an instance and store its slot pairs.

  In prototype mode the paths on the object stack are evaluated, which
  creates nested participants. Outside that mode a path stays stored
  until the slot is read."
  [state pieces]
  (let [[class slotsvals] pieces]
    (if (frame/curr-prototype (:kb state))
      (let [created (after-create (prototypes/create-instance state class slotsvals)
                                  slotsvals)]
        (cond
          (refused? created) created
          (nil? (:value created)) created
          :else (expand-prototype-paths created (:value created))))
      (let [[checked ok?] (slotsvals-ok? state slotsvals)]
        (if-not ok?
          checked
          (listed (after-create (prototypes/create-instance checked class slotsvals)
                                slotsvals)))))))

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

(defn- own-slots
  "Store own slot values. has, also-has, and now-has share this.

  combine is nil, appending, or overwriting. classify-all? is now-has:
  the Lisp calls classify with no slot list, so every definition is
  eligible. paths? evaluates paths while a prototype is open. The Lisp
  now-has leaves that call commented out."
  [head combine classify-all? paths?]
  (fn [state pieces]
    (let [[instance-expr slotsvals] pieces
          unique (km-unique-int state instance-expr :fail-mode :error)
          instance (:value unique)]
      (cond
        (refused? unique) unique
        (not (kb/kb-object? instance))
        (-> (report-error unique :user-error
                          "%s%n%s isn't/doesn't evaluate to a KB object name."
                          (print/km-format (term/build-list [instance-expr head] slotsvals))
                          (print/km-format instance-expr))
            (assoc :value nil))
        :else
        (let [[checked ok?] (slotsvals-ok? unique slotsvals)]
          (if-not ok?
            checked
            (try
              (let [stored (frame/add-slotsvals (:kb checked) instance
                                                (explain/convert-comments slotsvals)
                                                :combine-values-by combine
                                                :query (:query checked)
                                                :errors (:errors checked)
                                                :warnings (:warnings checked)
                                                :error-structures (:error-structures checked))]
                (if (refused? stored)
                  stored
                  (let [done (assoc checked
                                    :kb (frame/un-done (:kb stored) instance)
                                    :query (:query stored)
                                    :errors (vec (or (:errors stored) []))
                                    :warnings (vec (or (:warnings stored) []))
                                    :error-structures (vec (or (:error-structures stored) []))
                                    :value (term/km-list instance))
                        classed (if classify-all?
                                  (classify/classify done instance km-int)
                                  (classify/classify done instance km-int
                                                     :slots-that-changed
                                                     (changed-slot-names slotsvals false)))]
                    (cond
                      (refused? classed) classed
                      (and paths? (frame/curr-prototype (:kb classed)))
                      (expand-prototype-paths classed instance)
                      :else classed))))
              (catch clojure.lang.ExceptionInfo thrown
                (if (errors/abort-exception? thrown)
                  (throw thrown)
                  (-> (report-error checked :user-error "%s" (.getMessage thrown))
                      (assoc :value nil)))))))))))

(def ^:private has-handler
  (own-slots (symbol "has") nil false true))

(defn- every-also-hasnt
  "also-hasnt is refused on a class. The instance expression is not evaluated."
  [state pieces]
  (let [[instance-expr slotsvals] pieces]
    (-> (report-error state :user-error
                      "%s:%nCan't use also-hasnt with an \"every\" expression (can only use it with instances, not classes)"
                      (print/km-format
                       (term/build-list [(symbol "every") instance-expr (symbol "also-hasnt")]
                                        slotsvals)))
        (assoc :value nil))))

(defn- delete-values
  [state instance slot vals]
  (loop [vals vals
         current state]
    (cond
      (nil? vals) current
      (not (term/cons? vals))
      (throw (ex-info "This list is dotted." {:tail vals}))
      :else
      (let [gone (frame/delete-val (:kb current) instance slot (term/car vals)
                                   :query (:query current))]
        (recur (term/cdr vals)
               (assoc current :kb (:kb gone) :query (:query gone)))))))

(defn- delete-slots
  [state instance slotsvals]
  (loop [pairs slotsvals
         current state]
    (cond
      (nil? pairs)
      (assoc current
             :kb (frame/un-done (:kb current) instance)
             :value (term/km-list instance))
      (not (term/cons? pairs))
      (throw (ex-info "This list is dotted." {:tail pairs}))
      :else
      (let [pair (term/car pairs)]
        (recur (term/cdr pairs)
               (delete-values current instance (frame/slot-in pair) (frame/vals-in pair)))))))

(defn- also-hasnt-handler
  "Delete the named values. A missing value is left in place.

  The Lisp object-name error reprints also-has, not also-hasnt."
  [state pieces]
  (let [[instance-expr slotsvals] pieces
        unique (km-unique-int state instance-expr :fail-mode :error)
        instance (:value unique)]
    (cond
      (refused? unique) unique
      (not (kb/kb-object? instance))
      (-> (report-error unique :user-error
                        "%s%n%s isn't/doesn't evaluate to a KB object name."
                        (print/km-format
                         (term/build-list [instance-expr (symbol "also-has")] slotsvals))
                        (print/km-format instance-expr))
          (assoc :value nil))
      :else
      (let [[checked ok?] (slotsvals-ok? unique slotsvals)]
        (if-not ok?
          checked
          (try
            (delete-slots checked instance slotsvals)
            (catch clojure.lang.ExceptionInfo thrown
              (if (errors/abort-exception? thrown)
                (throw thrown)
                (-> (report-error checked :user-error "%s" (.getMessage thrown))
                    (assoc :value nil))))))))))

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

(defn- sometimes-handler
  "Evaluate the body.

  A stored sometimes reaches this handler when the slot's value list
  is read. While a constraint is being enforced, sometimes answers the
  symbol t and this handler is not used."
  [state pieces]
  (km-int state (first pieces)
          :fail-mode (:fail-mode state)
          :target (:target state)
          :rewrite? true))

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

(defn- flag-option
  "The boolean after a keyword whose name is key. A missing key is default.

  nil, the symbol nil, and f are false. A keyword or a symbol names the
  option. This is the same reading (explain-all) and (clear-explanations)
  use for their keywords."
  [expr key default]
  (loop [tail (when (term/cons? expr) (term/cdr expr))]
    (cond
      (or (nil? tail) (not (term/cons? tail))) default
      :else
      (let [head (term/car tail)
            name (cond
                   (keyword? head) (str/lower-case (name head))
                   (term/km-symbol? head) (str/lower-case (term/symbol-name head))
                   :else nil)
            rest (term/cdr tail)]
        (if (and (= name key) (term/cons? rest))
          (let [value (term/car rest)
                label (cond
                        (keyword? value) (str/lower-case (name value))
                        (term/km-symbol? value) (str/lower-case (term/symbol-name value))
                        :else nil)]
            (not (or (nil? value)
                     (false? value)
                     (contains? #{"nil" "f"} label))))
          (recur (cond
                   (and (some? name) (term/cons? rest)) (term/cdr rest)
                   (term/cons? tail) (term/cdr tail)
                   :else nil)))))))

(defn- all-concepts
  "Frame names after dereference, without user comments.

  A later copy of the same name is the one that stays. This is
  get-all-concepts."
  [kb]
  (utils/remove-duplicates
   (term/build-list
    (filterv kb/kb-object? (mapv #(frame/dereference kb %) (frame/objects kb)))
    nil)))

(defn- column-values
  "One column of explanation records, with the later duplicate kept."
  [records n]
  (loop [records records
         acc []]
    (if (or (nil? records) (not (term/cons? records)))
      (utils/remove-duplicates (term/build-list acc nil))
      (recur (term/cdr records) (conj acc (nth-value (term/car records) n))))))

(defn- records-for
  "Records whose slot and value match. The value test is eql."
  [records slot value]
  (loop [records records
         acc []]
    (if (or (nil? records) (not (term/cons? records)))
      (term/build-list acc nil)
      (let [record (term/car records)]
        (recur (term/cdr records)
               (if (and (utils/eql? (nth-value record 1) slot)
                        (utils/eql? (nth-value record 2) value))
                 (conj acc record)
                 acc))))))

(defn- explain-situation
  [state instance situation]
  (let [found (frame/explanation-records (:kb state) instance nil :situation situation)
        state (assoc state :kb (:kb found))
        records (:value found)
        slots (column-values records 1)]
    (loop [slots slots
           state state]
      (if (or (nil? slots) (not (term/cons? slots)))
        state
        (let [slot (term/car slots)
              slot-records (loop [pending records
                                  acc []]
                             (if (or (nil? pending) (not (term/cons? pending)))
                               (term/build-list acc nil)
                               (let [record (term/car pending)]
                                 (recur (term/cdr pending)
                                        (if (utils/eql? (nth-value record 1) slot)
                                          (conj acc record)
                                          acc)))))
              values (column-values slot-records 2)]
          (recur (term/cdr slots)
                 (loop [values values
                        state state]
                   (if (or (nil? values) (not (term/cons? values)))
                     state
                     (let [value (term/car values)
                           matched (records-for slot-records slot value)
                           rules (loop [pending matched
                                        acc []]
                                   (if (or (nil? pending) (not (term/cons? pending)))
                                     acc
                                     (recur (term/cdr pending)
                                            (conj acc (explain/build-rule
                                                       (nth-value (term/car pending) 3))))))]
                       (recur (term/cdr values)
                              (append-text
                               state
                               (str "\n(:triple " (print/km-format instance) " "
                                    (print/km-format slot) " "
                                    (print/km-format value) " [in "
                                    (print/km-format situation) "]) because:\n"
                                    (apply str (map #(str "   " (print/km-format %) "\n")
                                                    rules))))))))))))))

(defn- explain-all-command
  "Print every stored explanation. The answer is (t).

  include-globalp defaults to true. Theories are not walked. A global
  record is also printed while a local situation is walked, because the
  read includes both properties."
  [state expr]
  (let [include? (flag-option expr "include-globalp" true)
        places (let [all (vec (frame/situations (:kb state)))]
                 (if include?
                   all
                   (filterv #(not (utils/eql? % term/global-situation)) all)))
        concepts (all-concepts (:kb state))]
    (loop [concepts concepts
           state state]
      (if (or (nil? concepts) (not (term/cons? concepts)))
        (assoc state :value (term/km-list (symbol "t")))
        (let [instance (term/car concepts)]
          (recur (term/cdr concepts)
                 (reduce (fn [state situation]
                           (explain-situation state instance situation))
                         state
                         places)))))))

(defn- clear-explanations-command
  "Remove explanation records and answer (t).

  clear-globalp defaults to false, so *Global stays. A prototype is
  cleared along with every other frame."
  [state expr]
  (assoc state
         :kb (frame/clear-explanations (:kb state)
                                       :clear-global? (flag-option expr "clear-globalp" false))
         :value (term/km-list (symbol "t"))))

(defn- comment-command
  "Store the text of one comment tag. The answer is that text.

  A tag that is not a comment records the user error and answers nil.
  The printed form keeps the text as one element."
  [state pieces]
  (let [[tag data] pieces]
    (if-not (explain/comment-tag? tag)
      (-> (report-error state :user-error
                        "%s%n       Comment tag %s should be a symbol in square brackets, e.g. [Car1]!"
                        (print/km-format (term/km-list (symbol "comment") tag data))
                        (print/km-format tag))
          (assoc :value nil))
      (assoc state
             :kb (frame/store-comment (:kb state) tag data)
             :value data))))

(defn- show-comment-command
  "The text stored for one comment tag.

  A valid tag with nothing stored answers nil. A tag that is not a
  comment records the user error and answers nil."
  [state pieces]
  (let [tag (first pieces)]
    (if-not (explain/comment-tag? tag)
      (-> (report-error state :user-error
                        "%s%n       Comment tag %s should be a symbol in square brackets, e.g. [Car1]!"
                        (print/km-format (term/km-list (symbol "show-comment") tag))
                        (print/km-format tag))
          (assoc :value nil))
      (assoc state :value (frame/comment-data (:kb state) tag)))))

(defn- comment-columns
  "The exit texts and the entry texts of comment lists.

  The first element of a comment is the exit text. The second is the
  entry text. Nil elements are left out. This is the first two rows of
  transpose."
  [rows]
  (loop [rows rows
         exits []
         entries []]
    (if (or (nil? rows) (not (term/cons? rows)))
      {:exit (term/build-list exits nil)
       :entry (term/build-list entries nil)}
      (let [row (term/car rows)]
        (recur (term/cdr rows)
               (if (some? (when (term/cons? row) (term/car row)))
                 (conj exits (term/car row))
                 exits)
               (if (some? (nth-value row 1))
                 (conj entries (nth-value row 1))
                 entries))))))

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
               (let [sources (explain/sources explanation)
                     state (if (and (term/cons? sources) (term/cons? (term/cdr sources)))
                             (report-error state :nodebugger-error
                                           "get-comments: More than one source path %s (?). Just using first..."
                                           (print/km-format sources))
                             state)
                     tags (explain/comment-tags explanation)
                     columns (comment-columns
                              (term/build-list
                               (mapv #(frame/bound-comment (:kb state) %)
                                     (utils/elements tags))
                               nil))
                     rule (explain/desource-for-printing (explain/build-rule explanation))
                     state (if (some? (:entry columns))
                             (append-text state (str "   ENTRY TEXT: "
                                                     (print/km-format (:entry columns))
                                                     "\n"))
                             state)
                     state (if (some? (:exit columns))
                             (append-text state (str "   EXIT TEXT: "
                                                     (print/km-format (:exit columns))
                                                     "\n"))
                             state)]
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

(defn- spaces
  [n]
  (apply str (repeat (max 0 (or n 0)) \space)))

(defn- seen?
  [item coll]
  (boolean (some #(utils/equal? % item) coll)))

(defn- comma-text
  "commaify of class names, joined into one string."
  [classes]
  (loop [classes classes
         acc ""]
    (cond
      (or (nil? classes) (not (term/cons? classes))) acc
      (term/singleton? classes) (str acc (print/km-format (term/car classes)))
      :else (recur (term/cdr classes)
                   (str acc (print/km-format (term/car classes)) ", ")))))

(defn- intersects?
  [left right]
  (boolean (some #(utils/member? % right) (utils/elements left))))

(defn- specific-classes
  "immediate-classes, then the most specific of those."
  [state instance]
  (let [found (taxonomy/immediate-classes (:kb state) instance)
        removed (taxonomy/remove-subsumers (:kb found) (:value found))]
    {:state (assoc state :kb (:kb removed))
     :classes (:value removed)}))

(defn- classes-of-rules
  "The classes named by these rules, most specific first."
  [state rules]
  (loop [rules rules
         state state
         acc []]
    (cond
      (or (nil? rules) (not (term/cons? rules)))
      (let [removed (taxonomy/remove-subsumers (:kb state) (term/build-list acc nil))]
        {:state (assoc state :kb (:kb removed))
         :classes (:value removed)})
      :else
      (let [found (frame/originated-from-classes (:kb state) (term/car rules))]
        (if (:error found)
          {:state (report-error (assoc state :kb (:kb found))
                                :user-error "%s" (:error found))
           :classes nil}
          (recur (term/cdr rules)
                 (assoc state :kb (:kb found))
                 (into acc (utils/elements (:value found)))))))))

(defn- source-classes
  "Classes that explain instance slot value in that direction only.

  This is source-classes-for-triple. A prototype triple is not walked
  through in-prototype."
  [state instance slot value situation]
  (let [found (frame/explanations-for (:kb state) instance slot value :situation situation)
        explanations (loop [items (:value found)]
                       (cond
                         (or (nil? items) (not (term/cons? items))) nil
                         (utils/eql? (nth-value (term/car items) 1) slot)
                         (nth-value (term/car items) 3)
                         :else (recur (term/cdr items))))
        rules (loop [items explanations
                     acc []]
                (if (or (nil? items) (not (term/cons? items)))
                  (term/build-list acc nil)
                  (let [rule (explain/build-rule (term/car items))]
                    (recur (term/cdr items) (if (some? rule) (conj acc rule) acc)))))]
    (classes-of-rules (assoc state :kb (:kb found)) rules)))

(defn- subgoal-text
  [state triple situation tab]
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
        head (str "\n" (spaces tab) "subgoal " (print/km-format triple) ": Computed from:")]
    {:state (assoc state :kb (:kb found))
     :text (if (seq rules)
             (apply str head "\n"
                    (map #(str (spaces (+ tab 2)) (print/km-format %) "\n") rules))
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
  "One sentence for a leaf, with the classes the triple came from.

  The sentence names the side whose classes meet those source classes.
  Nothing stored on either side keeps the triple as it was asked."
  [state triple situation tab]
  (let [instance (kb/arg1 triple)
        slot (kb/arg2 triple)
        value (kb/arg3 triple)
        forward (source-classes state instance slot value situation)
        state (:state forward)
        inverse (frame/invert-slot (:kb state) slot)
        backward (source-classes state value inverse instance situation)
        state (:state backward)
        classes (utils/remove-duplicates
                 (utils/append-lists (term/km-list (:classes forward)
                                                   (:classes backward))))
        own (specific-classes state instance)
        other (specific-classes (:state own) value)
        state (:state other)
        instance-hit (intersects? (:classes own) classes)
        value-hit (intersects? (:classes other) classes)
        shown-instance (cond instance-hit instance value-hit value :else instance)
        shown-value (cond instance-hit value value-hit instance :else value)
        shown-slot (cond instance-hit slot value-hit inverse :else slot)
        phrased-instance (phrase-of state shown-instance)]
    (if (refused? (:state phrased-instance))
      {:state (:state phrased-instance) :text nil}
      (let [phrased-value (phrase-of (:state phrased-instance) shown-value)]
        {:state (:state phrased-value)
         :text (str (spaces tab)
                    "The " (print/km-format shown-slot)
                    " of " (:text phrased-instance)
                    " = " (:text phrased-value) "."
                    (if (some? classes)
                      (str " (from " (comma-text classes) ")")
                      ""))}))))

(defn- leaf-text
  "The line (justify) prints for one triple that has no comment tag.

  developer-mode prints the KM rule. justify-leaves, when that mode is
  off and the slot is not instance-of, prints one English sentence.
  Both flags off print nothing."
  [state triple situation tab]
  (let [developer? (get-in state [:kb :runtime :developer-mode?] false)
        justify? (get-in state [:kb :runtime :justify-leaves?] false)
        slot (kb/arg2 triple)]
    (cond
      developer? (subgoal-text state triple situation tab)
      (and justify? (not (utils/eql? slot (symbol "instance-of"))))
      (english-leaf state triple situation tab)
      :else {:state state :text nil})))

(defn- lines-for-triples
  [state triples situation depth & {:keys [done tab] :or {done [] tab 0}}]
  (if (> depth 20)
    {:state (append-text state
                         "(depth limit for justification reached...no further details below this)\n")
     :lines []}
    (let [batch (vec (utils/elements triples))
          done-now (into (vec done) batch)]
      (loop [triples triples
             seen []
             state state
             lines []]
        (cond
          (or (nil? triples) (not (term/cons? triples)))
          {:state state :lines lines}
          (or (seen? (term/car triples) seen)
              (seen? (term/car triples) done))
          (recur (term/cdr triples) seen state lines)
          :else
          (let [walked (justify-one state (term/car triples) situation tab done-now depth)]
            (if (refused? (:state walked))
              {:state (:state walked) :lines []}
              (recur (term/cdr triples)
                     (conj seen (term/car triples))
                     (:state walked)
                     (into lines (filterv some? (:lines walked)))))))))))

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

(def ^:private value1-symbol (symbol "Value1"))
(def ^:private value2-symbol (symbol "Value2"))
(def ^:private the-slot-symbol (symbol "TheSlot"))
(def ^:private the-subslot-symbol (symbol "TheSubslot"))
(def ^:private subslot-comment-tag (symbol "[subslot-reasoning]"))

(defn- subst-comment
  "Replace Value1, TheSlot, Value2, and TheSubslot.

  A binding of nil stays nil. A symbol inside quote is replaced too.
  This is sublis of those four symbols."
  [expr frame slot value subslot]
  (let [table {value1-symbol frame
               the-slot-symbol slot
               value2-symbol value
               the-subslot-symbol subslot}]
    (cond
      (and (term/km-symbol? expr) (contains? table expr)) (get table expr)
      (term/cons? expr)
      (term/cons-cell (subst-comment (term/car expr) frame slot value subslot)
                      (subst-comment (term/cdr expr) frame slot value subslot))
      :else expr)))

(defn- subslot-comment-body
  "The text of [subslot-reasoning], without the comment tag.

  Self is not replaced. Value1, TheSlot, Value2, and TheSubslot are
  replaced afterwards."
  []
  (term/km-list
   ""
   (term/km-list :seq
                 "The" the-subslot-symbol (symbol "of") value1-symbol
                 "=" value2-symbol ", and"
                 the-subslot-symbol "is a subslot of" the-slot-symbol)
   (term/km-list :triple value1-symbol the-subslot-symbol value2-symbol)))

(defn- comment-parts
  "The comment list for an internal tag. A user comment answers nil.

  [subslot-reasoning] uses the built-in text. Any other tag replaces
  Self with the tag's third element."
  [kb tag]
  (when (explain/internal-comment? tag)
    (if (utils/eql? (nth-value tag 1) subslot-comment-tag)
      (subslot-comment-body)
      (frame/bind-self (frame/comment-data kb (nth-value tag 1))
                       (nth-value tag 2)))))

(defn- comment-field
  "call, exit, or subgoals of one comment tag. This is get-comment2."
  [kb tag mode]
  (let [comments (comment-parts kb tag)]
    (case mode
      :call (nth-value comments 1)
      :exit (nth-value comments 0)
      :subgoals (nth-value comments 2))))

(defn- forward-explanations
  "Explanations stored for instance slot value in that direction only.

  This is the explanations list of get-explanations0. The inverse
  direction is a separate call."
  [state instance slot value situation]
  (let [found (frame/explanations-for (:kb state) instance slot value
                                      :situation situation)
        explanations (loop [items (:value found)]
                       (cond
                         (or (nil? items) (not (term/cons? items))) nil
                         (utils/eql? (nth-value (term/car items) 1) slot)
                         (nth-value (term/car items) 3)
                         :else (recur (term/cdr items))))]
    {:state (assoc state :kb (:kb found))
     :explanations explanations}))

(defn- because-line
  [state instance slot value tab]
  (let [left (phrase-of state instance)]
    (if (refused? (:state left))
      {:state (:state left) :text nil}
      (let [right (phrase-of (:state left) value)]
        {:state (:state right)
         :text (when-not (refused? (:state right))
                 (str (spaces tab)
                      "The " (print/km-format slot)
                      " of " (:text left)
                      " = " (:text right)
                      " because:"))}))))

(defn- phrase-line
  "make-phrase of one evaluated comment field, indented."
  [state expr tab extra]
  (let [ran (km-int state expr :fail-mode :fail)]
    (if (refused? ran)
      {:state ran :text nil}
      (let [phrased (phrase-of ran (:value ran))]
        {:state (:state phrased)
         :text (when-not (refused? (:state phrased))
                 (str (spaces tab) extra (:text phrased)))}))))

(defn- justify-computed
  "One subgoal. The depth check runs before the triple is expanded.

  A value that is not a triple records the user error and contributes
  no lines. This is get-justification0 for a comment subgoal."
  [state triple situation tab done depth]
  (cond
    (and (some? triple) (not (kb/km-triple? triple)))
    {:state (report-error state :user-error
                          "(justify %s): Argument should be a triple (justify (:triple <f> <s> <v>))!"
                          (print/km-format triple))
     :lines []}

    (> depth 20)
    {:state (append-text state
                         "(depth limit for justification reached...no further details below this)\n")
     :lines []}

    :else
    (let [computed (compute-triples state triple)]
      (if (refused? (:state computed))
        {:state (:state computed) :lines []}
        (lines-for-triples (:state computed)
                           (:triples computed)
                           situation
                           depth
                           :done done
                           :tab tab)))))

(defn- justify-subgoals
  "Walk the values of one subgoal expression.

  Nil is not evaluated, so a missing subgoal does not justify the
  previous answer. Each value is justified one step deeper."
  [state expr situation tab done depth]
  (if (nil? expr)
    {:state state :lines []}
    (let [ran (km-int state expr :fail-mode :fail)]
      (if (refused? ran)
        {:state ran :lines []}
        (loop [items (:value ran)
               state ran
               lines []]
          (cond
            (or (nil? items) (not (term/cons? items)))
            {:state state :lines lines}
            :else
            (let [step (justify-computed state (term/car items) situation
                                         (+ tab 2) done (inc depth))]
              (if (refused? (:state step))
                {:state (:state step) :lines []}
                (recur (term/cdr items)
                       (:state step)
                       (into lines (:lines step)))))))))))

(defn- justify-comment
  "The lines of one comment tag. This is get-comment-justification.

  developer-mode adds the entry and exit banners. The call text is the
  second element of the comment. The exit text is the first. Subgoals
  are the third. [subslot-reasoning] reads the built-in comment. The
  two extra spaces on an exit apply when the tag itself is that symbol."
  [state tag triple situation tab done depth]
  (let [frame (kb/arg1 triple)
        slot (kb/arg2 triple)
        value (kb/arg3 triple)
        subslot (nth-value tag 3)
        bind #(subst-comment % frame slot value subslot)
        caller (bind (comment-field (:kb state) tag :call))
        exiter (bind (comment-field (:kb state) tag :exit))
        subgoals (bind (comment-field (:kb state) tag :subgoals))
        developer? (get-in state [:kb :runtime :developer-mode?] false)
        shown (explain/desource-for-printing tag)
        banner (fn [label]
                 (str (spaces tab)
                      "(Doing triple: " (print/km-format triple) ")\n"
                      label " for " (print/km-format shown) ":"))
        ;; Live Lisp compares the whole tag with [subslot-reasoning].
        ;; A stored (comm [subslot-reasoning] ...) does not take the spaces.
        exit-pad (if (utils/eql? tag subslot-comment-tag) "  " "")
        entry (when developer? (banner "Entry text"))
        state (if (some? caller)
                (phrase-line state caller tab "")
                {:state state :text nil})]
    (if (refused? (:state state))
      {:state (:state state) :lines []}
      (let [call (:text state)
            walked (justify-subgoals (:state state) subgoals situation tab done depth)]
        (if (refused? (:state walked))
          {:state (:state walked) :lines []}
          (let [state (if (some? exiter)
                        (phrase-line (:state walked) exiter tab exit-pad)
                        {:state (:state walked) :text nil})]
            (if (refused? (:state state))
              {:state (:state state) :lines []}
              {:state (:state state)
               :lines (filterv some? (into [entry call] (conj (:lines walked)
                                                              (when developer? (banner "Exit text"))
                                                              (:text state))))})))))))

(defn- justify-direction
  "Comment tags for one direction of a triple.

  :lines is nil when this direction has no comment tag, so the other
  direction can run. A tag keeps the earlier copy. The because line is
  printed once, then each tag. This is get-justification2."
  [state instance slot value situation tab done depth]
  (let [found (forward-explanations state instance slot value situation)
        tags (utils/remove-duplicates
              (utils/mapcan-list explain/comment-tags-recursive (:explanations found))
              :test utils/equal?
              :from-end? true)]
    (if (nil? tags)
      {:state (:state found) :lines nil}
      (let [because (because-line (:state found) instance slot value tab)]
        (if (refused? (:state because))
          {:state (:state because) :lines []}
          (loop [tags tags
                 state (:state because)
                 lines [(:text because)]]
            (cond
              (or (nil? tags) (not (term/cons? tags)))
              {:state state :lines (filterv some? lines)}
              :else
              (let [triple (term/km-list :triple instance slot value)
                    walked (justify-comment state (term/car tags) triple
                                            situation tab done depth)]
                (if (refused? (:state walked))
                  {:state (:state walked) :lines []}
                  (recur (term/cdr tags)
                         (:state walked)
                         (into lines (:lines walked))))))))))))

(defn- justify-one
  "Comment tags forward, then inverse, then the leaf.

  A direction with a tag is the whole answer. Both flags off and no tag
  contribute no line. This is get-justification1."
  [state triple situation tab done depth]
  (let [instance (kb/arg1 triple)
        slot (kb/arg2 triple)
        value (kb/arg3 triple)
        forward (justify-direction state instance slot value situation tab done depth)]
    (if (some? (:lines forward))
      forward
      (let [inverse (frame/invert-slot (:kb (:state forward)) slot)
            backward (justify-direction (:state forward) value inverse instance
                                        situation tab done depth)]
        (if (some? (:lines backward))
          backward
          (let [leaf (leaf-text (:state backward) triple situation tab)]
            {:state (:state leaf)
             :lines (if (some? (:text leaf)) [(:text leaf)] [])}))))))

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
                                        :situation (frame/current-situation (:kb state)))]
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

(defn- pair-for
  "The (slot (values)) pair named slot, or nil."
  [slotsvals slot]
  (loop [pairs slotsvals]
    (cond
      (or (nil? pairs) (not (term/cons? pairs))) nil
      (utils/eql? slot (frame/slot-in (term/car pairs))) (term/car pairs)
      :else (recur (term/cdr pairs)))))

(defn- atomic-classes?
  "True when every parent is a knowledge-base object.

  An empty parent list is true, and the missing instance-of check
  then applies."
  [parents]
  (loop [parents parents]
    (cond
      (nil? parents) true
      (not (term/cons? parents)) false
      (kb/kb-object? (term/car parents)) (recur (term/cdr parents))
      :else false)))

(defn- every-reprint
  "The non-object error form. The instance form still starts with every."
  [expr word slotsvals]
  (term/build-list [(symbol "every") expr word] slotsvals))

(defn- definition-reprint
  [expr word slotsvals class-level?]
  (if class-level?
    (every-reprint expr word slotsvals)
    (term/build-list [expr word] slotsvals)))

(defn- prepared-definition
  "The slot pairs stored for a definition.

  A class definition keeps sources. An instance definition drops
  comments and sources, and instance-of keeps its list of classes."
  [frame slotsvals class-level?]
  (if class-level?
    (explain/convert-comments
     (explain/annotate-slotsvals slotsvals (explain/make-source frame)))
    (explain/desource-decomment slotsvals)))

(defn- definition-parents
  [slots0 class-level?]
  (let [values (frame/vals-in (pair-for slots0 (symbol "instance-of")))]
    (if class-level?
      (explain/desource-decomment values :delistify? false)
      values)))

(defn- undone-instances
  [state class]
  (let [found (taxonomy/all-instances (:kb state) class)]
    (loop [rest (:value found)
           kb (:kb found)]
      (if (or (nil? rest) (not (term/cons? rest)))
        (assoc state :kb kb)
        (recur (term/cdr rest) (frame/un-done kb (term/car rest)))))))

(defn- answer-frame
  [state frame]
  (assoc state :value (term/km-list frame)))

(defn- store-definition
  "Store or remove a definition, then classify an instance.

  now-has-definition deletes the previous definition first. An empty
  now-has-definition removes it and leaves the definitions flag as it
  is. A class definition does not classify the instances it names."
  [state frame original slots0 parents class-level? now?]
  (let [facet (if class-level?
                (symbol "member-definition")
                (symbol "own-definition"))
        state (if now?
                (classify/remove-definition state frame facet)
                state)]
    (if (nil? parents)
      (answer-frame state frame)
      (let [stored (frame/add-slotsvals (:kb state) frame slots0
                                        :facet facet
                                        :bind-self? true
                                        :query (:query state)
                                        :errors (:errors state)
                                        :warnings (:warnings state)
                                        :error-structures (:error-structures state))]
        (if (refused? stored)
          stored
          (let [pointed (classify/point-parents
                         (assoc state
                                :kb (:kb stored)
                                :query (:query stored)
                                :errors (vec (or (:errors stored) []))
                                :warnings (vec (or (:warnings stored) []))
                                :error-structures (vec (or (:error-structures stored) [])))
                         frame parents facet)
                flagged (update pointed :kb #(frame/set-are-some % :definitions true))
                cleared (if class-level?
                          (undone-instances flagged frame)
                          (assoc flagged :kb (frame/un-done (:kb flagged) frame)))
                answered (answer-frame cleared frame)]
            (if class-level?
              answered
              (let [classed (classify/classify answered frame km-int
                                               :slots-that-changed
                                               (changed-slot-names original false))]
                (if (refused? classed)
                  classed
                  (answer-frame classed frame))))))))))

(defn- definition-handler
  "has-definition and now-has-definition, for a class or one instance.

  class-level? selects the member definition. The instance form's
  non-object error still prints every."
  [word class-level?]
  (fn [state pieces]
    (let [[expr slotsvals] pieces
          unique (km-unique-int state expr :fail-mode :error)
          frame (:value unique)
          now? (utils/eql? word (symbol "now-has-definition"))]
      (cond
        (refused? unique) unique
        (not (kb/kb-object? frame))
        (-> (report-error unique :user-error
                          (if class-level?
                            "%s%n%s isn't/doesn't evaluate to a class name."
                            "%s%n%s isn't/doesn't evaluate to a KB object name.")
                          (print/km-format (every-reprint expr word slotsvals))
                          (print/km-format expr))
            (assoc :value nil))
        :else
        (let [[checked ok?] (slotsvals-ok? unique slotsvals)]
          (if-not ok?
            checked
            (try
              (let [slots0 (prepared-definition frame slotsvals class-level?)
                    parents (definition-parents slots0 class-level?)]
                (cond
                  (not (atomic-classes? parents))
                  (-> (report-error checked :user-error
                                    "%s%nThe `instance-of' slot-filler(s) in a %s must be atomic class name(s) only."
                                    (print/km-format (definition-reprint expr word slots0 class-level?))
                                    (term/symbol-name word))
                      (assoc :value nil))
                  (and (nil? parents)
                       (or (not now?) (some? slots0)))
                  (-> (report-error checked :user-error
                                    "%s%nYou must specify an `instance-of' slot value for a %s, pointing to the parent class(es)!"
                                    (print/km-format (definition-reprint expr word slots0 class-level?))
                                    (term/symbol-name word))
                      (assoc :value nil))
                  :else
                  (store-definition checked frame slotsvals slots0 parents
                                    class-level? now?)))
              (catch clojure.lang.ExceptionInfo thrown
                (if (errors/abort-exception? thrown)
                  (throw thrown)
                  (-> (report-error checked :user-error "%s" (.getMessage thrown))
                      (assoc :value nil)))))))))))

(defn- the-class-handler
  "Answer the description (the-class Class). It is not evaluated."
  [state pieces]
  (process-unquotes state
                    (term/km-list (term/km-list (symbol "the-class") (first pieces)))))

(defn- the-class-with-handler
  "Answer (the-class Class with slots). The slots are not evaluated."
  [state pieces]
  (let [[class slotsvals] pieces
        [checked ok?] (slotsvals-ok? state slotsvals)]
    (if-not ok?
      checked
      (process-unquotes checked
                        (term/km-list
                         (term/build-list [(symbol "the-class") class (symbol "with")]
                                          slotsvals))))))

(def ^:private it-symbol (symbol "It"))
(def ^:private it2-symbol (symbol "It2"))

(def ^:private drop-sentinel
  "The marker a failed sequence constraint leaves.

  The walk drops this symbol. A real value equal to the symbol
  to-remove is dropped with it."
  (symbol "to-remove"))

(defn- again
  "Evaluate expr again with the caller's fail mode, target, and rewrite."
  [state expr]
  (km-int state expr
          :fail-mode (:fail-mode state)
          :target (:target state)
          :rewrite? true))

(defn- false-test?
  "True when the whole answer is nil, the symbol f, or the symbol F.

  km-int of the atom f returns the list (f). That list is not the atom,
  so (if f then ... else ...) takes the then branch."
  [answer]
  (or (nil? answer)
      (utils/eql? answer (symbol "f"))
      (utils/eql? answer (symbol "F"))))

(defn- if-then-handler
  [state pieces]
  (let [[condition action] pieces]
    (again state (term/km-list (symbol "if") condition (symbol "then") action
                               (symbol "else") nil))))

(defn- if-else-handler
  [state pieces]
  (let [[condition action altaction] pieces
        fail-mode (:fail-mode state)
        tested (km-int state condition)]
    (cond
      (refused? tested) tested
      (false-test? (:value tested))
      (km-int tested altaction :fail-mode fail-mode)
      :else (km-int tested action :fail-mode fail-mode))))

(defn- demand-var
  "Nil when var is a KM variable. Otherwise the variable error.

  The sentence says Second argument. The printed expression is the
  whole form, including when the variable is the first argument."
  [state var expr]
  (when-not (kb/km-var? var)
    (-> (report-error state :user-error
                      "%s: Second argument should be a variable (e.g., ?x)!"
                      (print/km-format expr))
        (assoc :value nil))))

(defn- project-set
  "Append the value of each member that passes the constraint.

  Nil elements of those values are dropped. A refusal stops the walk."
  [state members var constraint value-expr]
  (loop [members members
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? members)
      (assoc state :value (term/build-list (filterv some? acc) nil))
      (not (term/cons? members))
      (throw (ex-info "This list is dotted." {:tail members}))
      :else
      (let [member (term/car members)
            tested (km-int state (subst-symbol member var constraint))]
        (cond
          (refused? tested) tested
          (nil? (:value tested))
          (recur (term/cdr members) tested acc)
          :else
          (let [produced (km-int tested (subst-symbol member var value-expr))]
            (if (refused? produced)
              produced
              (recur (term/cdr members)
                     produced
                     (into acc (utils/elements (:value produced)))))))))))

(defn- every-member
  "The first nil test answers nil. An empty collection answers (t).

  A refusal stops the walk."
  [state members var test]
  (loop [members members
         state state]
    (cond
      (refused? state) state
      (nil? members) (assoc state :value (term/km-list (symbol "t")))
      (not (term/cons? members))
      (throw (ex-info "This list is dotted." {:tail members}))
      :else
      (let [tested (km-int state (subst-symbol (term/car members) var test))]
        (cond
          (refused? tested) tested
          (nil? (:value tested)) (assoc tested :value nil)
          :else (recur (term/cdr members) tested))))))

(defn- first-where
  "The first member whose test is non-nil, as a one-element list.

  A miss answers nil. A refusal stops the walk."
  [state members var test]
  (loop [members members
         state state]
    (cond
      (refused? state) state
      (nil? members) (assoc state :value nil)
      (not (term/cons? members))
      (throw (ex-info "This list is dotted." {:tail members}))
      :else
      (let [member (term/car members)
            tested (km-int state (subst-symbol member var test))]
        (cond
          (refused? tested) tested
          (some? (:value tested)) (assoc tested :value (term/km-list member))
          :else (recur (term/cdr members) tested))))))

(defn- forall-body
  [state set constraint value var]
  (let [members (km-int state set)]
    (if (refused? members)
      members
      (project-set members (:value members) var constraint value))))

(defn- collection-shape?
  [values head]
  (and (term/singleton? values)
       (if (= head :seq)
         (kb/km-seq? (term/car values))
         (kb/km-bag? (term/car values)))))

(defn- project-elements
  "Map one sequence or bag.

  A sequence keeps a nil value and drops a failed constraint. A bag
  drops both. A refusal stops the walk."
  [state elements constraint value var sequence?]
  (loop [elements elements
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? elements)
      (assoc state :value
             (term/km-list
              (term/cons-cell (if sequence? :seq :bag)
                              (term/build-list
                               (if sequence?
                                 (filterv #(not (utils/eql? drop-sentinel %)) acc)
                                 (filterv some? acc))
                               nil))))
      (not (term/cons? elements))
      (throw (ex-info "This list is dotted." {:tail elements}))
      :else
      (let [member (term/car elements)
            tested (km-int state (subst-symbol member var constraint))]
        (cond
          (refused? tested) tested
          (nil? (:value tested))
          (recur (term/cdr elements)
                 tested
                 (if sequence? (conj acc drop-sentinel) acc))
          :else
          (let [produced (km-int tested (subst-symbol member var value))]
            (if (refused? produced)
              produced
              (let [one (kb/vals-to-val (:value produced))]
                (recur (term/cdr elements)
                       produced
                       (if (and (not sequence?) (nil? one))
                         acc
                         (conj acc one)))))))))))

(defn- project-collection
  "Project one sequence or bag.

  empty-ok? is the form without a variable: a null collection answers
  nil and records no error. A variable form has already been checked,
  and nil fails the single-sequence test. check-var? runs before the
  collection is evaluated."
  [state coll constraint value var head empty-ok? check-var? reprint]
  (if-let [bad (when check-var? (demand-var state var reprint))]
    bad
    (let [found (km-int state coll)]
      (cond
        (refused? found) found
        (and empty-ok? (nil? (:value found))) found
        (not (collection-shape? (:value found) head))
        (-> (report-error found :user-error
                          (if (= head :seq)
                            "%s: %s should evaluate to a single sequence (:seq ... ...)!"
                            "%s: %s should evaluate to a single bag (:bag ... ...)!")
                          (print/km-format reprint)
                          (print/km-format coll))
            (assoc :value nil))
        :else
        (project-elements found
                          (kb/seq-elements (term/car (:value found)))
                          constraint value var (= head :seq))))))

(defn- where-t
  "Insert where t before the last argument and evaluate again."
  [head]
  (fn [state pieces]
    (let [value (peek pieces)
          front (pop pieces)]
      (again state (term/build-list
                    (into [head]
                          (concat front [(symbol "where") (symbol "t") value]))
                    nil)))))

(defn- where-t-var
  "The ?var in form of where-t. A bad variable is reported first."
  [head]
  (fn [state pieces]
    (let [var (first pieces)
          rest (vec (rest pieces))
          expr (term/build-list (into [head var (symbol "in")] rest) nil)]
      (if-let [bad (demand-var state var expr)]
        bad
        (let [value (peek rest)
              front (pop rest)]
          (again state
                 (term/build-list
                  (into [head var (symbol "in")]
                        (concat front [(symbol "where") (symbol "t") value]))
                  nil)))))))

(defn- allof-where
  [quantifier referent]
  (fn [state pieces]
    (let [[set test] pieces]
      (again state (term/km-list quantifier set (symbol "where") test referent)))))

(defn- allof-must
  [referent]
  (fn [state pieces]
    (let [[set test] pieces
          members (km-int state set)]
      (if (refused? members)
        members
        (every-member members (:value members) referent test)))))

(defn- allof-where-must
  [head referent]
  (fn [state pieces]
    (let [[set test2 test] pieces
          filtered (km-int state (term/km-list head set (symbol "where") test2))]
      (if (refused? filtered)
        filtered
        (every-member filtered (:value filtered) referent test)))))

(defn- oneof-where
  [referent]
  (fn [state pieces]
    (let [[set test] pieces
          members (km-int state set)]
      (if (refused? members)
        members
        (first-where members (:value members) referent test)))))

(defn- theoneof-of
  [quantifier referent]
  (fn [state pieces]
    (let [[set test] pieces
          unique (km-unique-int state
                                (term/km-list quantifier set (symbol "where") test referent)
                                :fail-mode (:fail-mode state)
                                :target (:target state)
                                :rewrite? true)]
      (cond
        (refused? unique) unique
        (some? (:value unique))
        (assoc unique :value (term/km-list (:value unique)))
        :else unique))))

(defn- forall-where
  [referent]
  (fn [state pieces]
    (let [[set constraint value] pieces]
      (forall-body state set constraint value referent))))

(defn- seq-where
  [head referent]
  (fn [state pieces]
    (let [[seq constraint value] pieces]
      (project-collection state seq constraint value referent :seq true false
                          (term/km-list head seq (symbol "where") constraint value)))))

(defn- bag-where
  [head referent]
  (fn [state pieces]
    (let [[bag constraint value] pieces]
      (project-collection state bag constraint value referent :bag true false
                          (term/km-list head bag (symbol "where") constraint value)))))

(defn- allof-in-where
  [state pieces]
  (let [[var set test] pieces
        expr (term/km-list (symbol "allof") var (symbol "in") set (symbol "where") test)]
    (if-let [bad (demand-var state var expr)]
      bad
      (again state (term/km-list (symbol "forall") var (symbol "in") set
                                 (symbol "where") test var)))))

(defn- allof-must-in
  [state pieces]
  (let [[var set test] pieces
        expr (term/km-list (symbol "allof") var (symbol "in") set (symbol "must") test)]
    (if-let [bad (demand-var state var expr)]
      bad
      (let [members (km-int state set)]
        (if (refused? members)
          members
          (every-member members (:value members) var test))))))

(defn- allof-where-must-in
  [state pieces]
  (let [[var set test2 test] pieces
        expr (term/km-list (symbol "allof") var (symbol "in") set
                           (symbol "where") test2 (symbol "must") test)]
    (if-let [bad (demand-var state var expr)]
      bad
      (let [filtered (km-int state
                            (term/km-list (symbol "allof") var (symbol "in") set
                                          (symbol "where") test2))]
        (if (refused? filtered)
          filtered
          (every-member filtered (:value filtered) var test))))))

(defn- oneof-in
  [state pieces]
  (let [[var set test] pieces
        expr (term/km-list (symbol "oneof") var (symbol "in") set (symbol "where") test)]
    (if-let [bad (demand-var state var expr)]
      bad
      (let [members (km-int state set)]
        (if (refused? members)
          members
          (first-where members (:value members) var test))))))

(defn- theoneof-in
  [state pieces]
  (let [[var set test] pieces
        expr (term/km-list (symbol "theoneof") var (symbol "in") set
                           (symbol "where") test)]
    (if-let [bad (demand-var state var expr)]
      bad
      (let [unique (km-unique-int state
                                  (term/km-list (symbol "forall") var (symbol "in") set
                                                (symbol "where") test var)
                                  :fail-mode (:fail-mode state)
                                  :target (:target state)
                                  :rewrite? true)]
        (cond
          (refused? unique) unique
          (some? (:value unique))
          (assoc unique :value (term/km-list (:value unique)))
          :else unique)))))

(defn- forall-in-where
  [state pieces]
  (let [[var set constraint value] pieces
        expr (term/km-list (symbol "forall") var (symbol "in") set
                           (symbol "where") constraint value)]
    (if-let [bad (demand-var state var expr)]
      bad
      (forall-body state set constraint value var))))

(defn- seq-in-where
  [state pieces]
  (let [[var seq constraint value] pieces]
    (project-collection state seq constraint value var :seq false true
                        (term/km-list (symbol "forall-seq") var (symbol "in") seq
                                      (symbol "where") constraint value))))

(defn- bag-in-where
  [state pieces]
  (let [[var bag constraint value] pieces]
    (project-collection state bag constraint value var :bag false true
                        (term/km-list (symbol "forall-bag") var (symbol "in") bag
                                      (symbol "where") constraint value))))

(defn- tags-cover?
  "The state after both tag reads, and whether every tag is present.

  A refusal is that state alone. An empty tag list keeps the value.
  The slot reads still run."
  [state val tags]
  (let [called (km-int state (term/km-list (symbol "the") (symbol "called")
                                           (symbol "of") val))]
    (if (refused? called)
      called
      (let [named (:value called)
            unique (km-int called
                           (term/km-list (symbol "the") (symbol "uniquely-called")
                                         (symbol "of") val))]
        (if (refused? unique)
          unique
          [unique
           (loop [need tags]
             (cond
               (nil? need) true
               (not (term/cons? need)) false
               (utils/member? (term/car need) 
                              (utils/append-lists (term/km-list named (:value unique)))
                              utils/equal?)
               (recur (term/cdr need))
               :else false))])))))

(defn- keep-tagged
  [state vals tags]
  (loop [vals vals
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? vals) (assoc state :value (term/build-list acc nil))
      (not (term/cons? vals))
      (throw (ex-info "This list is dotted." {:tail vals}))
      :else
      (let [checked (tags-cover? state (term/car vals) tags)]
        (if (refused? checked)
          checked
          (let [[next keep?] checked]
            (recur (term/cdr vals)
                   next
                   (if keep? (conj acc (term/car vals)) acc))))))))

(defn- called-handler
  "Keep the values of expr that carry every tag.

  The expression uses the default fail mode. The mode captured here is
  used only when no value carries the tag, because a nested evaluation
  replaces :fail-mode on the state it returns."
  [state pieces]
  (let [[expr tag] pieces
        fail-mode (:fail-mode state)
        found (km-int state expr)]
    (if (refused? found)
      found
      (let [traced (if (some? (:value found))
                     (trace/km-trace found :comment
                                     "Now find just those value(s) whose tag = ~a..."
                                     [tag])
                     found)
            picked (keep-tagged traced (:value traced) (kb/val-to-vals tag))]
        (cond
          (refused? picked) picked
          (some? (:value picked)) picked
          (= fail-mode :error)
          (-> (report-error picked :user-error
                            "(%s called/uniquely-called %s): No values of %s (evaluates to %s) is called/uniquely-called %s!"
                            (print/km-format expr)
                            (print/km-format tag)
                            (print/km-format expr)
                            (print/km-format (:value found))
                            (print/km-format (kb/val-to-vals tag)))
              (assoc :value nil))
          :else (assoc picked :value nil))))))

(defn- uniquely-called-expr
  [state pieces]
  (let [[expr tag] pieces]
    (again state (term/km-list expr (symbol "called") tag))))

(defn- note-tags
  [state constraints?]
  (cond-> (update state :kb #(frame/set-are-some % :tags true))
    constraints? (update :kb #(frame/set-are-some % :constraints true))))

(defn- tag-error
  [state class slot tag slots]
  (let [expr (if (nil? slots)
               (term/km-list (symbol "a") class slot tag)
               (term/build-list [(symbol "a") class slot tag (symbol "with")] slots))
        spaces (if (nil? slots) "    " "   ")]
    (-> (report-error state :user-error
                      (str "%s%n" spaces "- The tag `%s' must be an atom or a constraint!")
                      (print/km-format expr)
                      (print/km-format tag))
        (assoc :value nil))))

(defn- create-tagged
  "Store the tag pair, classify, and list the new instance.

  Paths are evaluated only for a with form while a prototype is open."
  [state class slot tag slots paths?]
  (let [pair (term/km-list slot (kb/val-to-vals tag))
        slotsvals (term/cons-cell pair slots)
        created (after-create (prototypes/create-instance state class slotsvals)
                              slotsvals)]
    (cond
      (or (refused? created) (nil? (:value created))) created
      (and paths? (some? (frame/curr-prototype (:kb created))))
      (expand-prototype-paths created (:value created))
      :else (listed created))))

(defn- tagged-instance
  [state pieces constraints? with?]
  (let [class (first pieces)
        tag (second pieces)
        slots (when with? (nth pieces 2))
        slot (if constraints? (symbol "uniquely-called") (symbol "called"))
        noted (note-tags state constraints?)]
    (if-not (kb/km-tag? tag)
      (tag-error noted class slot tag (when with? slots))
      (if-not with?
        (create-tagged noted class slot tag nil false)
        (let [[checked ok?] (slotsvals-ok? noted slots)]
          (if-not ok?
            checked
            (create-tagged checked class slot tag slots true)))))))

(defn- in-class
  "Keep values whose class is target, in their original order.

  The symbol * keeps every value."
  [state values class]
  (if (or (nil? values) (utils/eql? class (symbol "*")))
    (assoc state :value values)
    (loop [values values
           state state
           acc []]
      (cond
        (nil? values) (assoc state :value (term/build-list acc nil))
        (not (term/cons? values))
        (throw (ex-info "This list is dotted." {:tail values}))
        :else
        (let [val (term/car values)
              under (taxonomy/isa? (:kb state) val class)]
          (recur (term/cdr values)
                 (assoc state :kb (:kb under))
                 (if (:value under) (conj acc val) acc)))))))

(defn- the-class-slot-handler
  [state pieces]
  (let [[class slot frameadd] pieces
        fail0 (:fail-mode state)
        target (:target state)]
    (cond
      (structured-slot? slot)
      (let [start (km-int state frameadd
                          :fail-mode fail0
                          :target target
                          :rewrite? true)]
        (if (refused? start)
          start
          (let [walked (multidepth start (:value start) slot)]
            (if (refused? walked)
              walked
              (in-class walked (:value walked) class)))))

      (kb/path? slot)
      (let [evaluated (km-unique-int state slot :fail-mode :error)]
        (if (refused? evaluated)
          evaluated
          (km-int evaluated
                  (term/km-list (symbol "the") class (:value evaluated)
                                (symbol "of") frameadd)
                  :fail-mode fail0
                  :target target
                  :rewrite? true)))

      :else
      (let [mode (if (contains? aggregation-slots slot) :fail fail0)
            read (km-int state
                         (term/km-list (symbol "the") slot (symbol "of") frameadd)
                         :fail-mode mode
                         :target target
                         :rewrite? true)]
        (if (refused? read)
          read
          (in-class read (:value read) class))))))

(defn- nth-cell
  "The element at index, counting from 0. A short list has none."
  [value index]
  (loop [value value
         index index]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? index) (term/car value)
      :else (recur (term/cdr value) (dec index)))))

(defn- list-length
  [value]
  (loop [value value
         n 0]
    (cond
      (nil? value) n
      (term/cons? value) (recur (term/cdr value) (inc n))
      :else (throw (ex-info "This list is dotted." {:tail value})))))

(defn- map-cells
  [values f]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      :else (recur (term/cdr values) (conj acc (f (term/car values)))))))

(defn- project-slot
  "Map pick over the values, then evaluate that collection.

  The read uses the caller's fail mode and target. The collected value
  uses the default fail mode."
  [pick]
  (fn [state pieces]
    (let [found (km-int state (first pieces)
                        :fail-mode (:fail-mode state)
                        :target (:target state)
                        :rewrite? true)]
      (if (refused? found)
        found
        (km-int found (kb/vals-to-val (map-cells (:value found) pick)))))))

(defn- positional
  "Rewrite (the1 slot of frame) to (the1 of (the slot of frame))."
  [head]
  (fn [state pieces]
    (let [[slot frameadd] pieces]
      (again state (term/km-list head (symbol "of")
                                 (term/km-list (symbol "the") slot
                                               (symbol "of") frameadd))))))

(defn- position-index
  "The positive integer, and the values of frameadd.

  A refusal from the integer stops the read. Any other integer failure
  still reads frameadd, then records the sentence. The sentence prints
  (the <expr> of <frame>), for both theN and theNth, and it says
  non-negative. 0 is rejected."
  [state nexpr frameadd]
  (let [indexed (km-unique-int state nexpr :fail-mode :error)]
    (if (refused? indexed)
      indexed
      (let [found (km-int indexed frameadd
                          :fail-mode (:fail-mode state)
                          :target (:target state)
                          :rewrite? true)
            n (:value indexed)]
        (cond
          (refused? found) found
          (and (integer? n) (>= n 1)) [found n]
          :else
          (-> (report-error found :user-error
                            "Doing %s. %s should evaluate to a non-negative integer!"
                            (print/km-format
                             (term/km-list (symbol "the") nexpr (symbol "of") frameadd))
                            (print/km-format nexpr))
              (assoc :value nil)))))))

(defn- the-n-handler
  "The nth argument of one structured value.

  the1, the2, and the3 take the argument whenever the value is
  structured. theN also requires n to be inside the list, counting the
  keyword. When that fails and n is 1, the whole value is kept."
  [state pieces]
  (let [[nexpr frameadd] pieces
        ready (position-index state nexpr frameadd)]
    (if-not (vector? ready)
      ready
      (let [[found n] ready]
        (km-int found
                (kb/vals-to-val
                 (map-cells (:value found)
                            (fn [value]
                              (cond
                                (and (term/structured-list? value)
                                     (< n (list-length value)))
                                (nth-cell value n)
                                (= n 1) value)))))))))

(defn- the-nth-handler
  "The nth value, counting from 1. A missing place answers nil."
  [state pieces]
  (let [[nexpr frameadd] pieces
        ready (position-index state nexpr frameadd)]
    (if-not (vector? ready)
      ready
      (let [[found n] ready
            vals (:value found)
            chosen (nth-cell vals (dec n))]
        (assoc found :value (when (and (<= n (list-length vals)) (some? chosen))
                              (term/km-list chosen)))))))

(defn- append-elements
  "The elements one side contributes, and the state after any error.

  A sequence or a bag contributes its elements. Nil contributes nothing.
  Any other KM term contributes itself. Anything else records the
  sentence and contributes nothing. The caller still builds a result."
  [state left right failing value]
  (cond
    (or (kb/km-seq? value) (kb/km-bag? value)) [state (kb/seq-elements value)]
    (nil? value) [state nil]
    (kb/is-km-term? value) [state (term/km-list value)]
    :else
    [(-> (report-error state :user-error
                       "(%s append %s): %s doesn't evaluate to an instance, sequence, or bag!"
                       (print/km-format left)
                       (print/km-format right)
                       (print/km-format failing))
         (assoc :value nil))
     nil]))

(defn- append-handler
  [state pieces]
  (let [[left right] pieces
        one (km-unique-int state left)]
    (if (refused? one)
      one
      (let [two (km-unique-int one right)]
        (if (refused? two)
          two
          (let [seq1 (:value one)
                seq2 (:value two)
                [taken1 elts1] (append-elements two left right left seq1)
                [taken2 elts2] (append-elements taken1 left right right seq2)
                mixed? (or (and (kb/km-seq? seq1) (kb/km-bag? seq2))
                           (and (kb/km-seq? seq2) (kb/km-bag? seq1)))
                noted (if mixed?
                        (-> (report-error taken2 :user-error
                                          "(%s append %s): Elements should be both sequences or both bags!"
                                          (print/km-format left)
                                          (print/km-format right))
                            (assoc :value nil))
                        taken2)
                head (cond
                       mixed? :seq
                       (or (kb/km-bag? seq1) (kb/km-bag? seq2)) :bag
                       :else :seq)]
            (assoc noted :value
                   (term/km-list
                    (term/cons-cell head
                                    (utils/append-lists (term/km-list elts1 elts2)))))))))))

(defn- reverse-handler
  [state pieces]
  (let [expr (first pieces)
        found (km-unique-int state expr
                             :fail-mode (:fail-mode state)
                             :target (:target state)
                             :rewrite? true)
        seq (:value found)]
    (cond
      (refused? found) found
      (nil? seq) (assoc found :value nil)
      (kb/km-seq? seq)
      (assoc found :value
             (term/km-list
              (term/cons-cell :seq
                              (term/build-list (reverse (utils/elements (term/cdr seq))) nil))))
      :else
      (-> (report-error found :user-error
                        "Attempting to reverse a non-sequence %s!%n[Sequences should be of the form (:seq <e1> ... <en>)]"
                        (print/km-format expr))
          (assoc :value nil)))))

(def ^:private handlers
  (into
   [(entry ["the" "?slot" "of" "?frameadd"] the-handler)
    (entry ["a" "?class"] a-handler)
    (entry ["a" "?class" "called" "?tag"] #(tagged-instance %1 %2 false false))
    (entry ["a" "?class" "uniquely-called" "?tag"] #(tagged-instance %1 %2 true false))
    (entry ["a" "?class" "with" "&rest"] a-with-handler)
    (entry ["a" "?class" "uniquely-called" "?tag" "with" "&rest"] #(tagged-instance %1 %2 true true))
    (entry ["a" "?class" "called" "?tag" "with" "&rest"] #(tagged-instance %1 %2 false true))
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
    (entry ["?instance-expr" "also-has" "&rest"]
           (own-slots (symbol "also-has") (symbol "appending") false true))
    (entry ["every" "?instance-expr" "also-hasnt" "&rest"] every-also-hasnt)
    (entry ["?instance-expr" "also-hasnt" "&rest"] also-hasnt-handler)
    (entry ["?instance-expr" "now-has" "&rest"]
           (own-slots (symbol "now-has") (symbol "overwriting") true false))
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
    (entry ["the" "?class" "?slot" "of" "?frameadd"] the-class-slot-handler)
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
    (entry ["every" "?cexpr" "has-definition" "&rest"]
           (definition-handler (symbol "has-definition") true))
    (entry ["every" "?cexpr" "now-has-definition" "&rest"]
           (definition-handler (symbol "now-has-definition") true))
    (entry ["?instance-expr" "has-definition" "&rest"]
           (definition-handler (symbol "has-definition") false))
    (entry ["?instance-expr" "now-has-definition" "&rest"]
           (definition-handler (symbol "now-has-definition") false))
    (entry ["if" "?condition" "then" "?action"] if-then-handler)
    (entry ["if" "?condition" "then" "?action" "else" "?altaction"] if-else-handler)
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
    (entry ["?seq-expr1" "append" "?seq-expr2"] append-handler)
    (entry ["?expr" "called" "?tag"] called-handler)
    (entry ["?expr" "uniquely-called" "?tag"] uniquely-called-expr)
    (entry ["allof" "?set" "where" "?test"] (allof-where (symbol "forall") it-symbol))
    (entry ["allof" "?set" "must" "?test"] (allof-must it-symbol))
    (entry ["allof" "?set" "where" "?test2" "must" "?test"] (allof-where-must (symbol "allof") it-symbol))
    (entry ["oneof" "?set" "where" "?test"] (oneof-where it-symbol))
    (entry ["theoneof" "?set" "where" "?test"] (theoneof-of (symbol "forall") it-symbol))
    (entry ["forall" "?set" "?value"] (where-t (symbol "forall")))
    (entry ["forall-seq" "?seq" "?value"] (where-t (symbol "forall-seq")))
    (entry ["forall-bag" "?bag" "?value"] (where-t (symbol "forall-bag")))
    (entry ["forall" "?set" "where" "?constraint" "?value"] (forall-where it-symbol))
    (entry ["forall-seq" "?seq" "where" "?constraint" "?value"] (seq-where (symbol "forall-seq") it-symbol))
    (entry ["forall-seq2" "?seq" "where" "?constraint" "?value"] (seq-where (symbol "forall-seq2") it2-symbol))
    (entry ["forall-bag" "?bag" "where" "?constraint" "?value"] (bag-where (symbol "forall-bag") it-symbol))
    (entry ["forall-bag2" "?bag" "where" "?constraint" "?value"] (bag-where (symbol "forall-bag2") it2-symbol))
    (entry ["allof2" "?set" "where" "?test"] (allof-where (symbol "forall2") it2-symbol))
    (entry ["allof2" "?set" "must" "?test"] (allof-must it2-symbol))
    (entry ["allof2" "?set" "where" "?test2" "must" "?test"] (allof-where-must (symbol "allof2") it2-symbol))
    (entry ["oneof2" "?set" "where" "?test"] (oneof-where it2-symbol))
    (entry ["forall2" "?set" "?value"] (where-t (symbol "forall2")))
    (entry ["forall-seq2" "?seq" "?value"] (where-t (symbol "forall-seq2")))
    (entry ["forall-bag2" "?bag" "?value"] (where-t (symbol "forall-bag2")))
    (entry ["theoneof2" "?set" "where" "?test"] (theoneof-of (symbol "forall2") it2-symbol))
    (entry ["forall2" "?set" "where" "?constraint" "?value"] (forall-where it2-symbol))
    (entry ["allof" "?var" "in" "?set" "where" "?test"] allof-in-where)
    (entry ["allof" "?var" "in" "?set" "must" "?test"] allof-must-in)
    (entry ["allof" "?var" "in" "?set" "where" "?test2" "must" "?test"] allof-where-must-in)
    (entry ["oneof" "?var" "in" "?set" "where" "?test"] oneof-in)
    (entry ["theoneof" "?var" "in" "?set" "where" "?test"] theoneof-in)
    (entry ["forall" "?var" "in" "?set" "?value"] (where-t-var (symbol "forall")))
    (entry ["forall-seq" "?var" "in" "?seq" "?value"] (where-t-var (symbol "forall-seq")))
    (entry ["forall-bag" "?var" "in" "?bag" "?value"] (where-t-var (symbol "forall-bag")))
    (entry ["forall" "?var" "in" "?set" "where" "?constraint" "?value"] forall-in-where)
    (entry ["forall-bag" "?var" "in" "?bag" "where" "?constraint" "?value"] bag-in-where)
    (entry ["forall-seq" "?var" "in" "?seq" "where" "?constraint" "?value"] seq-in-where)
    (entry ["function" "?lispcode"] function-handler)
    (entry ["the1" "?slot" "of" "?frameadd"] (positional (symbol "the1")))
    (entry ["the2" "?slot" "of" "?frameadd"] (positional (symbol "the2")))
    (entry ["the3" "?slot" "of" "?frameadd"] (positional (symbol "the3")))
    (entry ["the1" "of" "?frameadd"]
           (project-slot #(if (term/structured-list? %) (nth-cell % 1) %)))
    (entry ["the2" "of" "?frameadd"]
           (project-slot #(when (term/structured-list? %) (nth-cell % 2))))
    (entry ["the3" "of" "?frameadd"]
           (project-slot #(when (term/structured-list? %) (nth-cell % 3))))
    (entry ["theN" "?nexpr" "of" "?frameadd"] the-n-handler)
    (entry ["theNth" "?nexpr" "of" "?frameadd"] the-nth-handler)
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
    (entry ["the-class" "?class"] the-class-handler)
    (entry ["the-class" "?class" "with" "&rest"] the-class-with-handler)
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
    (entry ["comment" "?comment-tag" "&rest"] comment-command)
    (entry ["show-comment" "?comment-tag"] show-comment-command)
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
    (entry ["reverse" "?seq-expr"] reverse-handler)
    (entry [:default "?expr"] default-handler)
    (entry ["sometimes" "?expr"] sometimes-handler)
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
                  (update-in [:query (if (get-in state [:query :am-classifying])
                                     :classification-inferences
                                     :query-directed-inferences)]
                             (fnil inc 0))
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
