(ns som.km.stats
  "Inference counters and the profile table.

  The short report is the line the prompt prints after an answer. It is
  stored on the result as :statistics and is not appended to :text. A
  clock reading is not part of the contract of that line: a test checks
  the words, not the seconds. The frame store, unification, and
  prototypes update their own counters, so this namespace does not own
  those writes and does not require them."
  (:require [clojure.string :as str]
            [som.km.errors :as errors]
            [som.km.print :as print])
  (:import [java.util Locale]))

(defn reset-enabled?
  "True when a top-level query zeroes the counters.

  The flag starts true. While it is false, a top-level query still
  clears the stacks and the trace depth. It does not zero the counters
  and it does not move the clock start."
  [kb]
  (get-in kb [:runtime :reset-statistics-enabled?] true))

(defn- counter
  [query key]
  (or (get query key) 0))

(defn- inferences
  [query]
  (+ (counter query :classification-inferences)
     (counter query :query-directed-inferences)))

(defn- accesses
  [kb]
  (or (get-in kb [:runtime :kb-accesses]) 0))

(defn- elapsed-nanos
  "Nanoseconds since the counters were last zeroed.

  No stored start counts as no time, so the report stays the zero line."
  [query]
  (let [start (:statistics-cpu-start query)]
    (if (number? start)
      (max 0 (- (System/nanoTime) start))
      0)))

(defn- one-decimal
  [value]
  (String/format Locale/US "%.1f" (object-array [(double value)])))

(defn- two-decimals
  [value]
  (String/format Locale/US "%.2f" (object-array [(double value)])))

(defn- lips
  "How many count items fit in one second of nanos.

  A zero interval is 0, so the division is not attempted."
  [count nanos]
  (if (pos? nanos)
    (long (Math/floor (/ (* (double count) 1.0e9) (double nanos))))
    0))

(defn report
  "The one-line statistics sentence, including its closing newline.

  A zero interval prints \"in 0.0 sec)\" and stops. A positive interval
  adds the lips and kaps clause. That clause already ends with a
  parenthesis, and the sentence adds another. The extra parenthesis is
  the Lisp sentence."
  [kb query]
  (let [nanos (elapsed-nanos query)
        seconds (/ (double nanos) 1.0e9)
        prefix (str "(" (inferences query) " inferences and " (accesses kb)
                    " KB accesses in " (one-decimal seconds) " sec")]
    (str prefix
         (when (pos? nanos)
           (str " [" (lips (inferences query) nanos) " lips, "
                (lips (accesses kb) nanos) " kaps])"))
         ")\n")))

(defn report-long
  "The longer statistics text. No prompt command prints it.

  The classification lines count attempts and successes. A query with
  no definition and no slotted prototype leaves both at 0."
  [kb query]
  (let [nanos (elapsed-nanos query)
        seconds (/ (double nanos) 1.0e9)
        n (inferences query)]
    (str n " inferences ("
         (counter query :query-directed-inferences) " query-directed, "
         (counter query :classification-inferences) " classification) and "
         (accesses kb) " KB accesses in " (one-decimal seconds) " sec\n"
         (when (pos? nanos)
           (str " (" (lips n nanos) " inferences per second, "
                (lips (accesses kb) nanos) " KB accesses per second).\n"))
         (counter query :classifications-attempted)
         " classifications attempted, of these "
         (counter query :classifications-succeeded) " succeeded.\n"
         (counter query :skolems) " Skolem instances created, "
         (counter query :unifications)
         " unifications, maximum depth of reasoning was depth "
         (counter query :max-depth) ".\n")))

(defn maybe-spot
  "Append a spot-speed line every N inferences, when that frequency is set.

  The frequency starts unset, and then this records nothing. The line
  goes on :text. A zero interval prints 0 lips. The spot clock then
  moves to now."
  [state]
  (let [freq (get-in state [:kb :runtime :inference-report-frequency])
        n (inferences (:query state))]
    (if (and (number? freq) (pos? freq) (zero? (mod n freq)))
      (let [start (or (:spot-runtime (:query state))
                      (:statistics-cpu-start (:query state))
                      (System/nanoTime))
            elapsed (max 0 (- (System/nanoTime) (long start)))
            speed (if (pos? elapsed) (lips freq elapsed) 0)]
        (-> state
            (update :text #(str % n " logical inferences done (spot speed: "
                                speed " lips)\n"))
            (assoc-in [:query :spot-runtime] (System/nanoTime))))
      state)))

(defn profile-reset
  "Clear the profile tables on the knowledge base."
  [kb]
  (-> kb
      (assoc-in [:runtime :profile-cpu] {})
      (assoc-in [:runtime :profile-entries] {})
      (assoc-in [:runtime :profile-starts] {})))

(defn profile-call
  "Remember the start time of expr while profiling is on.

  The key is the expression the caller passes. The caller desources it
  once and uses that same value on the way out."
  [state expr]
  (if (get-in state [:query :profiling?])
    (assoc-in state [:kb :runtime :profile-starts expr] (System/nanoTime))
    state))

(defn profile-exit
  "Add the elapsed time of expr and count the call.

  A missing start records a program error and leaves the answer as it
  is. Profiling that is off does nothing."
  [state expr]
  (if-not (get-in state [:query :profiling?])
    state
    (let [start (get (get-in state [:kb :runtime :profile-starts] {}) expr)]
      (if-not (number? start)
        (errors/report-error state :program-error
                             "Profiler: missing start-time when exiting call to %s!"
                             (print/km-format expr))
        (let [elapsed (max 0 (- (System/nanoTime) (long start)))]
          (-> state
              (update-in [:kb :runtime :profile-cpu]
                         #(assoc (or % {}) expr (+ (get (or % {}) expr 0) elapsed)))
              (update-in [:kb :runtime :profile-entries]
                         #(assoc (or % {}) expr (inc (get (or % {}) expr 0))))))))))

(defn- pad-line
  [^StringBuilder sb column]
  (let [text (str sb)
        break (str/last-index-of text \newline)
        now (if (nil? break) (count text) (- (count text) break 1))
        target (if (< now column) column (inc now))]
    (dotimes [_ (- target now)]
      (.append sb \space))))

(defn profile-report-text
  "The profile table, slowest expression first.

  Ties use the printed expression, so the text does not depend on hash
  order. n is how many rows to keep. The header is always present. The
  seconds are not a stable value."
  [kb n]
  (let [cpu (get-in kb [:runtime :profile-cpu] {})
        entries (get-in kb [:runtime :profile-entries] {})
        rows (sort-by (fn [[expr nanos]]
                        [(- (long nanos)) (print/km-format expr)])
                      (seq cpu))
        shown (take (max 0 (long n)) rows)
        header (let [sb (StringBuilder. "CPU-TIME")]
                 (pad-line sb 10)
                 (.append sb "# CALLS")
                 (.append sb \newline)
                 (str sb))
        body (map (fn [[expr nanos]]
                    (let [sb (StringBuilder. (two-decimals (/ (double nanos) 1.0e9)))]
                      (pad-line sb 10)
                      (.append sb (str (get entries expr 0)))
                      (pad-line sb 20)
                      (.append sb (print/km-format expr))
                      (.append sb \newline)
                      (str sb)))
                  shown)]
    (apply str header body)))
