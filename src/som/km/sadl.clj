(ns som.km.sadl
  "The SADL event-chain walker.

  (do-plan instance) reads first-subevent, runs do-and-next, and follows
  next-event. The walk finishes in the situation it reached. It calls
  the situation step and the interpreter. It is not a second action
  language. km-int and km-unique-int are passed in."
  (:require [som.km.errors :as errors]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.term :as term]
            [som.km.trace :as trace]
            [som.km.utils :as utils]))

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- length-of
  [values]
  (loop [values values
         seen 0]
    (cond
      (nil? values) seen
      (term/cons? values) (recur (term/cdr values) (inc seen))
      :else seen)))

(defn- every-args?
  "True when every value is an :args list. An empty list is true."
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (kb/km-args? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- some-args?
  [values]
  (loop [values values]
    (cond
      (nil? values) false
      (not (term/cons? values)) false
      (kb/km-args? (term/car values)) true
      :else (recur (term/cdr values)))))

(defn- first-value
  [values]
  (when (term/cons? values) (term/car values)))

(defn- matching-events
  "The second element of each :args pair whose first element is result."
  [events result]
  (loop [events events
         acc []]
    (cond
      (nil? events) acc
      (not (term/cons? events)) acc
      (utils/equal? (kb/arg1 (term/car events)) result)
      (recur (term/cdr events) (conj acc (kb/arg2 (term/car events))))
      :else (recur (term/cdr events) acc))))

(defn- finish-nil
  "Record message and answer no next event.

  The caller treats that nil as the end of the simulation and still
  answers the current situation."
  [state template & args]
  (assoc (apply errors/report-error state :user-error template args) :value nil))

(defn- select-by-test
  [state event events test km-int km-unique-int]
  (let [tested (km-unique-int state (term/km-list (symbol "evaluate") test))]
    (if (refused? tested)
      tested
      (let [result (:value tested)
            chosen (matching-events events result)]
        (cond
          (= 1 (count chosen))
          (assoc tested :value (first chosen))

          (>= (count chosen) 2)
          (finish-nil tested
                      "%s has multiple next-events %s specified for the result %s (of test %s)%n(Don't know how to handle this)%n"
                      (print/km-format event)
                      (print/km-format (term/build-list chosen nil))
                      (print/km-format result)
                      (print/km-format test))

          :else
          (-> (trace/make-comment tested
                                  "(No next-event of ~a matches the result ~a (of test ~a)~%(next-events were ~a)~%Ending simulation...~%"
                                  [event result test events])
              (assoc :value nil)))))))

(defn- next-event
  "The event that follows event, or nil when the walk should stop.

  A user error also answers nil. The sentences match the Lisp,
  including the multiple-next-events sentence whose two values are
  printed in the opposite order from the English."
  [state event km-int km-unique-int]
  (let [found (km-int state (term/km-list (symbol "the") (symbol "next-event")
                                          (symbol "of") event))]
    (if (refused? found)
      found
      (let [events (:value found)
            tested (km-unique-int found
                                  (term/km-list (symbol "the") (symbol "next-event-test")
                                                (symbol "of") event))]
        (if (refused? tested)
          tested
          (let [test (:value tested)]
            (cond
              (and (nil? test) (some-args? events))
              (finish-nil tested
                          "Missing a next-event-test on %s!%n(It is needed to select the appropriate next-event from options: %s)%n"
                          (print/km-format event)
                          (print/km-format events))

              (and (some? test) (not (every-args? events)))
              (finish-nil tested
                          "next-events for %s should be a list of (:args <test-result> <next-event>) structures, as %s has a next-event-test!%n(Was %s instead)%n"
                          (print/km-format event)
                          (print/km-format event)
                          (print/km-format events))

              (and (nil? test) (>= (length-of events) 2))
              (finish-nil tested
                          "Multiple next-events %s specified for event %s! (Don't know how to handle this)%n"
                          (print/km-format event)
                          (print/km-format events))

              (nil? test)
              (assoc tested :value (first-value events))

              :else
              (select-by-test tested event events test km-int km-unique-int))))))))

(defn- follow-event-chain
  [state event km-int km-unique-int]
  (loop [state state
         event event]
    (let [state (trace/make-comment state "Executing event ~a...~%" [event])
          done (km-int state
                       (term/km-list (symbol "do-and-next") event)
                       :fail-mode :error)]
      (if (refused? done)
        done
        (let [nxt (next-event done event km-int km-unique-int)]
          (cond
            (refused? nxt) nxt
            (nil? (:value nxt))
            (-> (trace/make-comment nxt "No more next events: Finishing simulation.~%" [])
                (assoc :value (term/km-list (frame/current-situation (:kb nxt)))))
            :else (recur nxt (:value nxt))))))))

(defn do-plan
  "Walk the subevents of event and answer the situation the walk finished in.

  No first-subevent records the Lisp sentence and answers nil. A
  not-ported action stops the walk and returns that refusal. The walk
  has to start inside a situation: do-and-next in *Global answers nil."
  [state event km-int km-unique-int]
  (let [first-sub (km-unique-int state
                                 (term/km-list (symbol "the") (symbol "first-subevent")
                                               (symbol "of") event))]
    (cond
      (refused? first-sub) first-sub
      (nil? (:value first-sub))
      (assoc (errors/report-error first-sub :user-error
                                   "do-plan: event %s has no first-subevent, so I don't know where to start!"
                                   (print/km-format event))
             :value nil)
      :else (follow-event-chain first-sub (:value first-sub) km-int km-unique-int))))
