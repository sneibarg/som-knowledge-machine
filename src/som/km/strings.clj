(ns som.km.strings
  "String helpers used by the Knowledge Machine printer.

  These follow strings.lisp. The chunked concatenate workaround is not
  needed: Java strings do not share Lisp's apply argument limit.")

(defn explode
  "The characters of a string, in order."
  [text]
  (mapv identity (str text)))

(defn concat-list
  "Join strings in order."
  [parts]
  (let [out (StringBuilder.)]
    (doseq [part parts]
      (.append out part))
    (str out)))

(defn substitute-string
  "Replace each occurrence of old with new.

  When recursive? is true, the search continues through the replacement,
  matching substitute-string in strings.lisp. A replacement that still
  contains old does not finish."
  ([old new text]
   (substitute-string old new text false))
  ([old new text recursive?]
   (loop [remaining text
          parts []]
     (if-let [pos (clojure.string/index-of remaining old)]
       (let [before (subs remaining 0 pos)
             after (subs remaining (+ pos (count old)))]
         (if recursive?
           (recur (str new after) (conj parts before))
           (recur after (conj parts before new))))
       (concat-list (conj parts remaining))))))
