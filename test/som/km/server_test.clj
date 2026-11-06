(ns som.km.server-test
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.server :as server]))

(defn- body [text]
  (io/input-stream (.getBytes (str text) "UTF-8")))

(defn- parse [response]
  (json/read-str (:body response) :key-fn keyword))

(deftest port-text
  (is (= 8080 (server/parse-port nil)))
  (is (= 0 (server/parse-port "0")))
  (is (= 65535 (server/parse-port "65535")))
  (is (thrown? clojure.lang.ExceptionInfo (server/parse-port "nope")))
  (is (thrown? clojure.lang.ExceptionInfo (server/parse-port "70000"))))

(deftest status-route-matches-the-engine
  (let [response (server/handler {:request-method :get :uri "/status" :headers {}})]
    (is (= 200 (:status response)))
    (is (str/starts-with? (get-in response [:headers "Content-Type"]) "application/json"))
    (is (= (:km-version (engine/status)) (:km-version (parse response))))
    (is (= (set (:interfaces (engine/status))) (set (:interfaces (parse response)))))))

(deftest query-route-matches-the-engine
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain; charset=utf-8"}
                                  :body (body "  (a Cat)  ")})]
    (is (= 501 (:status response)))
    (is (= (engine/evaluate "  (a Cat)  ") (parse response)))))

(deftest blank-query-is-a-bad-request
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "  ")})]
    (is (= 400 (:status response)))
    (is (= "empty" (:error (parse response))))))

(deftest q-does-not-stop-the-service
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "q")})]
    (is (= 501 (:status response)))
    (is (= (engine/evaluate "q") (parse response)))))

(deftest json-is-not-a-query-body
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "application/json"}
                                  :body (body "{\"expr\":\"(a Cat)\"}")})]
    (is (= 415 (:status response)))
    (is (= "unsupported-media" (:error (parse response))))))

(deftest unknown-route
  (let [response (server/handler {:request-method :get :uri "/missing" :headers {}})]
    (is (= 404 (:status response)))
    (is (= "not-found" (:error (parse response))))))

(deftest index-names-the-two-routes
  (let [index (parse (server/handler {:request-method :get :uri "/" :headers {}}))]
    (is (= "GET /status" (get-in index [:routes :status])))
    (is (= "POST /query" (get-in index [:routes :query])))))

(deftest service-answers-over-http
  (let [http (server/start {:port 0})
        port (-> http .getAddress .getPort)
        base (str "http://127.0.0.1:" port)]
    (try
      (is (= "2.5.45"
             (:km-version (json/read-str (slurp (str base "/status")) :key-fn keyword))))
      (let [connection (.openConnection (java.net.URL. (str base "/query")))]
        (.setRequestMethod connection "POST")
        (.setDoOutput connection true)
        (.setRequestProperty connection "Content-Type" "text/plain; charset=utf-8")
        (with-open [out (.getOutputStream connection)]
          (.write out (.getBytes "(a Cat)" "UTF-8")))
        (is (= 501 (.getResponseCode connection)))
        (is (= (engine/evaluate "(a Cat)")
               (json/read-str (slurp (.getErrorStream connection)) :key-fn keyword))))
      (finally
        (server/stop http)))))
