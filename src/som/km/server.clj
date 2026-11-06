(ns som.km.server
  "The HTTP service.

  GET /status reports the same build facts as the prompt banner.
  POST /query submits the request body as Knowledge Machine text to the
  same engine function the prompt uses. The service holds no knowledge
  of its own. q in a request body is an expression, not a shutdown.

  The socket is the JDK HTTP server. The handler function is ordinary
  Clojure data, so a later step can put another server in front of it."
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [som.km.engine :as engine])
  (:import [com.sun.net.httpserver HttpExchange HttpHandler HttpServer]
           [java.net InetSocketAddress])
  (:gen-class))

(def default-port 8080)

(def ^:private listen-host "127.0.0.1")

(def ^:private error-http-status
  {"empty" 400
   "not-ported" 501
   "unsupported-media" 415})

(defn parse-port
  "Return a TCP port. Nil selects port 8080. Any other value must be a
  whole number from 0 through 65535."
  [text]
  (if (nil? text)
    default-port
    (try
      (let [port (Long/parseLong text)]
        (if (<= 0 port 65535)
          port
          (throw (ex-info (str "PORT must be a number from 0 through 65535. Was: " text) {}))))
      (catch NumberFormatException _
        (throw (ex-info (str "PORT must be a number from 0 through 65535. Was: " text) {}))))))

(defn- json-response [status body]
  {:status status
   :headers {"Content-Type" "application/json; charset=utf-8"}
   :body (json/write-str body)})

(defn- http-status [result]
  (if (:ok result)
    200
    (get error-http-status (:error result) 500)))

(defn- plain-text-body?
  "True when the client sent plain text, or named no content type."
  [request]
  (let [content-type (some-> (get-in request [:headers "content-type"]) str/trim str/lower-case)]
    (or (str/blank? content-type)
        (str/starts-with? content-type "text/plain"))))

(defn- read-body [request]
  (some-> (:body request) slurp))

(defn- query-response [request]
  (if (plain-text-body? request)
    (let [result (engine/evaluate (read-body request))]
      (json-response (http-status result) result))
    (json-response
     415
     {:ok false
      :error "unsupported-media"
      :message "POST /query takes the Knowledge Machine expression as plain text. Use Content-Type: text/plain."})))

(defn handler
  "Handle one request map and return a response map.
  :request-method is a keyword, :uri is a path, :headers is a lower-case
  string map, and :body is a stream or nil."
  [request]
  (case [(:request-method request) (:uri request)]
    [:get "/"]
    (json-response
     200
     {:name "som-knowledge-machine"
      :message "Knowledge Machine service. GET /status reports the build. POST /query takes one expression as plain text."
      :routes {:status "GET /status"
               :query "POST /query"}})

    [:get "/status"]
    (json-response 200 (engine/status))

    [:post "/query"]
    (query-response request)

    (json-response
     404
     {:ok false
      :error "not-found"
      :message "No route matches this request."})))

(defn- exchange->request [^HttpExchange exchange]
  {:request-method (-> exchange .getRequestMethod str/lower-case keyword)
   :uri (-> exchange .getRequestURI .getPath)
   :headers {"content-type" (some-> exchange .getRequestHeaders (.getFirst "Content-Type"))}
   :body (.getRequestBody exchange)})

(defn- write-exchange [^HttpExchange exchange response]
  (let [body (str (:body response))
        bytes (.getBytes body "UTF-8")
        headers (.getResponseHeaders exchange)]
    (doseq [[name value] (:headers response)]
      (.set headers (str name) (str value)))
    (.sendResponseHeaders exchange (int (:status response)) (alength bytes))
    (with-open [out (.getResponseBody exchange)]
      (.write out bytes))))

(defn- on-exchange [^HttpExchange exchange]
  (try
    (write-exchange exchange (handler (exchange->request exchange)))
    (catch Throwable thrown
      (.printStackTrace thrown)
      (try
        (write-exchange
         exchange
         (json-response 500 {:ok false
                             :error "internal"
                             :message "The service failed while handling the request."}))
        (catch Throwable _)))
    (finally
      (.close exchange))))

(defn start
  "Start the HTTP service and return the running server.
  :port defaults to 8080. Port 0 asks the operating system for a free port.
  The service listens on 127.0.0.1."
  [{:keys [port] :or {port default-port}}]
  (let [server (HttpServer/create (InetSocketAddress. listen-host (int port)) 0)]
    (.createContext server "/"
                    (reify HttpHandler
                      (handle [_ exchange]
                        (on-exchange exchange))))
    (.start server)
    server))

(defn stop
  "Stop a server returned by start."
  [^HttpServer server]
  (.stop server 0))

(defn -main
  "Listen for HTTP requests. PORT selects the port, and defaults to 8080."
  [& _]
  (try
    (let [port (parse-port (System/getenv "PORT"))
          server (start {:port port})]
      (.addShutdownHook (Runtime/getRuntime)
                        (Thread. #(stop server)))
      (println (str "Knowledge Machine service listening on http://" listen-host ":" port))
      (println "GET /status")
      (println "POST /query")
      (flush)
      @(promise))
    (catch clojure.lang.ExceptionInfo e
      (println (.getMessage e))
      (System/exit 1))))
