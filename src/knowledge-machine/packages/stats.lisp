
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: stats.lisp
;;; Author: Peter Clark
;;; Date: August 1994
;;; Purpose: Keep track and report various inference statistics

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defvar *reset-statistics-enabled* t)

(defun reset-statistics ()
  (cond (*reset-statistics-enabled*
          (setq *statistics-classification-inferences* 0)
          (setq *statistics-query-directed-inferences* 0)
          (setq *statistics-kb-access* 0)
          (setq *statistics-cpu-time* (get-internal-run-time))
          (setq *statistics-max-depth* 0)
          (setq *statistics-unifications* 0)
          (setq *statistics-skolems* 0)
          (setq *statistics-classifications-attempted* 0)
          (setq *statistics-classifications-succeeded* 0))))

;;; ----------

(defun report-statistics ()
  (let ( (cpu-time (- (get-internal-run-time) *statistics-cpu-time*))
	 (statistics-inferences (+ *statistics-classification-inferences* *statistics-query-directed-inferences*)) )
      (concat
       (format nil "(~a inferences and ~a KB accesses in ~,1F sec" statistics-inferences *statistics-kb-access*
	       (/ cpu-time internal-time-units-per-second))  ; itups = a system constant
       (cond ((not (= cpu-time 0))
	      (format nil " [~a lips, ~a kaps])"		; debugging only (history length ~a)"
		      (floor (/ (* internal-time-units-per-second  statistics-inferences) cpu-time))
		      (floor (/ (* internal-time-units-per-second  *statistics-kb-access*) cpu-time)))))
       (format nil ")~%"))))

(defun report-statistics-long ()
  (let ( (cpu-time (- (get-internal-run-time) *statistics-cpu-time*))
	 (statistics-inferences (+ *statistics-classification-inferences* *statistics-query-directed-inferences*)) )
      (concat
       (format nil "~a inferences (~a query-directed, ~a classification) and ~a KB accesses in ~,1F sec~%"
	       statistics-inferences *statistics-query-directed-inferences* *statistics-classification-inferences* *statistics-kb-access*
	       (/ cpu-time internal-time-units-per-second))  ; itups = a system constant
       (cond ((not (= cpu-time 0))
	      (format nil " (~a inferences per second, ~a KB accesses per second).~%"		; debugging only (history length ~a)"
		      (floor (/ (* internal-time-units-per-second  statistics-inferences) cpu-time))
		      (floor (/ (* internal-time-units-per-second  *statistics-kb-access*) cpu-time)))))
       (format nil "~a classifications attempted, of these ~a succeeded.~%"
	       *statistics-classifications-attempted* *statistics-classifications-succeeded*)
       (format nil "~a Skolem instances created, " *statistics-skolems*)
       (format nil "~a unifications, " *statistics-unifications*)
       (format nil "maximum depth of reasoning was depth ~a.~%" *statistics-max-depth*)
       )))

;;; ======================================================================
;;;		REPORTING INFERENCE SPEED
;;; Set *inference-report-frequency* to a number to have KM report its spot run-time speed
;;; ======================================================================

(defparameter *inference-report-frequency* nil)
(defvar *spot-runtime* 0)

(defun increment-inference-statistics ()
  (cond (*am-classifying* (setq *statistics-classification-inferences* (1+ *statistics-classification-inferences*)))
	(t (setq *statistics-query-directed-inferences* (1+ *statistics-query-directed-inferences*))))
  (cond ((and *inference-report-frequency*
	      (numberp *inference-report-frequency*)
	      (> *inference-report-frequency* 0))
	 (let ( (inferences (+ *statistics-classification-inferences* *statistics-query-directed-inferences*)) )
	   (multiple-value-bind
	    (number remainder)
	    (floor (/ inferences *inference-report-frequency*))
	    (declare (ignore number))
	    (cond ((= remainder 0)
		   (format t "~a logical inferences done (spot speed: ~a lips)~%"
			   inferences
			   (floor (/ (* *inference-report-frequency* internal-time-units-per-second)
				     (- (get-internal-run-time) *spot-runtime*))))
		   (setq *spot-runtime* (get-internal-run-time)))))))))

(defun inference-number () (+ *statistics-classification-inferences* *statistics-query-directed-inferences* 1))

;;; ======================================================================
;;;			PROFILING
;;; ======================================================================

(defvar *km-profile-start-cpu* (make-hash-table :test #'equal))
(defvar *km-profile-total-cpu* (make-hash-table :test #'equal))
(defvar *km-profile-total-entries* (make-hash-table :test #'equal))

(defun profile-call (kmexpr)
  (setf (gethash kmexpr *km-profile-start-cpu*) (get-internal-run-time)))

(defun profile-exit (kmexpr)
  (let* ((start-time (gethash kmexpr *km-profile-start-cpu*)))
    (cond ((not start-time) (report-error 'program-error
					  "Profiler: missing start-time when exiting call to ~a!~%" kmexpr))
	  (t (let ((cpu-time (- (get-internal-run-time) start-time))
		   (old-total-cpu-time (or (gethash kmexpr *km-profile-total-cpu*) 0))
		   (old-total-entries (or (gethash kmexpr *km-profile-total-entries*) 0)))
	       (setf (gethash kmexpr *km-profile-total-cpu*) (+ old-total-cpu-time cpu-time))
	       (setf (gethash kmexpr *km-profile-total-entries*) (1+ old-total-entries)))))))

(defun profile-reset ()
  (clrhash *km-profile-start-cpu*)
  (clrhash *km-profile-total-cpu*)
  (clrhash *km-profile-total-entries*))

(defun profile-report (&optional (n 100))
;  (km-format t "(hash-table-count *km-profile-start-cpu*) = ~a~%" (hash-table-count *km-profile-start-cpu*))
;  (km-format t "(hash-table-count *km-profile-total-cpu*) = ~a~%" (hash-table-count *km-profile-total-cpu*))
;  (km-format t "(hash-table-count *km-profile-total-entries*) = ~a~%" (hash-table-count *km-profile-total-entries*))
  (let ((exprs+cpus nil))
    (maphash #'(lambda (kmexpr cpu)
		 (push (list kmexpr cpu) exprs+cpus))
	     *km-profile-total-cpu*)
    (let ((exprs+cpus-srt (sort exprs+cpus #'> :key #'second)))
      (km-format t "CPU-TIME ~10t# CALLS~%")
      (mapc #'(lambda (expr+cpu)
		(let* ((expr (first expr+cpu))
		       (cpu (second expr+cpu))
		       (count (gethash expr *km-profile-total-entries*)))
		  (km-format t "~,2F ~10t~a ~20t~a~%"
			     (/ cpu internal-time-units-per-second) count expr)))
	    (first-n exprs+cpus-srt n))))
  t)

