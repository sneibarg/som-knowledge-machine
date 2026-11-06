
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: sadl.lisp	(version 1.1)
;;; Author: Peter Clark
;;; Date: 2/23/01 updated 11/9/01 for direct incorporation into KM
;;;       Totally rewritten and simplified 4/2/02 to be in line with the new SADL spec.

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))	; So that the dispatch macro #$ is recognized

(defun do-plan (event-instance)
  (let* ( (first-subevent (km-unique-int `#$(the first-subevent of ,EVENT-INSTANCE))) )
    (cond ((null first-subevent)
	   (report-error 'user-error "do-plan: event ~a has no first-subevent, so I don't know where to start!"
			 event-instance))
	  (t (follow-event-chain first-subevent)))))

(defun follow-event-chain (event)
    (make-comment "Executing event ~a...~%" event)
    (km-int `#$(do-and-next ,EVENT) :fail-mode 'error)
    (let ( (next-event (next-event event)) )
      (cond ((null next-event)
	     (make-comment "No more next events: Finishing simulation.~%")
	     (list (curr-situation)))
	    (t (follow-event-chain next-event)))))

(defun next-event (event)
  (let ( (next-events (km-int `#$(the next-event of ,EVENT)))
	 (next-event-test (km-unique-int `#$(the next-event-test of ,EVENT))) )
    (cond
     ((and (not next-event-test)
	   (some #'km-argsp next-events))
      (report-error 'user-error "Missing a next-event-test on ~a!~%(It is needed to select the appropriate next-event from options: ~a)~%" event next-events))
     ((and next-event-test
	   (notevery #'km-argsp next-events))
      (report-error 'user-error "next-events for ~a should be a list of (:args <test-result> <next-event>) structures, as ~a has a next-event-test!~%(Was ~a instead)~%" event event next-events))
     ((and (not next-event-test)
	   (>= (length next-events) 2))
      (report-error 'user-error "Multiple next-events ~a specified for event ~a! (Don't know how to handle this)~%" event next-events))
     ((not next-event-test) (first next-events))
     (t 		; next-event-test necc. present
      (let* ( (test-result (km-unique-int `#$(evaluate ,NEXT-EVENT-TEST)))
	      (actual-next-events
	       (mapcar #'arg2of (remove-if-not #'(lambda (next-event)
						   (equal (arg1of next-event) test-result))
					       next-events))) )
;	(km-format t "next-events = ~a~%" next-events)
;	(km-format t "actual-next-events = ~a~%" actual-next-events)
	(cond ((singletonp actual-next-events) (first actual-next-events))
	      ((>= (length actual-next-events) 2)
	       (report-error 'user-error "~a has multiple next-events ~a specified for the result ~a (of test ~a)~%(Don't know how to handle this)~%" event actual-next-events test-result next-event-test))
	      (t (make-comment "(No next-event of ~a matches the result ~a (of test ~a)~%(next-events were ~a)~%Ending simulation...~%"
			       event test-result next-event-test next-events))))))))

