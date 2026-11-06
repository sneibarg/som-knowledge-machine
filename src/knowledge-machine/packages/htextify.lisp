
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: htextify.lisp
;;; Author: Peter Clark
;;; Purpose: Dummy function, to suppress compiler warning.
;;; This function is referenced but inaccessible in stand-alone KM.

(defun htextify (concept &optional concept-phrase &key action window)
  (declare (ignore concept concept-phrase action window)))



