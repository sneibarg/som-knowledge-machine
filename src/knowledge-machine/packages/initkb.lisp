
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: initkb.lisp
;;; Author: Peter Clark
;;; Purpose: Initialize the KB (directive). This file is loaded last.

(reset-kb)

(defun version ()
  (format t "      ====================================================~%")
  (format t "      KM - THE KNOWLEDGE MACHINE - INFERENCE ENGINE v~a~%" *km-version-str*)
  (format t "      ====================================================~%")
  (format t "Copyright (C) 1994-~a Peter Clark and Bruce Porter. KM comes with ABSOLUTELY~%" *year*)
  (format t "NO WARRANTY. This is free software, and you are welcome to redistribute it~%")
  (format t "under certain conditions. Type (license) for details.~%~%")
  t)

(version)
(format t "Documentation at http://www.cs.utexas.edu/users/mfkb/km/~%")
(cond (*using-km-package*
       (format t "Type (in-package :km) then (km) for the KM interpreter prompt!~%"))
      (t (format t "Type (km) for the KM interpreter prompt!~%")))

; (hash-dollar)
