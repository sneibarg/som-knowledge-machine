
(unless (find-package :km) (make-package :km :use '(:common-lisp)))
(in-package :km)

;;; File: loadme.lisp
;;; Purpose: load all the KM files, if you've disassembled the full KM
;;; into its constituent files.
;;; Usage: Uncomment and load this file to compile and load the individual KM
;;; files (assumed within the local directory)

;;; ****NOTE**** You DON'T need to uncomment this part of the code
;;; if you are simply working with the single file km.lisp.

#|
;;; compile-and-load function
(defun cload (file) (load (user::compile-file-if-needed file :print nil)))

(cload "header")
(cload "htextify")
(cload "case")
(cload "interpreter")
(cload "get-slotvals")
(cload "frame-io")
(cload "trace")
(cload "lazy-unify")
(cload "constraints")
(cload "explain")
(cload "kbutils")
(cload "stack")
(cload "stats")
(cload "sadl")
(cload "anglify")
(cload "writer")
(cload "taxonomy")
(cload "subsumes")
(cload "prototypes")
(cload "loadkb")
(cload "minimatch")
(cload "utils")
(cload "strings")
(cload "compiler")
(cload "compiled-handlers")
(cload "licence")
(cload "initkb")
|#
