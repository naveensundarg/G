
(defparameter *ql-modules*
  (list "cl-unification"))



(mapcar #'ql:quickload *ql-modules*)


(defparameter *files*
  (list
   "package"
   "propnd-base" "propnd" "propnd-tests"))

(defun compile-and-load (pathname)
  (multiple-value-bind (output-pathname warnings-p failure-p)
      (compile-file 
       (merge-pathnames 
        pathname (load-time-value *load-truename*)))
    (load output-pathname)))


(map nil 'compile-and-load *files*)


 