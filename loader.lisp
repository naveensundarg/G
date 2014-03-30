
(defparameter *ql-modules*
  (list "cl-unification"))

;; (eval-when (:compile-toplevel :load-toplevel :execute)
;; (defvar *snark-loaded* nil)

;; (if (not *snark-loaded*)
;;   (let ((*package* *package*))
;;     (load (merge-pathnames
;;            "snark-20120808r009/snark-system"
;;            (or *load-pathname* *compile-file-pathname*)))
;;     ;; trying t(o MAKE-SNARK-SYSTEM when SNARK hasn't been compiled
;;     ;; produces an error.  This tries making the system within an
;;     ;; ignore errors, compiling it if the first attempt signals an
;;     ;; error, and then making the system.
;;     (multiple-value-bind (result condition)
;;         (ignore-errors (cl-user::make-snark-system))
;;       (declare (ignore result))
;;       (when (typep condition 'condition)
;;         (cl-user::make-snark-system t)
;;         (cl-user::make-snark-system))
;;       (setf *snark-loaded* t))))
;; ) ; (eval-when ...)


(mapcar #'ql:quickload *ql-modules*)


;; (defparameter *files*
;;   (list 
;;  ))


;; (defun compile-and-load (pathname)
;;   (multiple-value-bind (output-pathname warnings-p failure-p)
;;       (compile-file 
;;        (merge-pathnames 
;;         pathname (load-time-value *load-truename*)))
;;     (if failure-p
;;       (error "Error compiling file ~a." pathname)
;;       (load output-pathname))))


;; (map nil 'compile-and-load *files*)

