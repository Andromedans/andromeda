(require 'proof)

;; debugging facilities for the andromeda project
(setq m31-comint-filters
      '((lambda (s)
          (replace-regexp-in-string "^ocd " "(ocd) " s))
        (lambda (s)
          (replace-regexp-in-string "(\\([^)[:space:]]*\\))" "\\1" s))
        (lambda (s)
          ((lambda (s)
             (replace-regexp-in-string "(\\([^)[:space:]]*\\))" "\\1" s))
           s))
        (lambda (s)
          (replace-regexp-in-string "Tt.Ty \(Tt.Type\)" "Type" s))
        (lambda (s)
          (replace-regexp-in-string "Tt.Bound \\([0-9]+\\)" "\\1" s))
        (lambda (s)
          (replace-regexp-in-string "Name.Anonymous" "_" s))
        (lambda (s)
          (replace-regexp-in-string "Tt.Name " "" s))
        (lambda (s)
          (replace-regexp-in-string "Name.String \\(\"[^\"]+\"\\)" "\\1" s))
        (lambda (s)
          (replace-regexp-in-string ",[[:space:]]*<abstr>" "" s))))

(defun m31-ocamldebug nil
  (interactive)
  (ocamldebug
   (concat
    (locate-dominating-file
     buffer-file-name
     ".dir-locals.el") "andromeda.d.byte"))
  (mapc
   (lambda (f)
     (add-hook 'comint-preoutput-filter-functions f nil t))
   m31-comint-filters)
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-init\n")
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-current\n"))

;; the major mode for writing galactical type theory
;;;###autoload
(define-derived-mode andromeda-mode coq-mode "m31")
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.m31\\'" . andromeda-mode))

(defun m31-get-andromeda-buffer-create nil
  (get-buffer-create "*andromeda*"))

;;;###autoload
(defun m31-send-file (fn)
  (interactive)
  (let ((cmd
         (concat (locate-dominating-file
                  buffer-file-name
                  ".dir-locals.el") "andromeda.byte " fn))
        (compilation-buffer-name-function (lambda (mm) "*andromeda*"))
        (compilation-scroll-output 'first-error)
        (compilation-ask-about-save nil)
        (hist compile-history)
        (prev-cmd compile-command))
    (setq m31--current-buffer (current-buffer))
    (compile cmd)
    (setq compile-history hist
          compile-command prev-cmd)
    (with-current-buffer "*andromeda*"
      (set
       (make-local-variable
        'compilation-finish-functions)
       '((lambda (buf msg)
           (let ((c (get-buffer-window m31--current-buffer))
                 (w (get-buffer-window buf 'visible)))
             (when w
               (select-window w t)
               (when (eobp)
                 (recenter -1))
               (select-window c t)))))))))

;;;###autoload
(defun m31-send-buffer nil
  "Send the current buffer to Andromeda"
  (interactive)
  (m31-send-file buffer-file-name))

;;;###autoload
(defun m31-send-buffer-up-to-point nil
  (interactive)
  (m31-send-file
   (concat
    buffer-file-name ":"
    (int-to-string (line-number-at-pos)))))

(define-key andromeda-mode-map (kbd "C-c C-.") 'm31-send-buffer-up-to-point)
(define-key andromeda-mode-map (kbd "C-c .") 'm31-send-buffer-up-to-point)
(define-key andromeda-mode-map (kbd "C-c C-b") 'm31-send-buffer)
(define-key andromeda-mode-map (kbd "C-c C-l") 'm31-send-buffer)


(provide 'andromeda)
;;; andromeda.el ends here
