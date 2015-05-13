(setq m31-comint-filters
      '((lambda (s)
          (replace-regexp-in-string "^ocd " "(ocd) " s))
        (lambda (s)
          (replace-regexp-in-string "(\\([^[:space:]]*\\))" "\\1" s))
        (lambda (s)
          ((lambda (s)
             (replace-regexp-in-string "(\\([^[:space:]]*\\))" "\\1" s))
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
  (ocamldebug (concat default-directory "andromeda.d.byte"))
  (mapc
   (lambda (f)
     (add-hook 'comint-preoutput-filter-functions f nil t))
   m31-comint-filters)
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-init\n")
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-current\n"))


(defun m31-send-current-statement nil
  (interactive)
  (save-excursion
    (comint-send-string
     (get-buffer-process (get-buffer "*andromeda*"))
     (concat
      (replace-regexp-in-string
       "\n" " "
       (buffer-substring-no-properties
        (1+ (search-backward "." 0)) (search-forward "." nil nil 2)))
      "
"))))

(defun m31-send-region nil
  (interactive)
  (save-excursion
    (comint-send-string
     (get-buffer-process (get-buffer "*andromeda*"))
     (concat
      (replace-regexp-in-string
       "\n" " "
       (buffer-substring-no-properties
        (region-beginning) (region-end)))
      "
"))))
;; (buffer-local-set-key (kbd "C-M-x") 'm31-send-current-statement)
