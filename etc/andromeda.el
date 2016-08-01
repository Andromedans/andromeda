(defgroup m31 nil "Editing Andromeda code." :prefix 'm31-
  :group 'languages)


;;; Syntax highlighting
(defvar m31-symbolchars '("!" "$" "%" "&" "*" "+" "-" "." "/" ":" "<" "=" ">" "?" "@" "^" "|" "~"))
(defvar m31-prefixop '("~" "?" "!"))
(defvar m31-infixop '("=" "<" ">" "|" "&" "$" "@" "^" "+" "-" "*" "/" "%" "**"))

(defvar m31-anonymous "_")

(defvar m31-operation-rx "operation")

(defface m31-operation-face '((t (:inherit font-lock-function-name-face)))
  "" :group 'm31)

(defvar m31-cases-keywords
  '("mltype" "operation"
    "handle" "handler"
    "match" "|" "with"
    "val" "finally"
    "end"
    "yield"))

(defface m31-cases-face '((t (:inherit font-lock-keyword-face)))
  "" :group 'm31)

(defvar m31-mltype-rx "mltype")
(defface m31-mltype-face '((t (:inherit m31-cases-face)))
  "" :group 'm31)
;; swap with constant / tt ?

(defvar m31-meta-binder-begin-rx
  (rx symbol-start                               ;FIXME: should be symbol \_< not \<
      (|
       ;; "and"  ; problematic because we use it in mltype declarations
       "dynamic" "now"
       (seq "let" (? (+ space) "rec")))
      symbol-end))

(defface m31-meta-binder-begin-face '((t (:inherit font-lock-preprocessor-face)))
  "" :group 'm31)

(defvar m31-meta-variable-rx
  (eval
   `(rx
     (|
      ;; "::"
      (sequence "(" (* space)
                (* (any ,(mapconcat (lambda (c) c) m31-symbolchars "")))
                (* space) ")")
      (sequence (| (syntax word) "_") (* (| (syntax word) (syntax symbol))))))))
(defface m31-meta-variable-face '((t (:inherit font-lock-function-name-face)))
  "" :group 'm31)

(defvar m31-meta-binder-end-keywords
  '("in"
    "="
    "=>" "⇒" "⟹"))
(defface m31-meta-binder-end-face '((t (:inherit m31-meta-binder-begin-face)))
  "" :group 'm31)

(defvar m31-topdirective-keywords '("do" "fail"))
(defface m31-topdirective-face '((t (:inherit font-lock-keyword-face)))
  "" :group 'm31)

(defvar m31-meta-keywords
  '(
    ;; "judgement"
    ;; "judgment"
    ;; "_"
    "external"
    "#include_once"
    "ref" "!" ":="
    ;;    ";" ","
    ))
(defface m31-meta-face '((t (:inherit font-lock-constant-face)))
  "" :group 'm31)

(defvar m31-tt-keywords
  '("==" "≡"
    "Type"
    "beta_step"
    "congr_apply" "congr_eq" "congr_lambda" "congr_prod" "congr_refl"
    "context"
    "natural"
    "occurs"
    "where"                        ;could be a destructor
    "refl"
    "|-" "⊢"))
(defface m31-tt-face '((t (:inherit font-lock-type-face)))
  "" :group 'm31)

(defvar m31-tt-atom-keywords
  '("assume" "constant"))
(defface m31-tt-atom-face '((t (:inherit font-lock-type-face)))
  "" :group 'm31)

(defvar m31-tt-binder-begin-rx (rx bow (| "forall" "∀" "Π" "∏" "lambda" "λ") eow))
(defface m31-tt-binder-begin-face '((t (:inherit font-lock-type-face)))
  "" :group 'm31)

(defvar m31-tt-binder-end-keywords '("->" "→" ","))

(defface m31-tt-binder-end-face '((t (:inherit m31-tt-binder-begin-face)))
  "" :group 'm31)

(defvar m31-boring-keywords '("," ";" "." "of"))
(defface m31-boring-face '((t (:inherit font-lock-preprocessor-face)))
  "" :group 'm31)

(defvar m31-pvar-rx (eval `(rx "?" (regexp ,m31-meta-variable-rx))))
(defface m31-pvar-face '((t (:inherit font-lock-variable-name-face)))
  "" :group 'm31)

(defvar m31-simple-syntax-classes '(boring cases topdirective meta tt))

(require 'cl-macs)
(defun m31-font-lock-mk (name)
  (cl-flet ((f (suf)
               (intern (concat "m31-" (symbol-name name) suf))))
    (list (regexp-opt (symbol-value (f "-keywords")) 'symbols) 1 `',(f "-face"))))

;; TODO: look into [info:elisp#Multiline Font Lock]
(defun m31-font-lock-defaults ()
  "Calculate the font-lock defaults for `m31-mode'."
  (list
   (append

    `((,(rx symbol-start (| "¬" "~") symbol-end) 0 'font-lock-negation-char-face))

    `((,(eval `(rx
                (group-n 1 (regexp ,m31-meta-binder-begin-rx))
                (group-n 2
                         (+ (| space (regexp "\n")))
                         (regexp ,m31-meta-variable-rx))
                (group-n 3 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,m31-meta-variable-rx))))))
       (1 '(m31-meta-binder-begin-face))
       (2 '(m31-meta-variable-face))
       (3 '(m31-pvar-face))))

    `((,(rx symbol-start (| "and" "as" "in") symbol-end) (0 '(m31-meta-binder-begin-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,(regexp-opt m31-tt-atom-keywords)))
                (group-n 2 (+ (seq
                               (+ (| space (regexp "\n")
                                     (regexp ",")
                                     ))
                               (regexp ,m31-meta-variable-rx))))))
       (1 '(m31-tt-atom-face))
       (2 '(m31-pvar-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,m31-mltype-rx))
                (+ (| space (regexp "\n")))
                (group-n 2 (regexp ,m31-meta-variable-rx))))
       (1 '(m31-boring-face))
       (2 '(m31-cases-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,m31-operation-rx))
                (+ (| space (regexp "\n")))
                (group-n 2 (regexp ,m31-meta-variable-rx))))
       (1 '(m31-boring-face))
       (2 '(m31-operation-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,m31-tt-binder-begin-rx))
                (group-n 2 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,m31-meta-variable-rx))))))
       (1 '(m31-tt-binder-begin-face))
       (2 '(m31-pvar-face))))

    `((,(eval `(rx
                (group-n 1 (sequence symbol-start "fun" symbol-end))
                (group-n 2 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,m31-meta-variable-rx))))))
       (1 '(m31-meta-binder-begin-face))
       (2 '(m31-pvar-face))))

    `((,(eval `(rx "!" (regexp ,m31-meta-variable-rx))) (0 '(m31-meta-face))))

    `((,m31-pvar-rx 0 'm31-pvar-face))

    (mapcar 'm31-font-lock-mk m31-simple-syntax-classes))))

(require 'subr-x)
(defvar m31-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?( "()1n" table)
                         (modify-syntax-entry ?* ". 23n" table)
                         (modify-syntax-entry ?) ")(4n" table)
    (modify-syntax-entry ?' "_" table)
    (modify-syntax-entry ?: "_" table)
    (modify-syntax-entry ?# "_" table)
    (modify-syntax-entry ?≡ "_" table)
    (mapc (lambda (c) (modify-syntax-entry c "." table)) ",;")
    (modify-syntax-entry ?¬ "w" table)
    (modify-syntax-entry ?∀ "w" table)
    (modify-syntax-entry ?∏ "w" table)
    (modify-syntax-entry ?⊢ "w" table)
    (modify-syntax-entry ?→ "_" table)
    ;; (modify-syntax-entry ?⟹ "w" table)
    ;; (modify-syntax-entry ?= "w" table)
    ;; (modify-syntax-entry ?> "w" table)
    (mapc (lambda (c) (modify-syntax-entry c "'"  table))
          (string-join m31-prefixop))
    table)
  "The syntax table used in `m31-mode'")



;;; Communicating with Andromeda
(require 'compile)

(defcustom m31-use-local-executable t
  "Whether or not to look for `m31-executable-name' in a parent
directory of the current file upon activation of `m31-mode'.
Useful typically when working with the Andromeda git repository."
:group 'm31)

(defcustom m31-executable-name "andromeda.native"
  "The name of the Andromeda executable file" :group 'm31)

(defun m31--find-executable nil
  (let ((d (locate-dominating-file
            (or buffer-file-name default-directory) m31-executable-name)))
    (if d
        (concat d m31-executable-name)
      "andromeda")))

(defun m31--set-executable-locally nil
  (when m31-use-local-executable
    (setq-local m31-executable (m31--find-executable))))

;;;###autoload
(defcustom m31-executable (m31--find-executable)
  "The name of the Andromeda executable"
  :group 'm31)

;;;###autoload
(defcustom m31-arguments ""
  "The `m31-executable' will be called with these arguments" :group 'andromeda)

(defun m31-compilation-buffer-name (&optional mm) "*andromeda*")

(defconst m31-error-single-line-regexp
  (rx bol "File \"" (group-n 1 (not (any ?\")))
      "\", line " (group-n 2 (+ digit))
      ", characters " (group-n 4 (+ digit)) "-" (group-n 5 (+ digit))
      ":" eol)
  "Regular expression matching and extracting locations from
  single-line error messages produced by Andromeda.")

(defconst m31-error-multi-line-regexp
  (rx bol "File \"" (group-n 1 (+ (not (any ?\"))))
      "\", line " (group-n 2 (+ digit))
      " character " (group-n 4 (+ digit)) " -"
      " line " (group-n 3 (+ digit))
      " character " (group-n 5 (+ digit))
      ":" eol)
  "Regular expression matching and extracting locations from
  multi-line error messages produced by Andromeda.")

(defun m31-get-andromeda-buffer-create nil
  (get-buffer-create (m31-compilation-buffer-name)))

(defun m31-send-file-up-to-lim (fn lim)
  (interactive)
  (let ((cmd (concat m31-executable " " m31-arguments " "
                     (if lim (concat "--lim-file " (int-to-string lim) " ") "")
                     "\"" fn "\""))
        (compilation-scroll-output 'first-error)
        (compilation-ask-about-save nil)
        (hist compile-history)
        (prev-cmd compile-command))
    (setq m31--current-buffer (current-buffer))
    (compile cmd)
    (setq compile-history hist
          compile-command prev-cmd)
    (with-current-buffer (m31-get-andromeda-buffer-create)
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
(defun m31-send-file (fn)
  (interactive)
  (m31-send-file-up-to-lim fn nil))

;;;###autoload
(defun m31-send-buffer nil
  "Send the current buffer to Andromeda"
  (interactive)
  (if buffer-file-name
      (m31-send-file (file-relative-name buffer-file-name))
    (error "No file associated to current buffer")))

;;;###autoload
(defun m31-send-buffer-up-to-point nil
  (interactive)
  (if buffer-file-name
      (m31-send-file-up-to-lim (file-relative-name buffer-file-name) (point))
    (error "No file associated to current buffer")))

(defun m31-interrupt-compile ()
  "Interrupt Andromeda"
  (interactive)
  (let* ((name (m31-compilation-buffer-name))
         (comp-proc (get-buffer-process (get-buffer name))))
    (when comp-proc
      (when (or (not (eq (process-status comp-proc) 'run))
                (yes-or-no-p
                 (format "Andromeda is running; kill it? " name)))
        (condition-case ()
            (progn
              (interrupt-process comp-proc)
              (sit-for 1)
              (delete-process comp-proc)))))))


;;; Debugging facilities for the andromeda project itself
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


(defcustom m31-ocamldebug-executable nil
  "Filename of the executable used in `m31-ocamldebug'. By default set through\
  `m31--set-debug-executable' in `m31-mode-hook'."
  :group 'm31)

(defun m31--find-debug-executable nil
    (concat
     (locate-dominating-file
      buffer-file-name
      ".dir-locals.el") "andromeda.d.byte"))

(defun m31--set-debug-executable nil
    (setq m31-ocamldebug-executable (m31--find-debug-executable)))

(defun m31-ocamldebug nil
  (interactive)
  (ocamldebug m31-ocamldebug-executable)
  (mapc
   (lambda (f)
     (add-hook 'comint-preoutput-filter-functions f nil t))
   m31-comint-filters)
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-init\n")
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-current\n"))



;;; Indentation
(defcustom m31-indent-smart nil
  "Non-`nil' value means that `m31-mode' will try to indent according to the\
  Andromeda parser. Otherwise, `eri-indent' will be used for
  semi-manual\ indentation." :group 'm31)

(defun m31-eri-setup nil
  (setq-local indent-line-function 'eri-indent)
  (define-key m31-mode-map (kbd "<backtab>") 'eri-indent-reverse))

(defun m31--indentation-setup nil
  (if m31-indent-smart
      (progn (require 'andromeda-smie) (m31-smie-setup))
    (progn (require 'eri) (m31-eri-setup))))


;;; The major mode for writing galactical type theory
;;;###autoload
(define-derived-mode m31-mode prog-mode "m31"
  "Major mode for editing Andromeda files.

Useful commands:
C-c C-.          m31-send-buffer-up-to-point
C-c .            m31-send-buffer-up-to-point
C-c C-b          m31-send-buffer
C-c C-l          m31-send-buffer
"
  (setq-local require-final-newline mode-require-final-newline)
  (setq-local compilation-buffer-name-function 'm31-compilation-buffer-name)
  (setq-local require-final-newline t)
  (setq-local comment-start "(* ")
  (setq-local comment-end " *)")
  (setq-local comment-start-skip "(\\*+[ \t]*")
  (setq-local font-lock-defaults (m31-font-lock-defaults))
  (setq-local compilation-error-regexp-alist '(andromeda-multi andromeda-single))
  (setq-local
   compilation-error-regexp-alist-alist
   `((andromeda-multi ,m31-error-multi-line-regexp 1 (2 . 3) (4 . 5) 2 nil)
     (andromeda-single ,m31-error-single-line-regexp 1 2 (4 . 5) 2 nil))))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.m31\\'" . m31-mode))

(define-key m31-mode-map (kbd "C-c C-.") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c .") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c C-b") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-l") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-c") 'm31-interrupt-compile)

(add-hook 'm31-mode-hook 'm31--set-executable-locally)
(add-hook 'm31-mode-hook 'm31--set-debug-executable)

(add-hook 'm31-mode-hook 'm31--indentation-setup)

(provide 'andromeda)
;;; andromeda.el ends here
