(defgroup and1 nil "Editing Andromeda-1 code." :prefix 'and1-
  :group 'languages)


;;; Syntax highlighting
(defvar and1-symbolchars '("!" "$" "%" "&" "*" "+" "-" "." "/" ":" "<" "=" ">" "?" "@" "^" "|" "~"))
(defvar and1-prefixop '("~" "?" "!"))
(defvar and1-infixop '("=" "<" ">" "|" "&" "$" "@" "^" "+" "-" "*" "/" "%" "**"))

(defvar and1-anonymous "_")

(defvar and1-operation-rx "operation")

(defface and1-operation-face '((t (:inherit font-lock-function-name-face)))
  "" :group 'and1)

(defvar and1-cases-keywords
  '("mltype" "operation"
    "handle" "handler"
    "match" "|" "with"
    "val" "finally"
    "end"
    "yield"))

(defface and1-cases-face '((t (:inherit font-lock-keyword-face)))
  "" :group 'and1)

(defvar and1-mltype-rx "mltype")
(defface and1-mltype-face '((t (:inherit and1-cases-face)))
  "" :group 'and1)
;; swap with constant / tt ?

(defvar and1-meta-binder-begin-rx
  (rx symbol-start                               ;FIXME: should be symbol \_< not \<
      (|
       ;; "and"  ; problematic because we use it in mltype declarations
       "dynamic" "now"
       (seq "let" (? (+ space) "rec")))
      symbol-end))

(defface and1-meta-binder-begin-face '((t (:inherit font-lock-preprocessor-face)))
  "" :group 'and1)

(defvar and1-meta-variable-rx
  (eval
   `(rx
     (|
      ;; "::"
      (sequence "(" (* space)
                (* (any ,(mapconcat (lambda (c) c) and1-symbolchars "")))
                (* space) ")")
      (sequence (| (syntax word) "_") (* (| (syntax word) (syntax symbol))))))))
(defface and1-meta-variable-face '((t (:inherit font-lock-function-name-face)))
  "" :group 'and1)

(defvar and1-meta-binder-end-keywords
  '("in"
    "="
    "=>" "⇒" "⟹"))
(defface and1-meta-binder-end-face '((t (:inherit and1-meta-binder-begin-face)))
  "" :group 'and1)

(defvar and1-topdirective-keywords '("do" "fail"))
(defface and1-topdirective-face '((t (:inherit font-lock-keyword-face)))
  "" :group 'and1)

(defvar and1-meta-keywords
  '(
    ;; "judgement"
    ;; "judgment"
    ;; "_"
    "external"
    "#include_once"
    "ref" "!" ":="
    ;;    ";" ","
    ))
(defface and1-meta-face '((t (:inherit font-lock-constant-face)))
  "" :group 'and1)

(defvar and1-tt-keywords
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
(defface and1-tt-face '((t (:inherit font-lock-type-face)))
  "" :group 'and1)

(defvar and1-tt-atom-keywords
  '("assume" "constant"))
(defface and1-tt-atom-face '((t (:inherit font-lock-type-face)))
  "" :group 'and1)

(defvar and1-tt-binder-begin-rx (rx bow (| "forall" "∀" "Π" "∏" "lambda" "λ") eow))
(defface and1-tt-binder-begin-face '((t (:inherit font-lock-type-face)))
  "" :group 'and1)

(defvar and1-tt-binder-end-keywords '("->" "→" ","))

(defface and1-tt-binder-end-face '((t (:inherit and1-tt-binder-begin-face)))
  "" :group 'and1)

(defvar and1-boring-keywords '("," ";" "." "of"))
(defface and1-boring-face '((t (:inherit font-lock-preprocessor-face)))
  "" :group 'and1)

(defvar and1-pvar-rx (eval `(rx "?" (regexp ,and1-meta-variable-rx))))
(defface and1-pvar-face '((t (:inherit font-lock-variable-name-face)))
  "" :group 'and1)

(defvar and1-simple-syntax-classes '(boring cases topdirective meta tt))

(require 'cl-macs)
(defun and1-font-lock-mk (name)
  (cl-flet ((f (suf)
               (intern (concat "and1-" (symbol-name name) suf))))
    (list (regexp-opt (symbol-value (f "-keywords")) 'symbols) 1 `',(f "-face"))))

;; TODO: look into [info:elisp#Multiline Font Lock]
(defun and1-font-lock-defaults ()
  "Calculate the font-lock defaults for `and1-mode'."
  (list
   (append

    `((,(rx symbol-start (| "¬" "~") symbol-end) 0 'font-lock-negation-char-face))

    `((,(eval `(rx
                (group-n 1 (regexp ,and1-meta-binder-begin-rx))
                (group-n 2
                         (+ (| space (regexp "\n")))
                         (regexp ,and1-meta-variable-rx))
                (group-n 3 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,and1-meta-variable-rx))))))
       (1 '(and1-meta-binder-begin-face))
       (2 '(and1-meta-variable-face))
       (3 '(and1-pvar-face))))

    `((,(rx symbol-start (| "and" "as" "in") symbol-end) (0 '(and1-meta-binder-begin-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,(regexp-opt and1-tt-atom-keywords)))
                (group-n 2 (+ (seq
                               (+ (| space (regexp "\n")
                                     (regexp ",")
                                     ))
                               (regexp ,and1-meta-variable-rx))))))
       (1 '(and1-tt-atom-face))
       (2 '(and1-pvar-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,and1-mltype-rx))
                (+ (| space (regexp "\n")))
                (group-n 2 (regexp ,and1-meta-variable-rx))))
       (1 '(and1-boring-face))
       (2 '(and1-cases-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,and1-operation-rx))
                (+ (| space (regexp "\n")))
                (group-n 2 (regexp ,and1-meta-variable-rx))))
       (1 '(and1-boring-face))
       (2 '(and1-operation-face))))

    `((,(eval `(rx
                (group-n 1 (regexp ,and1-tt-binder-begin-rx))
                (group-n 2 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,and1-meta-variable-rx))))))
       (1 '(and1-tt-binder-begin-face))
       (2 '(and1-pvar-face))))

    `((,(eval `(rx
                (group-n 1 (sequence symbol-start "fun" symbol-end))
                (group-n 2 (* (seq
                               (+ (| space (regexp "\n")))
                               (regexp ,and1-meta-variable-rx))))))
       (1 '(and1-meta-binder-begin-face))
       (2 '(and1-pvar-face))))

    `((,(eval `(rx "!" (regexp ,and1-meta-variable-rx))) (0 '(and1-meta-face))))

    `((,and1-pvar-rx 0 'and1-pvar-face))

    (mapcar 'and1-font-lock-mk and1-simple-syntax-classes))))

(require 'subr-x)
(defvar and1-mode-syntax-table
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
          (string-join and1-prefixop))
    table)
  "The syntax table used in `and1-mode'")



;;; Communicating with Andromeda-1
(require 'compile)

(defcustom and1-use-local-executable t
  "Whether or not to look for `and1-executable-name' in a parent
directory of the current file upon activation of `and1-mode'.
Useful typically when working with the Andromeda-1 git repository."
:group 'and1)

(defcustom and1-executable-name "andromeda.native"
  "The name of the Andromeda-1 executable file" :group 'and1)

(defun and1--find-executable nil
  (let ((d (locate-dominating-file
            (or buffer-file-name default-directory) and1-executable-name)))
    (if d
        (concat d and1-executable-name)
      "andromeda-1")))

(defun and1--set-executable-locally nil
  (when and1-use-local-executable
    (setq-local and1-executable (and1--find-executable))))

;;;###autoload
(defcustom and1-executable (and1--find-executable)
  "The name of the Andromeda-1 executable"
  :group 'and1)

;;;###autoload
(defcustom and1-arguments ""
  "The `and1-executable' will be called with these arguments" :group 'andromeda-1)

(defun and1-compilation-buffer-name (&optional mm) "*andromeda-1*")

(defconst and1-error-single-line-regexp
  (rx bol "File \"" (group-n 1 (not (any ?\")))
      "\", line " (group-n 2 (+ digit))
      ", characters " (group-n 4 (+ digit)) "-" (group-n 5 (+ digit))
      ":" eol)
  "Regular expression matching and extracting locations from
  single-line error messages produced by Andromeda-1.")

(defconst and1-error-multi-line-regexp
  (rx bol "File \"" (group-n 1 (+ (not (any ?\"))))
      "\", line " (group-n 2 (+ digit))
      " character " (group-n 4 (+ digit)) " -"
      " line " (group-n 3 (+ digit))
      " character " (group-n 5 (+ digit))
      ":" eol)
  "Regular expression matching and extracting locations from
  multi-line error messages produced by Andromeda-1.")

(defun and1-get-andromeda-1-buffer-create nil
  (get-buffer-create (and1-compilation-buffer-name)))

(defun and1-send-file-up-to-lim (fn lim)
  (interactive)
  (let ((cmd (concat and1-executable " " and1-arguments " "
                     (if lim (concat "--lim-file " (int-to-string lim) " ") "")
                     "\"" fn "\""))
        (compilation-scroll-output 'first-error)
        (compilation-ask-about-save nil)
        (hist compile-history)
        (prev-cmd compile-command))
    (setq and1--current-buffer (current-buffer))
    (compile cmd)
    (setq compile-history hist
          compile-command prev-cmd)
    (with-current-buffer (and1-get-andromeda-1-buffer-create)
      (set
       (make-local-variable
        'compilation-finish-functions)
       '((lambda (buf msg)
           (let ((c (get-buffer-window and1--current-buffer))
                 (w (get-buffer-window buf 'visible)))
             (when w
               (select-window w t)
               (when (eobp)
                 (recenter -1))
               (select-window c t)))))))))

;;;###autoload
(defun and1-send-file (fn)
  (interactive)
  (and1-send-file-up-to-lim fn nil))

;;;###autoload
(defun and1-send-buffer nil
  "Send the current buffer to Andromeda-1"
  (interactive)
  (if buffer-file-name
      (and1-send-file (file-relative-name buffer-file-name))
    (error "No file associated to current buffer")))

;;;###autoload
(defun and1-send-buffer-up-to-point nil
  (interactive)
  (if buffer-file-name
      (and1-send-file-up-to-lim (file-relative-name buffer-file-name) (point))
    (error "No file associated to current buffer")))

(defun and1-interrupt-compile ()
  "Interrupt Andromeda-1"
  (interactive)
  (let* ((name (and1-compilation-buffer-name))
         (comp-proc (get-buffer-process (get-buffer name))))
    (when comp-proc
      (when (or (not (eq (process-status comp-proc) 'run))
                (yes-or-no-p
                 (format "Andromeda-1 is running; kill it? " name)))
        (condition-case ()
            (progn
              (interrupt-process comp-proc)
              (sit-for 1)
              (delete-process comp-proc)))))))


;;; Debugging facilities for the andromeda-1 project itself
(setq and1-comint-filters
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


(defcustom and1-ocamldebug-executable nil
  "Filename of the executable used in `and1-ocamldebug'. By default set through\
  `and1--set-debug-executable' in `and1-mode-hook'."
  :group 'and1)

(defun and1--find-debug-executable nil
    (concat
     (locate-dominating-file
      buffer-file-name
      ".dir-locals.el") "andromeda-1.d.byte"))

(defun and1--set-debug-executable nil
    (setq and1-ocamldebug-executable (and1--find-debug-executable)))

(defun and1-ocamldebug nil
  (interactive)
  (ocamldebug and1-ocamldebug-executable)
  (mapc
   (lambda (f)
     (add-hook 'comint-preoutput-filter-functions f nil t))
   and1-comint-filters)
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-init\n")
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-current\n"))



;;; Indentation
(defcustom and1-indent-smart nil
  "Non-`nil' value means that `and1-mode' will try to indent according to the\
  Andromeda-1 parser. Otherwise, `eri-indent' will be used for
  semi-manual\ indentation." :group 'and1)

(defun and1-eri-setup nil
  (setq-local indent-line-function 'eri-indent)
  (define-key and1-mode-map (kbd "<backtab>") 'eri-indent-reverse))

(defun and1--indentation-setup nil
  (if and1-indent-smart
      (progn (require 'andromeda-1-smie) (and1-smie-setup))
    (progn (require 'eri) (and1-eri-setup))))


;;; The major mode for writing galactical type theory
;;;###autoload
(define-derived-mode and1-mode prog-mode "and1"
  "Major mode for editing Andromeda-1 files.

Useful commands:
C-c C-.          and1-send-buffer-up-to-point
C-c .            and1-send-buffer-up-to-point
C-c C-b          and1-send-buffer
C-c C-l          and1-send-buffer
"
  (setq-local require-final-newline mode-require-final-newline)
  (setq-local compilation-buffer-name-function 'and1-compilation-buffer-name)
  (setq-local require-final-newline t)
  (setq-local comment-start "(* ")
  (setq-local comment-end " *)")
  (setq-local comment-start-skip "(\\*+[ \t]*")
  (setq-local font-lock-defaults (and1-font-lock-defaults))
  (setq-local compilation-error-regexp-alist '(andromeda-1-multi andromeda-1-single))
  (setq-local
   compilation-error-regexp-alist-alist
   `((andromeda-1-multi ,and1-error-multi-line-regexp 1 (2 . 3) (4 . 5) 2 nil)
     (andromeda-1-single ,and1-error-single-line-regexp 1 2 (4 . 5) 2 nil))))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.m31\\'" . and1-mode))

(define-key and1-mode-map (kbd "C-c C-.") 'and1-send-buffer-up-to-point)
(define-key and1-mode-map (kbd "C-c .") 'and1-send-buffer-up-to-point)
(define-key and1-mode-map (kbd "C-c C-b") 'and1-send-buffer)
(define-key and1-mode-map (kbd "C-c C-l") 'and1-send-buffer)
(define-key and1-mode-map (kbd "C-c C-c") 'and1-interrupt-compile)

(add-hook 'and1-mode-hook 'and1--set-executable-locally)
(add-hook 'and1-mode-hook 'and1--set-debug-executable)

(add-hook 'and1-mode-hook 'and1--indentation-setup)

(provide 'andromeda-1)
;;; andromeda-1.el ends here
