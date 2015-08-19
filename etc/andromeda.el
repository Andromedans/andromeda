(require 'compile)

(defgroup m31 nil "Customization options for Andromeda" :prefix 'm31-
  :group 'languages)

;;;###autoload
(defcustom m31-executable
  (let ((d (locate-dominating-file
            (or buffer-file-name default-directory) "andromeda.byte")))
    (if d
        (concat d "andromeda.byte")
      "andromeda"))
  "The name of the Andromeda executable"
  :group 'm31)

;;;###autoload
(defcustom m31-arguments ""
  "The `m31-executable' will be called with these arguments" :group 'andromeda)



;;; Syntax highlighting

(defface m31-keyword-face '((t (:inherit font-lock-keyword-face)))
  "The face used to highlight M31 keywords."
  :group 'm31)

(defface m31-variable-name-face '((t (:inherit font-lock-function-name-face)))
  "The face used to highlight M31 tactics."
  :group 'm31)

(defface m31-name-face '((t (:inherit font-lock-variable-name-face)))
  "The face used to highlight m31 names."
  :group 'm31)

(defface m31-comment-face '((t (:inherit font-lock-comment-face)))
  "The face used to highlight m31 comments."
  :group 'm31)

(defconst m31-builtins '("reduce"))
(defface m31-builtin-face '((t (:inherit font-lock-builtin-face)))
         "The face for builtin keywords of Andromeda" :group 'm31)

(defconst m31-topcomputations '("Axiom" "assume" "Let" "Parameter" "Check")
  "Vernacular for `m31-mode'.")
(defface m31-topcomputation-face '((t (:inherit font-lock-keyword-face)))
         "The face for the Andromea vernacular" :group 'm31)

(defvar m31-topdirectives '("#context" "#help" "#include" "#quit" "#verbosity"))
(defface m31-topdirective-face '((t (:inherit font-lock-warning-face)))
         "The face for toplevel directives such as \"#help\" or \"#include\"")

;;  '("->" "⟶" "=>" "⟹")

(defvar m31-computations
  '("Beta" "beta"
    "Eta" "eta"
    "Hint" "hint"
    "Inhabit" "inhabit"
    "Unhint" "unhint"
    "refl" "≡" "=="
    ;; ":"
    "Type"
    "whnf")

  "A list of the computations to be highlighted in Andromeda mode.")

(defface m31-computation-face
 '((t (:inherit font-lock-constant-face)))
  "The face used to highlight m31 computations."
  :group 'm31)

(defvar m31-binders '("Let" "let" "assume" "Axiom" "Parameter"))
(defface m31-binder-face '((t (:inherit font-lock-function-name-face)))
         "The face used for binders" :group 'm31)

(defvar m31--abstraction-end '("⟹" "=>" "⟶" "->" ","))
(defvar m31-abstractions '("Π" "forall" "∀" "λ" "fun" "[" "]" "⟹" "=>"))
(defface m31-abstraction-face '((t (:inherit font-lock-type-face)))
         "The face used for abstractions" :group 'm31)

(defvar m31-borings '("," ";" "." "let" "and" "in" ":="))
(defface m31-boring-face '((t (:inherit font-lock-preprocessor-face)))
         "The face used for boring kewords such as \"let\"")

(defvar m31-syntax-classes
  '(abstraction boring computation topdirective topcomputation builtin))

(defun m31-font-lock-mk (name)
  (cl-flet ((f (suf)
               (intern (concat "m31-" (symbol-name name) suf))))
    (list (regexp-opt (symbol-value (f "s")) 'symbols) 1 `',(f "-face"))))

(defvar m31-binder-face 'm31-binder-face)
(defvar m31-name-face 'm31-name-face)


(defun m31-font-lock-defaults ()
  "Calculate the font-lock defaults for `m31-mode'."
  (list
   (append
    '(("\\<¬\\>" 0 'font-lock-negation-char-face))

    (let* ((r (regexp-opt m31-binders 'symbols))
           (n (regexp-opt-depth r)))
      `((,(concat
           r
            "[[:space:]]*\\(\\_<\\(:?\\w\\|\\s_\\)+\\_>\\)")
            ,(1+ n) '(m31-binder-face))))

    (mapcar 'm31-font-lock-mk m31-syntax-classes))))

(defvar m31-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?( "()1n" table)
    (modify-syntax-entry ?* ". 23n" table)
    (modify-syntax-entry ?) ")(4n" table)
    (modify-syntax-entry ?' "_" table)
    (modify-syntax-entry ?: "_" table)
    (modify-syntax-entry ?# "_" table)
    (modify-syntax-entry ?≡ "_" table)
    (modify-syntax-entry ?¬ "w" table)
    (modify-syntax-entry ?∀ "w" table)
    ;; (modify-syntax-entry ?⟹ "w" table)
    ;; (modify-syntax-entry ?= "w" table)
    ;; (modify-syntax-entry ?> "w" table)
    table))



;;; Indentation
(require 'smie)

(defvar m31--name-re "\\(\\w\\|\\s_\\)+")
(defvar m31--quoted-string-re (rx (seq ?\" (1+ (not (any ?\"))) ?\")))
(defvar m31--topdir-re
  (rx
   (or "#context" "#help" "#quit"
       (seq "#verbosity" (+ (any blank)) (+ (any digit)))
       (seq "#include"
            (+
             (seq
              (+ (any blank))
              (eval (cons 'regexp (list m31--quoted-string-re)))))))))

;; all hints simply produce a "HINT" token
(defvar m31--reserved
  '(("Axiom" . "PRIMITIVE")
    ("and" . "AND")
    ("beta" . "HINT")
    ("Beta" . "TOPHINT")
    ("Check" . "TOPCHECK")
    ("whnf" . "WHNF")
    ("eta" . "HINT")
    ("Eta" . "TOPHINT")
    ("hint" . "HINT")
    ("Hint" . "TOPHINT")
    ("unhint" . "UNHINT")
    ("Unhint" . "TOPUNHINT")
    ("Hypothesis" . "PRIMITIVE")
    ("inhabit" . "HINT")
    ("Inhabit" . "TOPHINT")
    ("Let" . "TOPLET")
    ("let" . "LET")
    ("Parameter" . "PRIMITIVE")
    ("reduce" . "REDUCE")
    ("forall" . "FORALL")
    ("∀" . "FORALL")
    ("Π" . "FORALL")
    ("fun" . "FUN")
    ("λ" . "FUN")
    ("in" . "IN")
    ("refl" . "REFL")
    ("Type" . "TYPE")))


(defvar m31--in-list-check-forward nil)
(defvar m31--in-list-check-backward nil)

(defun m31--guess-comma nil
  (let ((last-forall
         (if (looking-back "\\(Π\\|forall\\|∀\\)\\(:?\n\\|.\\)*") (match-beginning 0) 0))
        (last-hint
         (if (looking-back
              "\\(:?[Hh]int\\|[Bb]?eta\\|[Ii]nhabit\\)\\(:?\n\\|.\\)*")
             (match-beginning 0) 0)))
    (if (> last-forall last-hint)
        "forall-comma"
      "hint-comma")))

(defun m31--smie-token (dir)
  (cl-flet ((f (case dir ('forward 'looking-at)
                     ('backward (lambda (r) (looking-back r nil t))))))
    (cond
     ((f m31--topdir-re)  "TOPDIRECTIVE")
     ((f "(")             (progn (setq m31--in-list-check-backward t) "LPAREN"))
     ((f ")")             (progn (setq m31--in-list-check-forward  t) "RPAREN"))
     ((f "\\[")           "LBRACK")
     ((f "\\]")           "RBRACK")
     ((f ":=")            "COLONEQ")
     ((f ":")             "COLON")
     ((f ",")             (save-match-data (m31--guess-comma)))
     ((f ";")             "SEMICOLON")
     ((f "\\.")           "DOT")
     ((f "_")             "UNDERSCORE")
     ((f "->\\|⟶")      "ARROW")
     ((f "=>\\|⟹")      "DARROW")
     ((f "==\\|≡")        "EQEQ")
     ((f m31--name-re)
      (let ((s (buffer-substring-no-properties
                (match-beginning 0) (match-end 0))))
        (or
         (cdr (assoc s m31--reserved))
         "NAME")))
     ((f ".") "idk"))))

(defun m31--smie-forward-token nil
  (forward-comment (point-max))
  (if (and m31--in-list-check-forward
           (looking-back ")[[:space:]]*" nil t)
           (looking-at "("))
      (progn (setq m31--in-list-check-forward nil)
             "paren-list-sep")
    (let ((s (m31--smie-token 'forward)))
      (goto-char (match-end 0))
      s)))

(defun m31--smie-backward-token nil
  (forward-comment (- (point)))
  (if (and m31--in-list-check-backward
           (looking-back ")" nil t)
           (looking-at "[[:space:]]*("))
      (progn (setq m31--in-list-check-backward nil)
             "paren-list-sep")
    (let ((s (m31--smie-token 'backward)))
      (goto-char (match-beginning 0))
      s)))

(defun m31-smie-forward-token nil
  (interactive)
  (message "%s" (m31--smie-forward-token)))
(defun m31-smie-backward-token nil
  (interactive)
  (message "%s" (m31--smie-backward-token)))

(defvar m31-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((file  (topcomp "DOT" file)
             ("TOPDIRECTIVE" file))
      ;; (topdirective   ("TOPDIRECTIVE"))
      (topcomp        ("TOPLET" "NAME" paren_binds_ret "COLONEQ" term)
                      ("TOPCHECK" term)
                      ("TOPHINT" tags_hints)
                      ("TOPUNHINT" tags_unhints)
                      ("PRIMITIVE" names_primargs "COLON" term))
      (paren_binds_ret (paren_binds)
                       ;;(paren_binds "COLON" ty_term)
                       )
      (term           (ty_term)
                      ("WHNF" term)
                      ("LET" let_clauses "IN" term)
                      ("HINT" tags_opt_hints "IN" term)
                      ("UNHINT" tags_unhints "IN" term)
                      (term "ascr_COLON" term))
      (ty_term        (equal_term)
                      ("FORALL" abstraction "forall-comma" term)
                      ("FUN" abstraction "DARROW" term)
                      (equal_term "ARROW" ty_term))
      (equal_term     (app_term)
                      (app_term "EQEQ" app_term))
      (app_term       (simple_term)
                      (simple_term "@" app_term)
                      ("REFL" simple_term))
      (simple_term    ("TYPE")
                      ("LBRACK" "RBRACK")
                      ("LBRACK" term "RBRACK")
                      ("LPAREN" term "RPAREN")
                      (empty "NAME" empty))
      (let_clauses    (let_clause "AND" let_clauses)
                      (let_clause))
      (empty)
      (let_clause     (empty "NAME" "COLONEQ" term))
      (abstraction    (bind)
                      (paren_binds))
      (bind           (names "COLON" ty_term))
      (paren_bind     ("LPAREN" bind "RPAREN"))
      (paren_binds    (paren_bind "paren-list-sep" paren_binds))
      (paren_bind_red ("LPAREN" "REDUCE" names "COLON" term "RPAREN"))
      (primargs       (paren_bind     "paren-list-sep" primargs)
                      (paren_bind_red "paren-list-sep" primargs))
      (names_primargs (names "NAME" primargs))
      (name           (empty "NAME" empty))
      (names          (empty "NAME" names))
      (tags_unhints   (empty "NAME" "SEMICOLON" tags_unhints)
                      (name))
      (tags_hint      (name)
                      (names "COLON" comma_terms))
      (tags_hints     (tags_hint)
                      (tags_hint "tags_SEMICOLON" tags_hints))
      (comma_terms    (name)
                      (name "hint-comma" comma_terms))
      (tags_opt_hints (tags_opt_hint)
                      (tags_opt_hint "tags_SEMICOLON" tags_opt_hints))
      (tags_opt_hint  (tags_hint)
                      ("LPAREN" term "RPAREN")))

    '("IN" < "ascr_COLON")
    '("WHNF" > "ascr_COLON")
    '("ascr_COLON" = "ascr_COLON")
    '("forall-comma" < "ascr_COLON")
    '("DARROW" > "ascr_COLON")
    '("COLON" > "RPAREN")
    '("NAME" = "NAME")
    '("hint-comma" > "SEMICOLON"))))


;; lists of parenthesised expressions aren't aligned when broken over several lines

(defun m31-smie-rules (kind token)
  (pcase (cons kind token)
    (`(:elem . basic) smie-indent-basic)
    (`(,_ . "forall-comma") (smie-rule-separator kind))
    (`(:after . "COLONEQ") smie-indent-basic)
    (`(:before . ,(or `"begin" `"LPAREN" `"LBRACK"))
     (if (smie-rule-hanging-p) (smie-rule-parent)))
    (`(:after . ,(or `"in" `"end" `"RPAREN" `"RBRACK"))
     (if (smie-rule-hanging-p) (smie-rule-parent)))))


(defun m31-smie-setup nil
  (smie-setup m31-smie-grammar 'm31-smie-rules
              :forward-token 'm31--smie-forward-token
              :backward-token 'm31--smie-backward-token))



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

(defun m31-ocamldebug nil
  (interactive)
  (ocamldebug
   (concat
    (locate-dominating-file
     buffer-file-name
     ".dir-locals.el") "mainloop.d.byte"))
  (mapc
   (lambda (f)
     (add-hook 'comint-preoutput-filter-functions f nil t))
   m31-comint-filters)
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-init\n")
  (comint-send-string (get-buffer-process (current-buffer))
                      "source etc/debug-current\n"))


(defun m31-compilation-buffer-name (&optional mm) "*andromeda*")

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
  (m31-smie-setup))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.m31\\'" . m31-mode))

(define-key m31-mode-map (kbd "C-c C-.") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c .") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c C-b") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-l") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-c") 'm31-interrupt-compile)


(defun m31-get-andromeda-buffer-create nil
  (get-buffer-create (m31-compilation-buffer-name)))

;;;###autoload
(defun m31-send-file (fn)
  (interactive)
  (let ((cmd (concat m31-executable " " m31-arguments " " fn))
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
(defun m31-send-buffer nil
  "Send the current buffer to Andromeda"
  (interactive)
  (if buffer-file-name
      (m31-send-file buffer-file-name)
    (error "No file associated to current buffer")))

;;;###autoload
(defun m31-send-buffer-up-to-point nil
  (interactive)
  (if buffer-file-name
      (m31-send-file
       (concat
        buffer-file-name "#line_limit:"
        (int-to-string (point))))
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


(provide 'andromeda)
;;; andromeda.el ends here
