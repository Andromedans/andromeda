(add-to-list 'auto-mode-alist '("\\.m31\\'" . m31-mode))

;; Plan:
;; - restrict to a sublanguage for TT
;; - syntax highlighting
;; - smie


;; syntax highlighting
;; - what are the different syntactic categories?
;;   binders, toplevel keywords, punctuation, operators, ...
;;   they'll fix the fonts

(defgroup m31 nil "Editing Andromeda code." :prefix 'm31-
  :group 'languages)


;;; Syntax highlighting
(defvar m31-symbolchars '("!" "$" "%" "&" "*" "+" "-" "." "/" ":" "<" "=" ">" "?" "@" "^" "|" "~"))
(defvar m31-prefixop '("~" "?" "!"))
(defvar m31-infixop '("=" "<" ">" "|" "&" "$" "@" "^" "+" "-" "*" "/" "%" "**"))

(defvar m31-anonymous "_")

;; we can declare: operations, dynamic / static variables, ml-types, constants
;; we can bind: ml vars, dyn vars, tt vars, pvars
;; we can destruct: constructors, judgements, operations, finally, val




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
       ;; "fun"                               ;static variables
       (seq "let" (? (+ space) "rec")                               ;static variables
            ))
      symbol-end))

(defface m31-meta-binder-begin-face '((t (:inherit font-lock-preprocessor-face)))
  "" :group 'm31)

(defvar m31-meta-variable-rx
  (eval
   `(rx
     (|
      "::"
      (sequence "(" (* space)
                (* (any ,(mapconcat (lambda (c) c) m31-symbolchars "")))
                (* space) ")")
      (sequence (| (syntax word) "_") (* (| (syntax word) (syntax symbol))))))))
(defface m31-meta-variable-face '((t (:inherit font-lock-function-name-face)))
  "" :group 'm31)

(defvar m31-meta-binder-end-keywords
  '("in"
    "="
    "=>" "⇒" "⟹"
    ))
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

(defvar m31-syntax-classes
  '(
    boring
    cases
    topdirective
    meta tt
    ))

(require 'cl-macs)
(defun m31-font-lock-mk (name)
  (cl-flet ((f (suf)
               (intern (concat "m31-" (symbol-name name) suf))))
    (list (regexp-opt (symbol-value (f "-keywords")) 'symbols) 1 `',(f "-face"))))


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
                               (+ (| space (regexp "\n")))
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

    (mapcar 'm31-font-lock-mk m31-syntax-classes))))

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
    ;; (modify-syntax-entry ?⟹ "w" table)
    ;; (modify-syntax-entry ?= "w" table)
    ;; (modify-syntax-entry ?> "w" table)
    (mapc (lambda (c) (modify-syntax-entry c "'"  table))
          (string-join m31-prefixop))
    table)
  "The syntax table used in `m31-mode'")



;;; Indentation
(require 'smie)

;; TODO: add vdash here! in sedlex, it comes from `math'
(defvar m31--name-re m31-meta-variable-rx)
(defvar m31--quoted-string-re (rx (seq ?\" (1+ (not (any ?\"))) ?\")))

(defvar m31--topdir-re
  (rx
   (or (seq "verbosity" (+ (any blank)) (+ (any digit)))
       (seq "#include_once"
            (+
             (seq
              (+ (any blank))
              (eval (cons 'regexp (list m31--quoted-string-re)))))))))

(defvar m31--reserved
  '(("Type" . "TYPE")
    ("judgement" . "JUDGMENT")
    ("judgment" . "JUDGMENT")
    ("_" . "UNDERSCORE")
    ("_atom" . "UATOM")
    ("_constant" . "UCONSTANT")
    ("and" . "AND")
    ("as" . "AS")
    ("assume" . "ASSUME")
    ("beta_step" . "BETA_STEP")
    ("congr_prod" . "CONGR_PROD")
    ("congr_apply" . "CONGR_APPLY")
    ("congr_lambda" . "CONGR_LAMBDA")
    ("congr_eq" . "CONGR_EQ")
    ("congr_refl" . "CONGR_REFL")
    ("constant" . "CONSTANT")
    ("context" . "CONTEXT")
    ("do" . "DO")
    ("dynamic" . "DYNAMIC")
    ("end" . "END")
    ("external" . "EXTERNAL")
    ("fail" . "DO")
    ("finally" . "FINALLY")
    ("forall" . "PROD")
    ("fun" . "FUN")
    ("handle" . "HANDLE")
    ("handler" . "HANDLER")
    ("in" . "IN")
    ("lambda" . "LAMBDA")
    ("let" . "LLET")
    ("match" . "MATCH")
    ("mlstring" . "MLSTRING")
    ("mltype" . "MLTYPE")
    ("mlunit" . "MLUNIT")
    ("natural" . "NATURAL")
    ("now" . "LLET")
    ("occurs" . "OCCURS")
    ("of" . "OF")
    ("operation" . "OPERATION")
    ("rec" . "REC")
    ("ref" . "REF")
    ("refl" . "REFL")
    ("val" . "VAL")
    ("verbosity" . "VERBOSITY")
    ("where" . "WHERE")
    ("with" . "WITH")
    ("yield" . "YIELD")
    ("Π" . "PROD")
    ("λ" . "LAMBDA")
    ("∀" . "PROD")
    ("∏" . "PROD")
    ("⊢" . "VDASH")))

(require 'cl-macs)
;; (defun m31--smie-token (dir)
;;   (let ((let-rec-rx (rx (| "now" (seq "let" (? (+ space) "rec"))))))
;;     (cl-flet ((f (cl-case dir ('forward 'looking-at)
;;                           ('backward (lambda (r) (looking-back r nil t)))))
;;               (llet-heuristic
;;                (lambda nil
;;                  (save-match-data
;;                    (save-excursion
;;                      (search-forward-regexp
;;                       ".*\\_<=\\_>.*\\_<in\\_>"
;;                       (save-excursion (end-of-line 1) (point))
;;                       'noerror
;;                       )))))
;;               )
;;       (cond
;;        ((f m31--topdir-re)  "TOPDIRECTIVE")
;;        ((f "(")             (progn (setq m31--in-list-check-backward t) "LPAREN"))
;;        ((f ")")             (progn (setq m31--in-list-check-forward  t) "RPAREN"))
;;        ((f "\\[")           "LBRACK")
;;        ((f "\\]")           "RBRACK")
;;        ((f ":=")            "COLONEQ")
;;        ((f "\\_<=\\_>")     "EQ")
;;        ((f "::")            "NAME")
;;        ((f ":")             "COLON")
;;        ((f ",")             "COMMA")
;;        ((f ";")             "SEMICOLON")
;;        ((f "|-")            "NAME")
;;        ((f "|")             "BAR")
;;        ((f "_")             "UNDERSCORE")
;;        ((f "->\\|⟶")        "ARROW")
;;        ((f "=>\\|⟹\\|⇒")       "DARROW")
;;        ((f "==\\|≡")        "EQEQ")
;;        ((f
;;          ;; there should be a way to figure out the indentation column of the
;;          ;; current module level, use that instead of ^
;;          (concat
;;           "^\\(:?" let-rec-rx "\\)"))  (if (llet-heuristic)
;;                                 "LLET"
;;                               "TLET"))
;;        ((f let-rec-rx)      "LLET")
;;        ((f m31-pvar-rx)     "NAME")
;;        ((f m31--name-re)
;;         (let ((s (buffer-substring-no-properties
;;                   (match-beginning 0) (match-end 0))))
;;           (or
;;            (cdr (assoc s m31--reserved))
;;            "NAME")))
;;        ((f m31--quoted-string-re) "STRING")
;;        ((eobp) "EOF")
;;        ((f ".") "idk")))))


(defcustom m31-indent-basic smie-indent-basic "" :group 'm31)
(defcustom m31-indent-do (/ m31-indent-basic 2) "" :group 'm31)
(defcustom m31-indent-after-with 0 "" :group 'm31)
(defcustom m31-indent-double-arrow 2 "" :group 'm31)

;; sequencing, toplevel-handlers, top-let, #include, dynamic, top-now

(defvar m31-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2

    '((topdirs  (topdirs "CONSTANT" topdirs)
                (topdirs "OPERATION" topdirs)
                (topdirs "DYNAMIC" topdirs)
                (topdirs "DO" topdirs)
                (topdirs "MLTYPE" topdirs)
                (topdirs "HANDLE" topdirs)
                (topdirs "TOPDIRECTIVE" topdirs)
                (topdirs "TLET" topdirs)
                ;; (term "WITH" term)

                (names "EQ" tydefs)
                (names "COLON" term)
                (names "EQ" term)
                (pattern)
                )

      (tydefs   (tydefs "TYBAR" tydefs)
                (tydef))
      (tydef    (names)
                (names "OF" tyargs))
      (tyargs   ;(names "AND" tyargs)
       ("AND" tyargs)
       (names)
       )

      (term     (ty_term)
;                ("HANDLE" term "WITH" patterns "END")
                ;; ("WITH" term "HANDLE" term)
                ("MATCH" term "WITH" patterns "END")
                ("LLET" names "EQ" term "IN" term)
                ("ASSUME" "NAME" "COLON" term "IN" term)
                ("AND" names "EQ" term "IN" term)
                ("HANDLER" patterns "END")
                (term "NAME" term)
                (term "COLON" ty_term)
                ("LAMBDA" simple_term "COMMA" term)
                ("FUN" names "DARROW" term)
                ("STRING")
                (term "COMMA" term)
;                (names)
                )

      (ty_term  (term "EQEQ" term)
                (simple_term))

      (simple_term ("TYPE")
                   ("LPAREN" term "RPAREN"))

      (names    (names "NAME" names))

      (patterns (patterns "BAR" patterns)
                (pattern))

      (pattern  (term "DARROW" term)
                (term "COLON" term "DARROW" term))

      )

    ;; '("IN" < "ascr_COLON")
     '((assoc "DO" "CONSTANT" "OPERATION" "MLTYPE" "DYNAMIC" "TLET"
              "TOPDIRECTIVE" "END")
       (assoc "HANDLE")

       (assoc "withtype"))
     '((right "COLON") (assoc "BAR" "TYBAR")
       (assoc "NAME")
       (left "EQEQ" "EQ")
       (assoc "IN" "DARROW")
       (assoc "COMMA")
       )
     )))

(defun smie-walk-parents nil (interactive)
       (let (smie--parent x)
         (setq x (smie-indent--parent))
         (message "%S" x)
         (goto-char (cadr x))))

(defun m31--before-darrow nil
  (when (smie-rule-hanging-p)
    (if (smie-rule-parent-p "COLON")
        (save-excursion
          ;; goto COLON
          (goto-char (cadr (smie-indent--parent)))
          (let (smie--parent)
            ;; goto BAR
            (goto-char (cadr (smie-indent--parent)))
            (smie-rule-parent m31-indent-basic)))
      ;; if the first | of a handle is omitted, the parent will be the handle
      ;; and not the bar, so we should indent like for a ??
      (if (smie-rule-parent-p "HANDLE")
          (progn (message "pt: %S, par: %S" (point) smie--parent)
                 (save-excursion
                   (back-to-indentation)
                   `(column . ,(+ (current-column) m31-indent-basic))))
        (smie-rule-parent m31-indent-double-arrow))
      )))

(defun m31-smie-rules (kind token)
  (message "looking at %S : %S, pt: %S" token kind (point))
  (pcase (cons kind token)
    (`(:elem . basic) (message "basic") m31-indent-basic)
;    (`(,_ . "COMMA") (message "separator-comma") (smie-rule-separator kind))
;    (`(,_ . "AND") (message "separator-AND") (smie-rule-separator kind))
    ;; (`(:after . "COLONEQ") m31-indent-basic)

    (`(:after . "IN") (message "after-IN, hanging: %S, parent: %S, prev-DO: %S"
                               (smie-rule-hanging-p) smie--parent (smie-rule-prev-p "DO"))
     (when (smie-rule-hanging-p)
       (if (smie-rule-prev-p "DO")
           (smie-rule-parent m31-indent-do)
         (smie-rule-parent))
       ))

    (`(:after . "EQ")
     (when (smie-rule-parent-p "MLTYPE")
       (message "after-EQ parent:MLTYPE , nxt-NAME: %S" (smie-rule-next-p "NAME"))
       (smie-rule-parent
        (+ (if (smie-rule-next-p "NAME") 2 0)
           m31-indent-basic))))
    (`(:before . "BAR")
     (if (smie-rule-parent-p "MLTYPE")
         (progn (message "before-BAR parent:MLTYPE")
                (smie-rule-parent m31-indent-basic))
       (message "before-BAR, %S" (smie-rule-prev-p "HANDLE" "WITH"))
       (if (smie-rule-prev-p "HANDLE" "WITH")
           m31-indent-after-with
         (if (smie-rule-parent-p "BAR")
             0
           m31-indent-after-with))
       ))

    (`(:before . "AND")
     (let ((x (smie-rule-parent-p "OF" "AND"))
           (y (smie-rule-parent-p "EQ" "LPAREN"))
           (depth 0)
           res found)
       (message "before-AND, %S, %S" x y)
       (if x
           (smie-rule-parent)
         (while (and (< depth 5)
                     (not found))
           (setq depth (1+ depth))
           (setq res (let (smie--parent) (smie-indent--parent)))
           (setq found (member (caddr res) '("LLET" "TLET" "AND")))
           (message "res: %S" res)
           (goto-char (cadr res))
           )
         (cons 'column
               (- (progn (m31--smie-forward-token) (current-column)) 3)))))

    (`(:after . "OF") (message "after-OF") m31-indent-basic)
    (`(:after . "AND") (message "after-AND") (smie-rule-parent m31-indent-basic))

    (`(:before . "MATCH") nil)

    (`(:before . "NAME")
    ;;  nil)
    ;; (`(:x . "x")

     (progn (message "before-NAME") nil)
     (if (smie-rule-parent-p "MLTYPE")
         (progn (message "before-NAME parent:MLTYPE , foo: %S" (smie-rule-prev-p "BAR"))
                (smie-rule-parent (+ 2 m31-indent-basic)))

       ;; after an IN we should find the corresponding opening LET.

       (if (and ;(smie-rule-bolp) & prev = in
            (message "prev: %S" (save-excursion
                                  (m31--smie-backward-token)))
            (equal (m31--smie-backward-token) "DARROW") (message "hi"))

           (save-excursion
             ;; the IN has an EQ as parent, so go there and find its parent
             ;; (let (smie--parent) (smie-indent--parent)
             ;;      (goto-char (cadr (smie-indent--parent)))
             ;;      (message "parent %S" smie--parent))
             (let (smie--parent) (smie-indent--parent)
                  (goto-char (cadr (smie-indent--parent)))
                  (message "parent %S" smie--parent))
             (message "pt %S" (point))
             (cons 'column (current-column)))
         (message "backward /= IN") nil))
     )

    (`(:after . "HANDLE") (message "after-HANDLE") m31-indent-basic)

    (`(:before . "HANDLE")
     (message "before-HANDLE, par: %S, prev: %S"
              (let (smie--parent) (smie-indent--parent))
              (save-excursion (smie-indent-backward-token)))
     (if (and (smie-rule-parent-p "DO") (smie-rule-prev-p "DO"))
         (progn (message "hi") m31-indent-do)
       (when (smie-rule-next-p "BAR")
         (smie-rule-parent))))

    ;; breaking application over lines
    (`(:after . "NAME") (message "after-NAME") m31-indent-basic)

    ;; (`(:before . "LET") (message "before-LET") m31-indent-basic)

    (`(:before . "EQEQ") (message "before-EQEQ") (smie-rule-parent))
    (`(:after . "EQEQ") (message "after-EQEQ, hang: %S" (smie-rule-hanging-p))
          (if (smie-rule-hanging-p)
              (smie-rule-parent m31-indent-basic)))

    (`(:before . "EQ") (message "before-EQ") (smie-rule-parent))

    (`(:after  . "DARROW")
     (message "after-DARROW, hang: %S, p0: %S, pt: %S"
              (smie-rule-hanging-p) smie--parent (point))
     (when (smie-rule-hanging-p) (message "foo")
       0))

    (`(:before . "DARROW")
     (message "before-DARROW, hang: %S, p0: %S, pt: %S"
              (smie-rule-hanging-p) smie--parent (point))
     (m31--before-darrow)
)

    (`(:after . "COLON")
     (when (smie-rule-parent-p "CONSTANT")
       (message "after-colon parent:cnst")
       (smie-rule-parent m31-indent-basic)))
    (`(:after . "CONSTANT") (message "after-cnst") m31-indent-basic)
    (`(:after . "DO") (message "after-DO") m31-indent-do)
    (`(:after . "WITH") (message "after-WITH") m31-indent-after-with)
    (`(:before . ,(or `"begin" `"LPAREN" `"LBRACK"))
     (if (smie-rule-hanging-p) (smie-rule-parent)))
    (`(:after . ,(or `"in" `"end" `"RPAREN" `"RBRACK"))
     (if (smie-rule-hanging-p) (smie-rule-parent)))
    (_ (progn (message "fall-through: %S . %S" kind token) nil))
    ))

(defun m31--smie-forward-token nil
  (forward-comment (point-max))
  (let ((s (m31--smie-token 'forward)))
    (goto-char (match-end 0))
    s))

(defun m31--smie-backward-token nil
  (forward-comment (- (point)))
  (let ((s (m31--smie-token 'backward)))
    (goto-char (match-beginning 0))
    s))

(defun m31-smie-forward-token nil
  (interactive)
  (message "%s" (m31--smie-forward-token)))
(defun m31-smie-backward-token nil
  (interactive)
  (message "%s" (m31--smie-backward-token)))

(defun m31-smie-setup nil
  (smie-setup m31-smie-grammar 'm31-smie-rules
              :forward-token 'm31--smie-forward-token
              :backward-token 'm31--smie-backward-token))




;;; communicating with andromeda
(require 'compile)

(defun m31--find-executable nil
  (let ((d (locate-dominating-file
            (or buffer-file-name default-directory) "andromeda.native")))
    (if d
        (concat d "andromeda.native")
      "andromeda")))

(defun m31--set-executable nil
  (setq m31-executable (m31--find-executable)))

;;;###autoload
(defcustom m31-executable (m31--find-executable)
  "The name of the Andromeda executable"
  :group 'm31)

;;;###autoload
(defcustom m31-arguments ""
  "The `m31-executable' will be called with these arguments" :group 'andromeda)

(defun m31-compilation-buffer-name (&optional mm) "*andromeda*")

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
  ;;(m31-smie-setup)
)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.m31\\'" . m31-mode))

(define-key m31-mode-map (kbd "C-c C-.") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c .") 'm31-send-buffer-up-to-point)
(define-key m31-mode-map (kbd "C-c C-b") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-l") 'm31-send-buffer)
(define-key m31-mode-map (kbd "C-c C-c") 'm31-interrupt-compile)

(add-hook 'm31-mode-hook 'm31--set-executable)
(add-hook 'm31-mode-hook 'm31--set-debug-executable)

(provide 'mini-m31)
;;; mini-m31.el ends here
