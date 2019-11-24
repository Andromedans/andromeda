
;;; Indentation
(require 'smie)

;; TODO: add vdash here! in sedlex, it comes from `math'
(defvar m31--name-re m31-ml-variable-rx)
(defvar m31--quoted-string-re (rx (seq ?\" (1+ (not (any ?\"))) ?\")))

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
    ("fun" . "FUNCTION")
    ("handle" . "LHANDLE")
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

(defun m31--llet-heuristic nil
  (let*
      ((g (lambda (r)
            (save-match-data
              (save-excursion
                (search-forward-regexp
                 r (save-excursion (end-of-line 1) (point)) 'noerror)))))
       (nxt-let (save-excursion (progn (goto-char (match-end 0)) (funcall g "let"))))
       (nxt-in (funcall g ".*?\\_<=\\_>.*?\\_<in\\_>")))
    (and nxt-in
         (if nxt-let (< nxt-in nxt-let) t))))

(defun m31--local-handle-heuristic nil
  (if
      (save-match-data
        (save-excursion
          (goto-char (match-end 0))
          (forward-comment (point-max)) (looking-at " *|")))
      nil
    t))

(defconst m31--prod-rx
  (regexp-opt
   (let (res)
     (mapcar (lambda (r) (when (equal (cdr r) "PROD") (push (car r) res)))
             m31--reserved)
     res)))
(defconst m31--lambda-rx
  (regexp-opt
   (let (res)
     (mapcar (lambda (r) (when (equal (cdr r) "LAMBDA") (push (car r) res)))
             m31--reserved)
     res)))

(defconst m31--include-rx "\\_<#include_once\\>")

(defun m31--guess-comma nil
  (let* ((limit (max 0 (- (point) 1000)))
         (lst '((m31--prod-rx . "TT_COMMA") (m31--lambda-rx . "TT_COMMA")
                (m31--include-rx . "INCLUDE_COMMA") ("\\[" . "ML_COMMA")
                ("(" . "ML_COMMA") ("\<constant\>" . "CST_COMMA"))))
    (setq lst
          (mapcar
           (lambda (x)
             `(,(save-excursion
                  (save-match-data (search-backward-regexp (eval (car x)) limit 'noerror))) .
               ,(cdr x)))
           lst))

    (cdar (seq-sort
           (lambda (x y) (> (car x) (car y)))
           (seq-filter
            (lambda (x) (car x))
            lst)))))

(defun m31--guess-bar nil
  (let* ((limit (max 0 (- (point) 1000)))
         (last-mlty (save-excursion
                      (save-match-data (search-backward-regexp "mltype" limit 'noerror))))
         (last-handle (save-excursion
                        (save-match-data (search-backward-regexp "handle" limit 'noerror))))
         (last-match (save-excursion
                     (save-match-data (search-backward-regexp "match" limit 'noerror)))))
    (setq last-match (or last-match last-handle))
    (setq last-handle (or last-handle last-match))
    (if (not last-mlty)
        "BAR"
      (if last-handle
          (progn (setq last-handle (max last-handle last-match))
                 (if (> last-mlty last-handle)
                     "MLTY_BAR"
                   "BAR"))
        "MLTY_BAR"))))

(defconst m31--let-rx
  (rx bow (| "now" (seq "let" (? (+ space) "rec"))) eow))

(defconst m31--mltype-rx
  (rx bow (seq "mltype" (? (+ space) "rec")) eow))

(defun m31--guess-and nil
  (let* ((limit (max 0 (- (point) 1000)))
         (last-of (save-excursion
                        (save-match-data (search-backward-regexp "\\<of\\>" limit 'noerror))))
         (last-mlty (save-excursion
                      (save-match-data (search-backward-regexp m31--mltype-rx limit 'noerror))))
         (last-let (save-excursion
                     (save-match-data (search-backward-regexp m31--let-rx limit 'noerror)))))
    (setq last-let (or last-let last-mlty))
    (setq last-mlty (or last-mlty last-let))
    (if (not last-of)
        "AND"
      (if last-mlty
          (progn (setq last-mlty (max last-mlty last-let))
                 (if (> last-of last-mlty)
                     "OF_AND"
                   "AND"))
        "OF_AND"))))

(defconst m31--prefixop-rx
  (eval `(rx (any ,(mapconcat (lambda (c) c) m31-prefixop ""))
             (* (any ,@(mapcar 'string-to-char m31-symbolchars))))))
(defconst m31--infixop-rx
  (eval `(rx (regexp ,(regexp-opt m31-infixop))
             (* (any ,@(mapcar 'string-to-char m31-symbolchars))))))

(defun m31--smie-token (dir)
  (let ((f (cl-case dir ('forward 'looking-at)
                    ('backward (lambda (r) (looking-back r nil t))))))
    (cond
     ((funcall f m31--include-rx) "INCLUDE")
     ((funcall f "(")             (progn (setq m31--in-list-check-backward t) "LPAREN"))
     ((funcall f ")")             (progn (setq m31--in-list-check-forward  t) "RPAREN"))
     ((funcall f "\\[")           "LBRACK")
     ((funcall f "\\]")           "RBRACK")
     ((funcall f ":=")            "COLONEQ")
     ((funcall f "|-")            "VDASH")
     ((funcall f "|")             (m31--guess-bar))
     ((funcall f "\\_<=\\_>")     "EQ")
     ((funcall f "->")            "ARROW")
     ((funcall f "→")             "ARROW")
     ((funcall f "=>\\|⟹\\|⇒")   "DARROW")
     ((funcall f "==\\|≡")        "EQEQ")
     ((funcall f "::")            "INFIXOP")
     ((funcall f (concat ": *\\(" m31-pvar-rx "\\)")) "COLON_PVAR")
     ((funcall f ":")             "COLON")
     ((funcall f ",")             (m31--guess-comma))
     ((funcall f m31-pvar-rx)      "NAME")
     ((funcall f ";")             "SEMICOLON")
     ((funcall f "?")             "NAME")
     ((funcall f "_")             "UNDERSCORE")
     ((funcall f m31--prefixop-rx) "PREFIXOP")
     ((funcall f m31--infixop-rx) "INFIXOP")
     ((funcall f
               ;; there should be a way to figure out the indentation column of the
               ;; current module level, use that instead of ^
               (concat "^\\(:?" m31--let-rx "\\)")) (if (m31--llet-heuristic) "LLET" "TLET"))
     ((funcall f "\\<and\\>")     (m31--guess-and))
     ((funcall f "^handle") (if (m31--local-handle-heuristic) "LHANDLE" "THANDLE"))
     ((funcall f m31--let-rx)      "LLET")
     ((funcall f m31--mltype-rx)   "MLTYPE")
     ((funcall f (rx bow (+ (any digit)) eow)) "NUMERAL")
     ((funcall f m31--name-re)
      (let ((s (buffer-substring-no-properties
                (match-beginning 0) (match-end 0))))
        (or
         (cdr (assoc s m31--reserved))
         "NAME")))
     ((funcall f m31--quoted-string-re) "STRING")
     ((eobp) "EOF")
     ((funcall f ".") "idk"))))


(defcustom m31-indent-basic smie-indent-basic "" :group 'm31)
(defcustom m31-indent-do (/ m31-indent-basic 2) "" :group 'm31)
(defcustom m31-indent-after-with 1 "" :group 'm31)
(defcustom m31-indent-mltype m31-indent-after-with "" :group 'm31)
(defcustom m31-indent-double-arrow 2 "" :group 'm31)

;; sequencing, toplevel-handlers, top-let, #include, dynamic, top-now

(defvar m31-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2

    '((topdirs (topdirs "DO" term)
               (topdirs "TLET" let_clauses)
               (topdirs "DYNAMIC" names "EQ" term)
               (topdirs "NOW" names "EQ" term)
               (topdirs "THANDLE" top_handler_cases "END")
               (topdirs "CONSTANT" comma_names "COLON" term)
               (topdirs "MLTYPE" mlty_defs "END")
               (topdirs "OPERATION" "NAME" "COLON" op_mlsig)
               (topdirs "VERBOSITY" "NUMERAL")
               (topdirs "INCLUDE" includes))

      (includes    ("STRING") (includes "INCLUDE_COMMA" includes))
      (comma_names ("NAME") (comma_names "CST_COMMA" comma_names))

      (op_mlsig (prod_mlty)
                (op_mlsig "ARROW" op_mlsig))

      (mlty_defs   (mlty_def)
                   (mlty_defs "AND" mlty_defs))
      (mlty_def    ("NAME" names "EQ" mlty_def_body))
      (mlty_def_body (mlty)
                     (mlty_constructors))
      (mlty_constructors (mlty_constructors "MLTY_BAR" mlty_constructors)
                         (mlty_constructor))
      (mlty_constructor ("NAME" mlty_constructor_args))
      (mlty_constructor_args ("OF" mltys))
      (mltys (mlty "OF_AND" mltys) (mlty))
      (mlty        (prod_mlty)
                   (prod_mlty "ARROW" mlty)
                   (prod_mlty "DARROW" mlty))
      (prod_mlty   (app_mlty "STAR" prod_mlty))
      (app_mlty    (simple_mlty)
                   ("NAME" simple_mlty))
      (simple_mlty ("LPAREN" mlty "RPAREN")
                   ("JUDGMENT")
                   ("NAME")
                   ("MLUNIT")
                   ("MLSTRING")) ;should really be a list of arguments
      (ml_schema   ("PROD" names "TT_COMMA" mlty)
                   (mlty))

      (top_handler_cases (top_handler_case "BAR" top_handler_cases))

      (top_handler_case  (names "DARROW" term)
                         ;; top_handler_checking creates a conflict. hack:
                         (names "COLON_PVAR" "DARROW" term))

      (let_clauses (let_clauses "AND" let_clauses)
                   (let_clause))

      (let_clause  ("NAME" names "EQ" term)
                   ("NAME" names "COLON" ml_schema "EQ" term)
                   ("NAME" names "DCOLON" term "EQ" term))

      (term     (ty_term)
                ("LLET" let_clauses "IN" term)
                ("ASSUME" assume_clause "IN" term)
                (equal_term "WHERE" simple_term "EQ" term)
                ("MATCH" term "WITH" match_cases "END")
                ("LHANDLE" ascription "WITH" handler_cases "END")
                ;; ("LHANDLE" term "WITH" handler_cases "END")
                ("WITH" lhandle "END")

                (equal_term "SEMICOLON" term)
                (simple_term "COLON" simple_term)
                ;; (app_term "COLON" ty_term)
                )
      (ascription (names "COLON" names))

      (lhandle (term "LHANDLE" term))

      (handler_cases (handler_cases "BAR" handler_cases)
                     (handler_case))
      (handler_case  ("VAL" pattern "DARROW" term)
                     ("NAME" prefix_pattern "DARROW" term)
                     ;; FIXME: should be prefix_patterns but that creates a conflict.
                     ("NAME" prefix_pattern "COLON" pattern "DARROW" term)
                     (binop_pattern "INFIXOP" binop_pattern "COLON" pattern "DARROW" term)
                     (binop_pattern "INFIXOP" binop_pattern "DARROW" term)
                     ("FINALLY" pattern "DARROW" term))

      (pattern       ;; (binop_pattern)
                     ;; (simple_pattern "AS" "NAME")
                     ;; ("VDASH" tt_pattern "COLON" tt_pattern)
                     ;; ("VDASH" tt_pattern)
       (equal_term)
                     )

      (binop_pattern (app_pattern)
                     (binop_pattern "INFIXOP" binop_pattern))
      (app_pattern   (prefix_pattern)
                     ;; FIXME: should be a list of arguments
                     ;; ("PREFIXOP" prefix_pattern)
                     )
      (prefix_pattern (simple_pattern)
                      ("PREFIXOP" prefix_pattern))
      (simple_pattern ("UNDERSCORE")
                      ("NAME")
                      ("LPAREN" comma_patterns "RPAREN")
                      ("LBRACK" comma_patterns "RBRACK"))
      (comma_patterns (pattern)
                      (comma_patterns "ML_COMMA" comma_patterns)
                      )

      (tt_pattern    (equal_tt_pattern)
                     ;; tt_binders
;                     ("LAMBDA" lambda_abstraction "TT_COMMA" tt_pattern)
;                     ("LAMBDA" lambda_abstraction "TT_COMMA" tt_pattern)
                     )

      (match_cases (match_cases "BAR" match_cases)
                   (match_case))
      (match_case (pattern "DARROW" term))

      (assume_clause ("NAME" "COLON" ty_term))

      (ty_term  (equal_term)
                ("PROD" prod_abstraction "TT_COMMA" term)
;                ("LAMBDA" prod_abstraction "TT_COMMA" term)
                ("FUNCTION" names "DARROW" term))

      (prod_abstraction (typed_binders) (names "COLON" ty_term))
      (typed_binders ("LPAREN" typed_binder_clause "RPAREN" typed_binders))
      (typed_binder_clause (names "COLON" ty_term))

      (lambda_abstraction (prod_abstraction))

      (equal_term  (binop_term)
                   (binop_term "EQEQ" binop_term))

      (binop_term  (app_term)
                   (app_term "COLONEQ" binop_term)
                   (binop_term "INFIXOP" binop_term))

      (app_term    (prefix_term)
                   (app_term "NAME" app_term)
                   )

      (prefix_term (simple_term)
                   ("PREFIX" prefix_term))

      (simple_term ("TYPE")
                   ("NAME")
                   ("LPAREN" term "RPAREN")
                   ("LBRACK" comma-terms "RBRACK")
                   ("STRING"))

      (comma-terms (comma-terms "ML_COMMA" comma-terms)
                   (term))

      (names    ("NAME" names)))

     ;; '((assoc "DO" "CONSTANT" "OPERATION" "MLTYPE" "DYNAMIC" "TLET"
     ;;          "TOPDIRECTIVE" "END")
     ;;   (assoc "THANDLE"))
     ;; '((assoc "EQ"))
    '((assoc "AND"))
    '((assoc "DARROW"))
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
      (if (smie-rule-parent-p "LHANDLE" "THANDLE")
          (progn (message "pt: %S, par: %S" (point) smie--parent)
                 (save-excursion
                   (back-to-indentation)
                   `(column . ,(+ (current-column) m31-indent-basic))))
        (smie-rule-parent m31-indent-double-arrow))
      )))

(defun m31--smie-after-comma nil
  (message "after-COMMA, sibling: %S" (smie-rule-sibling-p))
  (if (smie-rule-sibling-p)
      (smie-rule-parent)
    0))

(defun m31-smie-rules (kind token)
  (message "looking at %S : %S, pt: %S" token kind (point))
  (pcase (cons kind token)
    (`(:elem . basic) (message "basic") m31-indent-basic)
                                        ;    (`(,_ . "COMMA") (message "separator-comma") (smie-rule-separator kind))
                                        ;    (`(,_ . "AND") (message "separator-AND") (smie-rule-separator kind))
    ;; (`(:after . "COLONEQ") m31-indent-basic)

    (`(:after . "IN") (message "after-IN, hanging: %S, parent: %S, prev-DO: %S"
                               (smie-rule-hanging-p) smie--parent (smie-rule-prev-p "DO"))
     ;; (when (smie-rule-hanging-p)
       (if (smie-rule-prev-p "DO")
           (smie-rule-parent m31-indent-do)
         (smie-rule-parent))
       ;; )
    )

    (`(:after . "COMMA")
     (m31--smie-after-comma))

    (`(:after . "EQ")
     (when (smie-rule-parent-p "MLTYPE")
       (message "after-EQ parent:MLTYPE , nxt-NAME: %S" (smie-rule-next-p "NAME"))
       (smie-rule-parent
        (+ (if (smie-rule-next-p "NAME") 2 0)
           m31-indent-mltype))))

    (`(:before . "BAR")
     (if (smie-rule-parent-p "MLTYPE")
         (progn (message "before-BAR parent:MLTYPE")
                (smie-rule-parent m31-indent-mltype))
       (message "before-BAR, %S" (smie-rule-prev-p "LHANDLE" "THANDLE" "WITH"))
       (if (smie-rule-prev-p "LHANDLE" "THANDLE" "WITH")
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

    ;; (`(:before . "NAME")
    ;; ;;  nil)
    ;; ;; (`(:x . "x")

    ;;  (progn (message "before-NAME") nil)
    ;;  (if (smie-rule-parent-p "MLTYPE")
    ;;      (progn (message "before-NAME parent:MLTYPE , foo: %S" (smie-rule-prev-p "BAR"))
    ;;             (smie-rule-parent (+ 2 m31-indent-basic)))

    ;;    ;; after an IN we should find the corresponding opening LET.

    ;;    (if (and ;(smie-rule-bolp) & prev = in
    ;;         (message "prev: %S" (save-excursion
    ;;                               (m31--smie-backward-token)))
    ;;         (equal (m31--smie-backward-token) "DARROW") (message "hi"))

    ;;        (save-excursion
    ;;          ;; the IN has an EQ as parent, so go there and find its parent
    ;;          ;; (let (smie--parent) (smie-indent--parent)
    ;;          ;;      (goto-char (cadr (smie-indent--parent)))
    ;;          ;;      (message "parent %S" smie--parent))
    ;;          (let (smie--parent) (smie-indent--parent)
    ;;               (goto-char (cadr (smie-indent--parent)))
    ;;               (message "parent %S" smie--parent))
    ;;          (message "pt %S" (point))
    ;;          (cons 'column (current-column)))
    ;;      (message "backward /= IN") nil))
    ;;  )

    (`(:after . "LHANDLE") (message "after-LHANDLE") m31-indent-basic)

    (`(:before . "LHANDLE")
     (message "before-HANDLE, par: %S, prev: %S"
              (let (smie--parent) (smie-indent--parent))
              (save-excursion (smie-indent-backward-token)))
     (if (and (smie-rule-parent-p "DO") (smie-rule-prev-p "DO"))
         (progn (message "hi") m31-indent-do)
       (when (smie-rule-next-p "BAR")
         (smie-rule-parent))))

    (`(:before . "THANDLE") (message "before-THANDLE") (smie-rule-parent))

    ;; breaking application over lines
    ;; (`(:after . "NAME") (message "after-NAME") m31-indent-basic)

    ;; (`(:before . "LET") (message "before-LET") m31-indent-basic)

    ;; (`(:before . "EQEQ") (message "before-EQEQ") (smie-rule-parent))
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
     (m31--before-darrow))

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


(provide 'andromeda-smie)
;;; andromeda-smie.el ends here
