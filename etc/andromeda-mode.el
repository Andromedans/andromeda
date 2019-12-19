; Emacs mode for andromeda, derived from OCaml tuareg-mode. See LICENSE.txt
; for licensing information.
;
; This code could be much improved.
;
; To use the andromeda-mode, put this file somewhere and add something like the following
; in your .emacs file:
;
;   (autoload 'andromeda-mode "<andromeda-mode-install-dir>/etc/andromeda-mode" "Major mode for editing Andromeda files" t)
;   (setq auto-mode-alist (cons '("\\.andromeda$" . andromeda-mode) auto-mode-alist))

(defvar andromeda-keywords
  '(
  "_atom"
  "abstract"
  "and"
  "as"
  "boundary"
  "by"
  "congruence"
  "context"
  "convert"
  "derive"
  "end"
  "exception"
  "external"
  "fresh"
  "fun"
  "try"
  "handler"
  "in"
  "include"
  "let"
  "match"
  "mlforall"
  "mltype"
  "module"
  "natural"
  "occurs"
  "of"
  "open"
  "operation"
  "raise"
  "rec"
  "ref"
  "rule"
  "require"
  "struct"
  "val"
  "verbosity"
  "when"
  "with"
))

(defvar andromeda-constants
  '(
  "false"
  "true"
  "type"
  ))

(defvar andromeda-types
  '(
  "derivation"
  "judgement"
  "judgment"
  "mlstring"
  "mlunit"
  ))

(defvar andromeda-tab-width 2 "Width of tab for Andromeda mode")

(defvar andromeda-font-lock-defaults
    `((
      ;; stuff between "
       ("\"\\.\\*\\?" . font-lock-string-face)
      ;; prefix and infix operators, can be improved
       ("+\\|,\\|;" . font-lock-keyword-face)
       ( ,(regexp-opt andromeda-keywords 'words) . font-lock-keyword-face)
       ( ,(regexp-opt andromeda-types 'words) . font-lock-type-face)
       ( ,(regexp-opt andromeda-constants 'words) . font-lock-constant-face)
       )))

(define-derived-mode andromeda-mode
  tuareg-mode
  "Andromeda"
  "Major mode for Andromeda (rudimentary)."

  (setq font-lock-defaults andromeda-font-lock-defaults)

;  (when andromeda-tab-width (setq tab-width andromeda-tab-width))
;
;  (setq comment-start "(*")
;  (setq comment-end "*)")
)

(provide 'andromeda-mode)
