;;; andromeda-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads nil "andromeda" "andromeda.el" (21878 62142 236933
;;;;;;  263000))
;;; Generated autoloads from andromeda.el

(autoload 'andromeda-mode "andromeda" "\
Major mode for editing Andromeda files.

Useful commands:
C-c C-.          m31-send-buffer-up-to-point
C-c .            m31-send-buffer-up-to-point
C-c C-b          m31-send-buffer
C-c C-l          m31-send-buffer

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("\\.m31\\'" . andromeda-mode))

(defvar m31-executable (let ((d (locate-dominating-file (or buffer-file-name default-directory) "andromeda.byte"))) (if d (concat d "andromeda.byte") "andromeda")) "\
The name of the Andromeda executable")

(custom-autoload 'm31-executable "andromeda" t)

(defvar m31-arguments "" "\
The `m31-executable' will be called with these arguments")

(custom-autoload 'm31-arguments "andromeda" t)

(autoload 'm31-send-file "andromeda" "\


\(fn FN)" t nil)

(autoload 'm31-send-buffer "andromeda" "\
Send the current buffer to Andromeda

\(fn)" t nil)

(autoload 'm31-send-buffer-up-to-point "andromeda" "\


\(fn)" t nil)

;;;***

(provide 'andromeda-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; andromeda-autoloads.el ends here
