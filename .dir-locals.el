;; Support for compiling in subdirectories from Emacs. Adapted from Coq source.
((nil
  . ((eval
      . (progn
          ;; root directory (ending with slash)
          (let ((m31-root-directory
                 (when buffer-file-name
                   (locate-dominating-file
                    buffer-file-name
                    ".dir-locals.el")))
                (m31-project-find-file
                 (and (boundp 'm31-project-find-file) m31-project-find-file)))

            ;; m31 tags file
            (when m31-root-directory
              (setq tags-file-name (concat m31-root-directory "TAGS"))

              ;; Setting the compilation directory to m31 root. This is
              ;; mutually exclusive with the setting of default-directory
              ;; below.
              (if (not m31-project-find-file)
                  (setq compile-command (concat "make -C " m31-root-directory))

                ;; Set default directory to m31 root ONLY IF variable
                ;; m31-project-find-file is non nil. This should remain a
                ;; user preference and not be set by default. This setting
                ;; is redundant with compile-command above as M-x compile
                ;; always CD's to default directory. To enable it add this
                ;; to your emacs config: (setq m31-project-find-file t)
                (setq default-directory m31-root-directory)))
            (setq m31-executable (concat m31-root-directory "andromeda.byte")))))))
 (tuareg-mode
  (show-trailing-whitespace . t))
 (m31-mode
  (show-trailing-whitespace . t)))
