;; Support for compiling in subdirectories from Emacs. Adapted from Coq source.
((nil
  . ((eval
      . (progn
          ;; root directory (ending with slash)
          (let ((m31-root-directory
                 (when buffer-file-name
                   (locate-dominating-file buffer-file-name ".dir-locals.el")))
                (m31-project-find-file
                 (and (boundp 'm31-project-find-file) m31-project-find-file)))

            ;; m31 tags file
            (when m31-root-directory
              (setq tags-file-name (concat m31-root-directory "TAGS"))
              (make-local-variable 'compilation-search-path)
              (add-to-list 'compilation-search-path m31-root-directory)
              ;; Setting the compilation directory to m31 root. This is
              ;; mutually exclusive with the setting of default-directory
              ;; below.
              (if (not m31-project-find-file)
                  (setq compile-command (concat "make -C " m31-root-directory)))
              )
            (setq m31-executable (concat m31-root-directory "andromeda.native")))))))
 (tuareg-mode
  (show-trailing-whitespace . t))
 (m31-mode
  (show-trailing-whitespace . t)))
