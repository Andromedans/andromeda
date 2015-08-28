;; Support for compiling in subdirectories from Emacs. Adapted from Coq source.
((nil
  (eval . (setq default-directory (locate-dominating-file buffer-file-name ".dir-locals.el"))))
 (tuareg-mode
  (show-trailing-whitespace . t))
 (m31-mode
  (show-trailing-whitespace . t)))
