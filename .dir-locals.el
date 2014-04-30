;; Support for compiling in subdirectories from Emacs. Adapted from Coq source.
((nil
  . ((eval
      . (progn
	  ;; root directory (ending with slash)
	  (let ((tt-root-directory (when buffer-file-name
				      (locate-dominating-file
				       buffer-file-name
				       ".dir-locals.el")))
		(tt-project-find-file
		 (and (boundp 'tt-project-find-file) tt-project-find-file)))
	    ;; tt tags file
	    (setq tags-file-name (concat tt-root-directory "TAGS"))

	    ;; Setting the compilation directory to tt root. This is
	    ;; mutually exclusive with the setting of default-directory
	    ;; below.
	    (unless tt-project-find-file
	      (setq compile-command (concat "make -C " tt-root-directory)))

	    ;; Set default directory to tt root ONLY IF variable
	    ;; tt-project-find-file is non nil. This should remain a
	    ;; user preference and not be set by default. This setting
	    ;; is redundant with compile-command above as M-x compile
	    ;; always CD's to default directory. To enable it add this
	    ;; to your emacs config: (setq tt-project-find-file t)
	    (when tt-project-find-file
	      (setq default-directory tt-root-directory))))
      ))
  ))
