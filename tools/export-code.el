;;; export-code.el --- Highlight the Magma blocks of the org file for the web page  -*- lexical-binding: t -*-

;; Usage: emacs --batch -Q -l tools/export-code.el -f paper/export-code ORG OUTDIR
;;
;; For every named Magma block of ORG, writes OUTDIR/NAME.html, the block as
;; Org's HTML exporter renders it (htmlize, with CSS classes that org-css.css
;; colors, as in the web book), and OUTDIR/NAME.meta, the block's statement
;; label (header argument :label), the file it tangles to, whether the box
;; starts open (:open t) and its title (:title); and OUTDIR/NAME.prose.html,
;; the org prose just above the block, which explains it.  tools/tex2html.py
;; puts them on the page.
;;
;; Noweb references are expanded, so that the code shown is the code that
;; runs; a block that is only a list of references is skipped (:html no).

(require 'package)
(setq package-user-dir (expand-file-name "~/.emacs.d/elpa"))
(package-initialize)
(require 'org)
(require 'ox-html)
(require 'ob-tangle)
(require 'magma-mode nil t)
(require 'htmlize nil t)

(add-to-list 'org-src-lang-modes '("magma" . magma))
(setq org-html-htmlize-output-type 'css
      org-export-with-sub-superscripts '{}
      org-confirm-babel-evaluate nil)

(defun paper/export-code ()
  (let* ((org (expand-file-name (pop command-line-args-left)))
         (outdir (file-name-as-directory (expand-file-name (pop command-line-args-left))))
         (count 0))
    (unless (featurep 'htmlize)
      (error "htmlize is not installed: the code would not be highlighted"))
    (unless (featurep 'magma-mode)
      (error "magma-mode is not installed: the code would not be highlighted"))
    (make-directory outdir t)
    (with-current-buffer (find-file-noselect org)
      (org-babel-map-src-blocks nil
        (let* ((info (org-babel-get-src-block-info 'no-eval))
               (name (nth 4 info))
               (params (nth 2 info)))
          (when (and (equal lang "magma") name
                     (not (equal (format "%s" (cdr (assq :html params))) "no"))
                     (or (not (string-prefix-p "setup-" name))
                         (equal (format "%s" (cdr (assq :html params))) "t")))
            (let* ((body (org-babel-expand-noweb-references info))
                   (tangle (cdr (assq :tangle params)))
                   (label (cdr (assq :label params)))
                   (open (cdr (assq :open params)))
                   (title (cdr (assq :title params)))
                   (html (org-export-string-as
                          (concat "#+begin_src magma\n"
                                  (org-escape-code-in-string body)
                                  "\n#+end_src\n")
                          'html t '(:with-toc nil :section-numbers nil))))
              (with-temp-file (expand-file-name (concat name ".html") outdir)
                (insert html))
              ;; the org prose between the previous block (or heading) and this
              ;; one explains the check; it goes into the box, above the code
              (let* ((begin (org-element-property :begin (org-element-at-point)))
                     (start (save-excursion
                              (goto-char begin)
                              (if (re-search-backward "^\\(\\*+ \\|[ \t]*#\\+end_src\\)" nil t)
                                  (line-beginning-position 2)
                                (point-min))))
                     (prose (string-trim (buffer-substring-no-properties start begin))))
                (with-temp-file (expand-file-name (concat name ".prose.html") outdir)
                  (unless (string-empty-p prose)
                    (insert (org-export-string-as prose 'html t '(:with-toc nil))))))
              (with-temp-file (expand-file-name (concat name ".meta") outdir)
                (insert (format "label\t%s\nfile\t%s\nopen\t%s\ntitle\t%s\n"
                                (or label "")
                                (if (and tangle (not (equal tangle "no"))) tangle "")
                                (if open (format "%s" open) "")
                                (or title ""))))
              (setq count (1+ count)))))))
    (message "export-code: %d Magma blocks written to %s" count outdir)))

;;; export-code.el ends here
