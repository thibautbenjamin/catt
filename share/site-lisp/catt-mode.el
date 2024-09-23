;; catt-mode.el -- CATT major emacs mode -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Thibaut Benjamin

;; Author: Thibaut Benjamin <thibaut.benjamin@gmail.com>
;; Version: 0.1
;; Package-Requires: ((emacs "27.1"))
;; Keywords: convenience
;; Homepage: https://github.com/thibautbenjamin/catt

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(defvar catt-font-lock-keywords
  '(
    ("#.*" . 'font-lock-comment-face)
    ("\\<\\(let\\|check\\|set\\|coh\\|fcoh\\|hyp\\|eval\\|env\\)\\>\\|:\\|=" . font-lock-keyword-face)
    ("\\<\\(Hom\\|Type\\)\\>\\|->" . font-lock-builtin-face)
    ;; ("\\<\\(\\)\\>" . font-lock-constant-face)
    ("\\<let[ \t]+\\([^ (=]*\\)" 1 'font-lock-function-name-face)
    )
  )

(defvar catt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?# "<" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for CATT major mode.")

(defvar catt-tab-width 4)

(define-derived-mode catt-mode prog-mode
  "CATT" "Major mode for CATT files."
  :syntax-table catt-mode-syntax-table
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "#+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(catt-font-lock-keywords))
  (setq mode-name "CATT")
  )


;;;###autoload
(add-to-list 'auto-mode-alist '("\\.catt\\'" . catt-mode))

(provide 'catt-mode)
;;; catt-mode.el ends here
