#lang racket
(require syntax/location)
(provide blob-root)

;; blob-root : path
;; The path that all built-in Python files are relative to
(define blob-root (syntax-source-directory #'here))
