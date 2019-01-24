#lang racket
(require jam/private/python/util)
(provide python-file python-directory)

;; python-file : path -> path
;; Given a relative path p, returns the path of the built-in python
;; file corresponding to p. Raises an error if no built-in file exists
(define (python-file path)
  (define maybe-file (build-path blob-root path))
  (unless (file-exists? maybe-file)
    (error 'python-file "path does not correspond to a built-in Python file\n\
  path: ~a" maybe-file))
  maybe-file)

(define (python-directory path)
  (define maybe-dir (build-path blob-root path))
  (unless (directory-exists? maybe-dir)
    (error 'python-directory "path does not correspond to a built-in Python directory\n\
  path: ~a" maybe-dir))
  maybe-dir)

(module+ test
  (require rackunit)
  (check-not-exn (lambda () (python-file "pycket_json_adapter.py")))
  (check-exn #rx"built-in Python file" (lambda () (python-file "all-your-base.py")))
  (check-not-exn (lambda () (python-directory "pycket")))
  (check-exn #rx"built-in Python directory" (lambda () (python-directory "packet"))))
