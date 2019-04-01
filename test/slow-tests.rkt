#lang racket
(require jam "lang-tests.rkt" syntax/location)

(module+ main
  (define dest (build-path (syntax-source-directory #'here) "jamtest-lc-env"))
  (jam-build lc-env eval
             #:dest/delete dest)
  (jam-run lc-env eval
    #:path dest
    #:prompt? #f))

(module+ test
  (require rackunit)
  (when (getenv "JAM_SLOW_TESTS")
    (check-match
     (let ([output (open-output-string)])
       (parameterize ([current-input-port (open-input-string "((lambda (x) 10) 0)")]
                      [current-output-port output])
         (list (system* (find-executable-path "racket") (quote-source-file))
               (string-trim (get-output-string output) #rx"\r?\n" #:left? #f))))
     (list #t "10"))))
