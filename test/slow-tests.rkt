#lang racket
(require jam "lang-tests.rkt" syntax/location)

(module+ main
  (define dest (syntax-source-directory #'here))
  (jam-run lc-env eval
    #:dest/delete (build-path dest "jamtest-lc-env")
    #:translate? #f))

(module+ test
  (require rackunit)
  (when (getenv "JAM_SLOW_TESTS")
    ;; XXX Need some way to either remove the prompt from the output
    ;; or set the prompt not to print in the first place.
    (check-match
     (let ([output (open-output-string)])
       (parameterize ([current-input-port (open-input-string "((lambda (x) 10) 0)")]
                      [current-output-port output])
         (list (system* (find-executable-path "racket") (quote-source-file))
               (get-output-string output))))
     (list #t "10"))))
