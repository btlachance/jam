#lang racket
(define (newline) (write-string "\n"))

(define (time-apply f vs)
    (let* ([then (current-inexact-milliseconds)]
           [results (call-with-values (lambda () (apply f vs)) list)]
           [now (current-inexact-milliseconds)])
      (define delta (inexact->exact (- now then)))
      (values results delta 0 delta)))
