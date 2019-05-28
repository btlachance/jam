#lang racket
(define (newline) (write-string "\n"))

(define (equal? v1 v2)
  (if (and (number? v1) (number? v2))
      (= v1 v2)
      (if (and (boolean? v1) (boolean? v2))
          (or (and v1 v2) (and (not v1) (not v2)))
          (if (and (string? v1) (string? v2))
              (string=? v1 v2)
              (if (and (null? v1) (null? v2))
                  #t
                  (if (and (symbol? v1) (symbol? v2))
                      (symbol=? v1 v2)
                      (if (and (pair? v1) (pair? v2))
                          (and (equal? (car v1) (car v2))
                               (equal? (cdr v1) (cdr v2)))
                          ;; XXX need vectors, ports
                          (raise))))))))

(define (time-apply f vs)
    (let* ([then (current-inexact-milliseconds)]
           [results (call-with-values (lambda () (apply f vs)) list)]
           [now (current-inexact-milliseconds)])
      (define delta (inexact->exact (- now then)))
      (values results delta 0 delta)))

(define (write v)
  (if (string? v)
      (write-string v)
      (if (number? v)
          (write (number->string v))
          (if (boolean? v)
              (if v (write "#t") (write "#f"))
              (if (symbol? v)
                  (write (symbol->string v))
                  (raise))))))

(define (display v)
  (if (string? v)
      (write v)
      (raise)))

(define (fprintf out format . vs)
  ;; XXX This is the format-string for time in the pycket/wrap language
  (if (equal? format "RESULT-cpu: ~a.0\nRESULT-gc: ~a.0\nRESULT-total: ~a.0\n")
      (begin
        (write "RESULT-cpu: ")
        (write (car vs))
        (write ".0\n")
        (write "RESULT-gc: ")
        (write (car (cdr vs)))
        (write ".0\n")
        (write "RESULT-total: ")
        (write (car (cdr (cdr vs))))
        (write ".0\n"))
      (raise)))
