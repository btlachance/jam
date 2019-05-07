#lang racket
(define-values (odd? even?)
  (values (lambda (n) (if (zero? n) #f (even? (- n 1))))
          (lambda (n) (if (zero? n) #t (odd? (- n 1))))))
(define-values () (values))
(odd? 0)
(even? 0)
(odd? 1)
(even? 2)
