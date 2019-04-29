#lang racket
(define (even? n)
  (if (zero? n)
      #t
      (odd? (- n 1))))
(define (odd? n)
  (if (zero? n)
      #f
      (even? (- n 1))))
(even? 10)
