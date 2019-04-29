#lang racket
(define (fact n)
  (if (zero? n)
      1
      (* n (fact (- n 1)))))
(fact 10)
