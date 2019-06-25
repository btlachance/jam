#;(testout "#t\n#t\n()\n")
#lang racket
(define x 0)
(define (inc) (set! x (+ x 1)))
(define (dec) (set! x (- x 1)))

(inc)
(dec)
(inc)
(inc)
(write (equal? x 2)) (newline)

(dec)
(dec)
(dec)
(write (equal? x -1)) (newline)
