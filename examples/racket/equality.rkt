#lang racket
(equal? "hello" "world")
(equal? 1 1)
(equal? 1.0 1.0)
(equal? (cons 1 2) (cons 3 4))
(equal? (cons 1 2) (cons 1 2))
(equal? #t #t)
(equal? #t #f)
(equal? #f #f)

(equal? 'a 'a)
(equal? 'a 'b)

(equal? (vector) (vector))
(equal? (vector 1) (vector 1))
(not (equal? (vector 1) (vector 2)))
