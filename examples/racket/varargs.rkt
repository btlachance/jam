#lang racket
(define (mylist . x) x)
(mylist)
(mylist 1 2 3)
(mylist 1 #f 2 #t 3 #f)

(define (list2+ x1 x2 . y)
  (cons x1 (cons x2 y)))
(list2+ #t #f 1 2 3)
(list2+ #f #t 1 2)

