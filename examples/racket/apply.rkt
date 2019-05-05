#lang racket
(apply + 1 (list 2))
(apply + (list 3 4))
(apply + 5 6 null)

(define (mylist . x) x)
(apply mylist null)
(apply mylist 1 null)
(apply mylist 1 (list 2))
