#lang racket
(vector)
(vector 1)
(vector 1 2 3)
(vector-immutable)
(vector-immutable 0)
(vector-immutable 2 1 0)

(vector-length (vector))
(vector-length (vector 9))
(vector-length (vector 10 11 12))
(vector-length (vector-immutable))
(vector-length (vector-immutable 9))
(vector-length (vector-immutable 10 11 12))

(vector-ref (vector 1) 0)
(vector-ref (vector 4 5 6) 2)
(vector-ref (vector-immutable 1) 0)
(vector-ref (vector-immutable 4 5 6) 2)

(define v (vector #t))
(vector-set! v 0 123)
(vector-ref v 0)
