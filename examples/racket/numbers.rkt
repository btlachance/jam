#lang racket
(+ 1 2)
(+ 1.0 2.0)

(- 1 1)
(- 1.0 5.0)

(* 4 12)
(* 11.5 12.1)

(zero? 0)
(zero? 0.0)
(zero? -0.0)

(exact-integer? 0)
(exact-integer? #t)
(exact-integer? 0.0)

(inexact? 1.0)
(inexact? 0)

(exact->inexact 1.0)
(exact->inexact 1)

(inexact->exact 1.0)
(inexact->exact 1)
