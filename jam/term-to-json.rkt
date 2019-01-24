#lang racket
(require json)
(provide term-to-json)

(define (term-to-json t)
  (match t
    [(? exact-integer? n)
     ;; XXX Double-check the bounds here. The JSONDecoder will decode
     ;; a JSON integer as an RPython int, which is bounded by the
     ;; machine size.
     (if (fixnum? n)
         (hash 'integer n)
         (hash 'biginteger (number->string n)))]

    [(? symbol? s) (hash 'symbol (symbol->string s))]

    ['() 'null]

    [(cons t ts) (hash 'pair (list (term-to-json t) (term-to-json ts)))]))

