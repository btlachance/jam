#lang racket
(require json)
(provide term-to-json)

(define (term-to-json t)
  (match t
    [(? exact-integer? n)
     ;; XXX Double-check the bounds here. The JSONDecoder will decode
     ;; a JSON integer as an RPython int, which is bounded by the
     ;; machine size.

     ;; XXX I don't even have biginteger yet in the Jam runtime. Need
     ;; to nail that down. (Also, RPython knows what its machine
     ;; integer size is, so maybe checking whether a Jam integer is
     ;; big or not should come from that side, and all Jam integers
     ;; get stringified?)
     (if (fixnum? n)
         (hash 'integer n)
         (hash 'biginteger (number->string n)))]

    ;; XXX ...why rule out nan/infinities?
    [(and (? flonum? n) (not (? infinite?) (? nan?)))
     (hash 'real n)]

    [(? string? s)
     (hash 'string s)]

    [(? symbol? s) (hash 'symbol (symbol->string s))]

    [(? boolean? b) (hash 'boolean b)]

    ['() 'null]

    [(cons t ts) (hash 'pair (list (term-to-json t) (term-to-json ts)))]))

