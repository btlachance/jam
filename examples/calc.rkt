#lang racket
(require jam)

(define-language arith
  (e ::= (op e e) (quote integer))
  (op ::= + * -)
  (v ::= integer)
  (k ::= mt (opk1 op e k) (opk2 op v k)))

(define-metafunction arith
  [(apply-op + v_1 v_2)
   (integer-add v_1 v_2)]

  [(apply-op - v_1 v_2)
   (integer-subtract v_1 v_2)]

  [(apply-op * v_1 v_2)
   (integer-multiply v_1 v_2)])

(define-transition arith
  step

  [--> ((op e_left e_right) k)
       (e_left (opk1 op e_right k))]
  [--> ((quote integer) k)
       (integer k)]

  [--> (v (opk1 op e k))
       (e (opk2 op v k))]
  [--> (v_right (opk2 op v_left k))
       ((apply-op op v_left v_right) k)])

(define-evaluator arith
  eval

  #:load [--> e (e mt)]
  #:unload [--> (v mt) v]
  #:transition step
  #:control-string [(e _) e])

(module+ test
  (current-test-language arith)
  (test-equal (run-eval (+ '1 '2)) 3)
  (jam-test))
