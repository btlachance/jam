#lang racket
(require jam)

(define-language impcore
  #:data ([xi rho (environment x v)]
          [phi (environment x f)])

  (P ::= (d ...))

  (d ::= (val x e)
         (define x (x ...) e)
         e)

  (e ::= x (int v) (x e ...) (if e e e)
         (while e e) (set x e) (begin e ...))

  (x ::= variable-not-otherwise-mentioned)
  (v ::= integer)
  (f ::= (function (x ...) e) prim)
  (prim ::= #%+ #%- #%* #%/)

  (k ::=
     (valk x P)
     (appk f (e ...) (v ...) k)
     (poplocalenv rho k)
     (ifk e e k)
     (whilek e e k)
     (setk-xi x k)
     (setk-rho x k)
     (begink (e e ...) k))

  (r ::= (last-result v)
         (no-result)))

(define-metafunction impcore
  [(apply-prim #%+ v_1 v_2) (integer-add v_1 v_2)]
  [(apply-prim #%- v_1 v_2) (integer-subtract v_1 v_2)]
  [(apply-prim #%* v_1 v_2) (integer-multiply v_1 v_2)]
  [(apply-prim #%/ v_1 v_2) (integer-divide v_1 v_2)])

(define-metafunction impcore
  [(initial-functions) (phi-extend (phi-empty)
                                   (  +   -   *   /)
                                   (#%+ #%- #%* #%/))])

(define-metafunction impcore
  [(begink* () k) k]
  [(begink* (e ...) k) (begink (e ...) k)])

(define-metafunction impcore
  [(poplocalenv* _ (poplocalenv rho k))
   (poplocalenv* rho k)]

  [(poplocalenv* rho k)
   (poplocalenv rho k)])

(define-transition impcore
  step

  [--> (((val x e) d ...) xi phi _)
       (e xi phi (rho-empty) (valk x (d ...)))]

  [--> (((define x_f (x ...) e) d ...) xi phi_0 r)
       ((d ...) xi phi_1 r)
       (where phi_1 (phi-extend1 phi_0 x_f (function (x ...) e)))]

  [--> ((e d ...) xi phi _)
       (e xi phi (rho-empty) (valk it (d ...)))]

  [--> (x xi phi rho k)
       (v xi phi rho k)
       (where #t (rho-bound? rho x))
       (where v (rho-lookup rho x))]

  [--> (x xi phi rho k)
       (v xi phi rho k)
       (where #f (rho-bound? rho x))
       (where #t (xi-bound? xi x))
       (where v (xi-lookup xi x))]

  [--> ((int v) xi phi rho k)
       (v xi phi rho k)]

  [--> ((x) xi phi rho k)
       (e xi phi (rho-empty) (poplocalenv* rho k))
       (where #t (phi-bound? phi x))
       (where (function () e) (phi-lookup phi x))]

  [--> ((x e e_rest ...) xi phi rho k)
       (e xi phi rho (appk (phi-lookup phi x) (e_rest ...) () k))
       (where #t (phi-bound? phi x))]

  [--> ((if e_test e_then e_else) xi phi rho k)
       (e_test xi phi rho (ifk e_then e_else k))]

  [--> ((while e_test e_body) xi phi rho k)
       (e_test xi phi rho (whilek e_test e_body k))]

  [--> ((set x e) xi phi rho k)
       (e xi phi rho (setk-rho x k))
       (where #t (rho-bound? rho x))]

  [--> ((set x e) xi phi rho k)
       (e xi phi rho (setk-xi x k))
       (where #f (rho-bound? rho x))
       (where #t (xi-bound? xi x))]

  [--> ((begin) xi phi rho k)
       (0 xi phi rho k)]

  [--> ((begin e e_rest ...) xi phi rho k)
       (e xi phi rho (begink* (e_rest ...) k))]

  [--> (v xi phi rho (valk x P))
       (P (xi-extend1 xi x v) phi (last-result v))]

  [--> (v xi phi rho (appk f (e e_rest ...) (v_rest ...) k))
       (e xi phi rho (appk f (e_rest ...) (v v_rest ...) k))]

  [--> (v xi phi rho (appk prim () (v_rest ...) k))
       (v_result  xi phi rho k)
       (where (v ...) (reverse (v v_rest ...)))
       (where v_result (apply-prim prim v ...))]

  [--> (v xi phi rho (appk (function (x ...) e) () (v_rest ...) k))
       (e xi phi rho_body (poplocalenv* rho k))
       (where (v ...) (reverse (v v_rest ...)))
       (where #t (same-length? (x ...) (v ...)))
       (where rho_body (rho-extend (rho-empty) (x ...) (v ...)))]

  [--> (v xi phi _ (poplocalenv rho k))
       (v xi phi rho k)]

  [--> (v xi phi rho (ifk e_then _ k))
       (e_then xi phi rho k)
       (where #f (integer-= v 0))]

  [--> (0 xi phi rho (ifk _ e_else k))
       (e_else xi phi rho k)]

  [--> (v xi phi rho (whilek e_test e_body k))
       (e_body xi phi rho (begink* (e_test) (whilek e_test e_body)))
       (where #f (integer-= v 0))]

  [--> (0 xi phi rho (whilek _ _ k))
       (0 xi phi rho k)]

  [--> (v xi phi rho (setk-xi x k))
       (v (xi-extend1 xi x v) phi rho k)]

  [--> (v xi phi rho (setk-rho x k))
       (v xi phi (rho-extend1 rho x v) k)]

  [--> (v xi phi rho (begink (e e_rest ...) k))
       (e xi phi rho (begink* (e_rest ...) k))])

(define-metafunction impcore
  [(unload-result (last-result v)) v]
  [(unload-result (no-result)) #f])

(define-evaluator impcore
  eval

  #:load [--> P (P (xi-empty) (initial-functions) (no-result))]
  #:unload [--> (() xi phi r) (unload-result r)]
  #:transition step
  #:control-string [(e xi phi rho k) e])

(module+ test
  (current-test-language impcore)
  (test-equal (run-eval ()) #f)
  (test-equal (run-eval ((define f (x) x))) #f)
  (test-equal (run-eval ((int 0)))
              0)
  (test-equal (run-eval ((int 0)
                         it
                         it
                         it))
              0)
  (test-equal (run-eval ((define second (x y) y)
                         (second (int 1) (int 2))))
              2)
  (test-equal (run-eval ((val x (int 0))
                         (define f (x)
                           (begin
                             (set x (int 1))
                             x))
                         (f (int 2))
                         x))
              0)
  (test-equal
   ;; test poplocalenv* dropping the right environment for tail calls
   (run-eval ((val x (int 5))
              (define g (x) x)
              (define f (x)
                (g (set x (+ x (int 1)))))
              (+ (f (int 10)) x)))
   16)
  (test-equal (run-eval ((+ (int 1) (int 2))))
              3)
  (jam-test))
