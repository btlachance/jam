#lang racket
(require jam)
(provide pl)

(define-language pl
  #:data ([env (environment x V)])

  (e     ::= x (lambda (x ...) e) integer boolean (e e ...)
             (if e e e))
  (x y z ::= variable-not-otherwise-mentioned)
  (v     ::= (lambda (x ...) e) integer boolean
             prim+ prim- prim* primzero?)

  (V ::= {env v})
  (k ::= mt (fn env (e ...) (V ...) k) (sel env e e k)))

(define-metafunction pl
  [(init-env)
   (env-extend
    env
    (+ - * zero?)
    ({env prim+} {env prim-} {env prim*} {env primzero?}))
   (where env (env-empty))])

(define-metafunction pl
  [(apply-op (lambda (x ...) e) env (V ...))
   {(env-extend env (x ...) (V ...)) e}]

  [(apply-op prim+ _ ({_ integer_1} {_ integer_2}))
   {(env-empty) (integer-add integer_1 integer_2)}]

  [(apply-op prim- _ ({_ integer_1} {_ integer_2}))
   {(env-empty) (integer-subtract integer_1 integer_2)}]

  [(apply-op prim* _ ({_ integer_1} {_ integer_2}))
   {(env-empty) (integer-multiply integer_1 integer_2)}]

  [(apply-op primzero? _ ({_ 0}))
   {(env-empty) #t}]

  [(apply-op primzero? _ ({_ v}))
   {(env-empty) #f}])

(define-transition pl
  step
  [--> (x env k)
       (v env_v k)
       (where {env_v v} (env-lookup env x))]

  [--> ((e e_args ...) env k)
       (e env (fn env (e_args ...) () k))]

  [--> ((if e_test e_then e_else) env k)
       (e_test env (sel env e_then e_else k))]

  [--> (v env_v (fn env (e_arg e_args ...) (V ...) k))
       (e_arg env (fn env (e_args ...) ({env_v v} V ...) k))]

  [--> (v env_v (fn _ () (V ...) k))
       (e env_e k)
       (where ({env_op v_op} V ...) (reverse ({env_v v} V ...)))
       (where {env_e e} (apply-op v_op env_op (V ...)))]

  [--> (#f _ (sel env _ e_else k))
       (e_else env k)]

  [--> (v _ (sel env e_then _ k))
       (e_then env k)])

(define-evaluator pl
  eval
  #:load [--> e (e (init-env) mt)]
  #:unload [--> (v _ mt) v]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (current-test-language pl)
  (test-equal (run-eval (+ 1 2)) 3)

  (test-equal (run-eval
               ((lambda (fib) (fib fib 10))
                (lambda (rec n)
                  (if (zero? n)
                      0
                      (if (zero? (- n 1))
                          1
                          (+ (rec rec (- n 1))
                             (rec rec (- n 2))))))))
              55)
  (jam-test))

(module+ main
  (require syntax/location)
  (define dest (syntax-source-directory #'here))
  (jam-run pl eval
    #:dest/delete (build-path dest "pycketlite")
    #:translate? #f))
