#lang racket
(require jam)
(provide lc-env)

(define-language lc
  (e ::= x (lambda (x ...) e) integer (e e ...))
  (x y z ::= variable-not-otherwise-mentioned)
  (v ::= (lambda (x ...) e) integer))

(define-metafunction lc
  [(cons x y)
   (x y)]

  [(cons x y z z_rest ...)
   (x rest)
   (where (name rest _) (cons y z z_rest ...))])

;; XXX delaying this for now since it means adding side conditions
;; (define-metafunction lc
;;   [(lookup x {(y V) _ ...}) V
;;    (side-condition (atom-equal? (term x) (term y)))]
;;   [(lookup x {_ (y V) ...}) (lookup x {(y V) ...})])

(module+ test
  (require (submod ".."))
  (current-test-language lc)

  (test-equal (cons a b) (a b))
  (test-equal (cons a e i) (a (e i)))
  (test-not-equal (cons a b) (a c))

  (let ([dest (build-path (find-system-path 'temp-dir) "jam-lc")])
    (when (directory-exists? dest)
      (delete-directory/files dest))
    (jam-test #:dest/delete dest)))


(define-language lc-env
  #:data ([env (environment x V)])

  (e     ::= x (lambda (x ...) e) integer boolean (e e ...)
             (if e e e))
  (x y z ::= variable-not-otherwise-mentioned)
  (v     ::= (lambda (x ...) e) integer boolean prim+)

  (V ::= {env v})
  (k ::= mt (fn env (e ...) (V ...) k) (sel env e e k)))

(define-metafunction lc-env
  [(init-env)
   (env-extend1
    env
    +
    {env prim+})
   (where env (env-empty))])

(define-metafunction lc-env
  [(reverse-onto () (name result _)) result]
  [(reverse-onto ((name hd _) (name rest _) ...) ((name onto _) ...))
   (reverse-onto (rest ...) (hd onto ...))])

(define-metafunction lc-env
  [(step0 x env k)
   (v env_v k)
   (where {env_v v} (env-lookup env x))]

  [(step0 (e e_args ...) env k)
   (e env (fn env (e_args ...) () k))]

  [(step0 (if e_test e_then e_else) env k)
   (e_test env (sel env e_then e_else k))]

  [(step0 v env_v (fn env (e_arg e_args ...) (V ...) k))
   (e_arg env (fn env (e_args ...) ({env_v v} V ...) k))]

  [(step0 v env_v (fn _ () (V ...) k))
   (e env_e k)
   (where ({env_op v_op} V ...) (reverse-onto ({env_v v} V ...) ()))
   (where {env_e e} (apply-op v_op env_op (V ...)))]

  [(step0 #f _ (sel env _ e_else k))
   (e_else env k)]

  [(step0 v _ (sel env e_then _ k))
   (e_then env k)])

(define-metafunction lc-env
  [(apply-op (lambda (x ...) e) env (V ...))
   {(env-extend env (x ...) (V ...)) e}]

  [(apply-op prim+ _ ({_ integer_1} {_ integer_2}))
   {(env-empty) (integer-add integer_1 integer_2)}])

(define-metafunction lc-env
  [(bare {_ v}) v])

(define-metafunction lc-env
  [(eval0 e)
   (eval0 (e (init-env) mt))]

  [(eval0 (v _ mt))
   v]

  [(eval0 (e env k))
   (eval0 (step0 e env k))])

(module+ test
  (current-test-language lc-env)

  (test-equal (reverse-onto () ())
              ())

  (test-equal (reverse-onto (1 2 3) ())
              (3 2 1))

  (test-equal (reverse ())
              ())

  (test-equal (reverse (1 2 3))
              (3 2 1))

  (test-equal (eval0 5)
              5)

  (test-equal (eval0 (lambda (x) 10))
              (lambda (x) 10))

  (test-equal (eval0 ((lambda () 13)))
              13)

  (test-equal (eval0 ((lambda (x) x) 0))
              0)

  (test-equal (eval0 ((lambda (x) 10) 11))
              10)

  (test-equal (eval0 ((lambda (x) x) (lambda (y) y)))
              (lambda (y) y)))

(define-transition lc-env
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

(define-evaluator lc-env
  eval
  #:load [--> e (e (init-env) mt)]
  #:unload [--> (v _ mt) v]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (current-test-language lc-env)
  (test-equal (run-eval 5)
              5)
  (test-equal (run-eval (((lambda (x) (lambda (y) x)) 10) 11))
              10)
  (test-not-equal (run-eval ((lambda (y) y) 10))
                  11)
  (test-equal (run-eval (lambda (x) x))
              (lambda (x) x))

  (test-equal (run-eval (if 0 1 2)) 1)
  (test-equal (run-eval (if #f 1 2)) 2)
  (test-equal (run-eval (if #t 1 2)) 1)

  (test-equal (bare (apply-op prim+ (env-empty) ({(env-empty) 5} {(env-empty) 4})))
              9)

  (test-not-equal (run-eval +) +)
  (test-equal (run-eval (+ 11 12)) 23)

  (jam-test
   #:dest/delete (build-path (find-system-path 'temp-dir) "jam-lc-env")))

(define-language bool)
(define-metafunction bool
  [(swap #t) #f]
  [(swap #f) #t])
(module+ test
  (current-test-language bool)
  (test-equal (#t 5) (#t 5))
  (test-not-equal #f #t)
  (test-equal (swap #t) #f)
  (test-equal (swap #f) #t)
  (jam-test))