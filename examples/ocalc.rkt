#lang racket
(require jam)

(define-language ocalc
  #:data ([env (environment var v)])

  (e ::= var l (quote c) emptyobj (app e e) (ifz e e e) (respond e var e)
         (send e var))

  (v ::= (clo l env) c (obj env))

  (var ::= variable-not-otherwise-mentioned)
  (l ::= (lam var e))
  (c ::= integer add1 sub1)

  (k ::= mt (arg e env k) (op v k) (sel e e env k) (gethandler e var env k)
         (extendobj v var k) (deliver var k)))

(define-transition ocalc
  step
  [--> (var env k) ((env-lookup env var) k)]
  [--> (l env k) ((clo l env) k)]
  [--> ((quote c) env k) (c k)]
  [--> (emptyobj env k) ((obj (env-empty)) k)]
  [--> ((app e_op e_arg) env k) (e_op env (arg e_arg env k))]
  [--> ((ifz e_test e_then e_else) env k) (e_test env (sel e_then e_else env k))]
  [--> ((respond e_obj var e_handler) env k) (e_obj env (gethandler e_handler var env k))]
  [--> ((send e_obj var) env k) (e_obj env (deliver var k))]

  [--> (v (arg e env k)) (e env (op v k))]
  [--> (v (op add1 k)) ((integer-add v 1) k)]
  [--> (v (op sub1 k)) ((integer-subtract v 1) k)]
  [--> (v (op (clo (lam var e_body) env_1) k))
       (e_body env k)
       (where env (env-extend1 env_1 var v))]
  [--> (0 (sel e_then e_else env k)) (e_then env k)]
  [--> (v (sel e_then e_else env k)) (e_else env k)]
  [--> (v (gethandler e var env k)) (e env (extendobj v var k))]
  [--> (v_handler (extendobj (obj env) var k))
       (v_extended k)
       (where v_extended (obj (env-extend1 env var v_handler)))]
  [--> (v_obj (deliver var k)) (v_obj (op v k))
       (where (obj env) v_obj)
       (where v (env-lookup env var))])

(define-evaluator ocalc
  eval
  #:load [--> e (e (env-empty) mt)]
  #:unload [--> (v mt) v]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (current-test-language ocalc)

  (test-equal (run-eval (app (quote add1) (quote 10))) 11)
  (test-equal (run-eval (app (lam self (quote 42)) (quote 0))) 42)
  (test-equal (run-eval (send (respond emptyobj x (lam self (quote 42))) x))
              42)

  (jam-test))
