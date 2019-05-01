#lang racket
(require jam)

;; Two CBV evaluators for the same language, one where all states are
;; of the form (e env k) and another where so-called eval and apply
;; states are distinct: eval are of the form (e env k) and apply are
;; (v k). Supporting new values in the former takes a little more work
;; than in the latter.

;; This file contains the evaluators without integers. See
;; twomachines-integers.rkt for notes and the evaluators that support
;; integers.

(define-language cbv
  #:data ([env (environment x v)])

  (e ::= x (lambda (x) e) (e e))
  (x ::= variable-not-otherwise-mentioned)
  (v ::= {l env})
  (l ::= (lambda (x) e))

  (k ::= mt (argk e env k) (callk v k)))

(define-transition cbv
  entangled

  [--> (x env k)
       (e env k)
       (where {e env} (env-lookup env x))]

  [--> ((e_1 e_2) env k)
       (e_1 env (argk e_2 env k))]

  [--> (l env (argk e_arg env_arg k))
       (e_arg env_arg (callk {l env} k))]

  [--> (l env_l (callk {(lambda (x) e) env} k))
       (e (env-extend1 env x {l env_l}) k)])

(define-transition cbv
  disentangled

  [--> (x env k)
       (v k)
       (where v (env-lookup env x))]

  [--> ((e_1 e_2) env k)
       (e_1 env (argk e_2 env k))]

  [--> (l env k)
       ({l env} k)]

  [--> (v (argk e env k))
       (e env (callk v k))]

  [--> (v (callk {(lambda (x) e) env} k))
       (e (env-extend1 env x v) k)])

(define-evaluator cbv
  eval-entangled
  #:transition entangled
  #:load [--> e (e (env-empty) mt)]
  #:unload [--> (l env mt) l]
  #:control-string [(e _ _) e])

(define-evaluator cbv
  eval-disentangled
  #:transition disentangled
  #:load [--> e (e (env-empty) mt)]
  #:unload [--> ({l env} mt) l]
  #:control-string [(e _ _) e])

(module+ test
  (require syntax/parse/define)
  (current-test-language cbv)

  (define-simple-macro (test-similar check expect)
    (begin
      (test-equal (run-eval-entangled check) expect)
      (test-equal (run-eval-disentangled check) expect)))

  (test-similar (lambda (x) x) (lambda (x) x))
  (test-similar ((lambda (x) x) (lambda (y) y)) (lambda (y) y))
  (test-similar ((lambda (x) x) (lambda (y) (y y))) (lambda (y) (y y)))

  (jam-test))
