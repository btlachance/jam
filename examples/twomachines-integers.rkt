#lang racket
(require jam)

;; Wanting to support integers, you include them in the expression and
;; value forms and proceed to update the entangled transition
;; function. The variable rule is a good place to start but now
;; environment lookup can produce two things, an integer or a
;; closure. Do you add another variable rule, one for when the name
;; was bound to an integer? Or do you change the way that integers are
;; stored in environments, e.g. by pairing them with a dummy
;; environment? Or analagously, do you change the value form so that
;; even integers are paired with an environment?

;; Once you settle on what the variable rule should do, more rules
;; need to be changed. What should happen when there's an integer in
;; the control string and an argk continuation? Raising an error at
;; that point is a bit unusual for a semantics but not out of the
;; question. When it's a lambda in the control string, we push a callk
;; continuation with the corresponding closure; the callk continuation
;; takes any value so we could shove an integer in there and move on.

;; What should happen when an integer returns to a callk continuation?
;; We need to extend the environment in a way that works with the
;; lookup rule. Or we could go back and change the lookup rule in a
;; way that works better with how we want to extend the environment.

;; The terminal state for the evaluator should probably also be
;; changed to produce an integer when the program evaluates to one. In
;; Jam, combining the lambda case and the integer case can be
;; accomplished in a few ways: introduce a nonterminal that ranges
;; over both lambdas and integer and the unload transition just
;; returns whatever matches that nonterminal; or use a metafunction to
;; return a lambda when the terminal state has a lambda and an integer
;; when the terminal state has an integer.

;; Adding integer support to the disentangled version only requires
;; adding one rule and changing none. And nothing needs to change with
;; the environments. The unload transition though needs a small
;; change.

;; (Even if we started out with a nonterminal that ranged over
;; syntactic values, which at the beginning was just lambdas, then we
;; would have still hit a snag with the environments. When returning
;; to an argk continuation, we could have then combined the lambda and
;; non-lambda case by changing our representaiton of values: every
;; syntactic value is paired with an environment, regardless of
;; whether it needs it. This is unusual looking from an implementer's
;; point of view but it does run. Changes to the disentangled
;; transition function would still have been minimal.)

(define-language cbv
  #:data ([env (environment x v)])

  (e ::= x l (e e) integer)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= {l env} integer)
  (l ::= (lambda (x) e))
  (c ::= (lambda (x) e) integer)

  (k ::= mt (argk e env k) (callk v k)))

(define-transition cbv
  entangled

  [--> (x env k)
       (e env k)
       (where {e env} (env-lookup env x))]

  [--> (x env k)
       (v (env-empty) k)
       (where v (env-lookup env x))]

  [--> ((e_1 e_2) env k)
       (e_1 env (argk e_2 env k))]

  [--> (l env (argk e_arg env_arg k))
       (e_arg env_arg (callk {l env} k))]

  [--> (integer env (argk e_arg env_arg k))
       (e_arg env_arg (callk integer k))]

  [--> (l env_l (callk {(lambda (x) e) env} k))
       (e (env-extend1 env x {l env_l}) k)]

  [--> (integer env_l (callk {(lambda (x) e) env} k))
       (e (env-extend1 env x integer) k)])

(define-transition cbv
  disentangled

  [--> (x env k)
       (v k)
       (where v (env-lookup env x))]

  [--> ((e_1 e_2) env k)
       (e_1 env (argk e_2 env k))]

  [--> (l env k)
       ({l env} k)]

  [--> (integer env k)
       (integer k)]

  [--> (v (argk e env k))
       (e env (callk v k))]

  [--> (v (callk {(lambda (x) e) env} k))
       (e (env-extend1 env x v) k)])

(define-metafunction cbv
  [(unwrap {(lambda (x) e) env}) (lambda (x) e)]
  [(unwrap integer) integer])

(define-evaluator cbv
  eval-entangled
  #:transition entangled
  #:load [--> e (e (env-empty) mt)]
  #:unload [--> (c _ mt) c]
  #:control-string [(e _ _) e])

(define-evaluator cbv
  eval-disentangled
  #:transition disentangled
  #:load [--> e (e (env-empty) mt)]
  #:unload [--> (v mt) (unwrap v)]
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
  (test-similar ((lambda (x) x) 100) 100)
  (test-similar ((lambda (x) 42) 10) 42)

  (jam-test))
