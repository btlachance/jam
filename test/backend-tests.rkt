#lang racket
(require
 rackunit
 racket/hash
 jam/lang-rep
 jam/pattern
 jam/ir jam/to-py jam/util (except-in jam/rep nonterminal)
 (only-in jam/lang jam-test))

(check-equal? (lang-nonterminals (lang-info 'x0 '() '())) '())

(define x1 (lang-info 'x1 '((x y z)) '((variable-not-otherwise-mentioned))))
(check-match (lang-nonterminals x1) (list-no-order 'x 'y 'z))


(define lc1 (lang-info 'lc1 '((x y z) (e)) '((variable-not-otherwise-mentioned)
                                             (x (e e) (lambda x e)))))
(check-match (lang-nonterminals lc1) (list-no-order 'x 'y 'z 'e))


(define lc2 (lang-info 'lc2 '((x y z) (e)) '((variable-not-otherwise-mentioned)
                                             (x (e e ...) (lambda (x ...) e)))))
(define lc2-name (lang-name lc2))
(check-match (lang-nonterminals lc2) (list-no-order 'x 'y 'z 'e))
(check-not-exn (lambda () (lang-parse-pattern lc2 '((lambda e_1 e_2)))))
(check-exn exn:fail? (lambda () (lang-parse-pattern lc2 '((lambda e e)))))


(check-match (let-values ([(_ names) (lang-parse-pattern
                                      lc2 '(name rest _)
                                      #:bound-names? #t)])
               names)
             (list-no-order 'rest))

(check-match (lang-parse-template lc2 '(x rest))
             (pair _ (pair (literal 'rest) _)))

(check-match (lang-parse-template lc2 '(x rest) '(rest))
             (pair _ (pair (name 'rest _) _)))

(check-match (let-values ([(_ names) (lang-parse-pattern
                                      lc2 '((lambda e_1 e_2))
                                      #:bound-names? #t)])
               names)
             (list-no-order 'e_1 'e_2))

(check-exn exn:fail? (lambda () (lang-parse-pattern lc2 '(z ... w))))

(define info0
  (compile/deconstruct (lang-parse-pattern lc2 '((((x ...) e) ...) y))))
(check-match (hash-ref info0 'y) (list 0 _))
(check-match (hash-ref info0 'e) (list 1 _))
(check-match (hash-ref info0 'x) (list 2 _))


(define info1 (compile/deconstruct (lang-parse-pattern lc2 '(x y z ...))))
(check-match (hash-ref info1 'x) (list 0 _))
(check-match (hash-ref info1 'y) (list 0 _))
(check-match (hash-ref info1 'z) (list 1 _))


(define p0 (lang-parse-pattern lc2 '(lambda ((name alpha x) _ z ...) e)))
(check-not-exn (lambda () (compile/guard p0 lc2-name)))
(define env0 (compile/deconstruct p0))
(define t0 (lang-parse-template lc2 '((alpha z) ...)))
(check-not-exn (lambda () (compile/transcribe t0 env0)))


(define p1 (lang-parse-pattern lc2 '(let (((x ...) e) ...) foo)))
(define t1 (lang-parse-template lc2 '(let (((x ...) e) ...) foo)))
(define env1 (compile/deconstruct p1))
(check-not-exn (lambda () (compile/transcribe t1 env1)))


(check-not-exn
 (lambda () (compile/transcribe (lang-parse-template lc2 'x) (hash))))

;; XXX to support metafunction definitions like a module-level define
;; in Racket with this API, need all `define-metafunction` forms in
;; the module to `add-metafunction-name!` before a single metafunction
;; template gets parsed. To get by, we can do something ugly in and
;; lift the parsing/registering code for each def-metafun to the end
;; of the module. To get rid of that, I should see if Redex uses its
;; phase 1 bindings for metafunctions in a way I can crib---it appears
;; to use that information in the `term` form so I would probably need
;; to parse templates, patterns, etc at phase 1.
(define mf0-name 'two-or-more)

(check-false (lang-metafunction-name? lc2 mf0-name))
(add-metafunction-name! lc2 mf0-name)
(check-true (lang-metafunction-name? lc2 mf0-name))
(check-match (lang-parse-template lc2 '(two-or-more 0 0))
             (mf-apply _ 'two-or-more _))
(check-match (lang-parse-template lc2 '(x (two-or-more 0 0)))
             (pair _ (pair (mf-apply _ 'two-or-more _) _)))

(define mf0
  (metafunction
   mf0-name
   (mf:plain
    (compile-clauses
     lc2-name
     (list
      (clause (lang-parse-pattern lc2 '(x y))
              (lang-parse-template lc2 '(x y))
              '())
      (clause (lang-parse-pattern lc2 '(w x y z ...))
              (lang-parse-template lc2 '(w x y z ...))
              '()))))))
(register-metafunction! lc2 mf0)


(check-false (lang-metafunction-name? lc2 'lookup))
(check-exn exn:fail? (lambda () (register-metafunction! lc2 mf0)))


(define mod0
  `(module test0 (require) (provide)
           ,(define:* 'x (proc* '(t) (lexical-var* 't)))))
(check-equal? (lift-procs mod0) mod0)

(define mod1
  `(module test1 (require) (provide)
           ,(define:* 'x `(call ,(lexical-var* 'map)
                                ,(proc* '(t) (lexical-var* 't))
                                (call ,(lexical-var* 'nil))))))
(check-match (lift-procs mod1)
             `(module test1 (require) (provide)
                      ,(define:* (? symbol? s) (proc* '(t) (lexical-var* 't)))
                      ,(define:* 'x `(call ,(lexical-var* 'map)
                                           ,(lexical-var* s)
                                           (call ,(lexical-var* 'nil))))))

(check-not-exn (lambda () (jam-test lc2 #:on-fail fail)))

(check-not-exn
 (lambda ()
   (compile-test lc2-name
                 (lang-parse-template lc2 '(two-or-more 0 0))
                 (lang-parse-template lc2 '(0 0))
                 "shouldn't run"
                 #:equal? #t)))
(check-not-exn
 (lambda ()
   (compile-test lc2-name
                 (lang-parse-template lc2 '(two-or-more 0 0))
                 (lang-parse-template lc2 '(0 1))
                 "shouldn't run"
                 #:equal? #f)))

(lang-add-test-equal! lc2 'x 'x)
(lang-add-test-equal! lc2 'alpha 'alpha)
(lang-add-test-not-equal! lc2 'x 'integer)

(lang-add-test-not-equal! lc2 0 'integer)
(lang-add-test-equal! lc2 '(0 a) '(0 a))

(lang-add-test-equal! lc2 '(two-or-more x z) '(x z))
(lang-add-test-not-equal! lc2 '(two-or-more x z) '(0 1))

(lang-add-test-equal! lc2 '(two-or-more w b c d e f) '(w b c d e f))

(define mf1-name 'cons-vars)
(add-metafunction-name! lc2 mf1-name)
(define mf1
  (metafunction
   mf1-name
   (mf:plain
    (compile-clauses
     lc2-name
     (list
      (clause (lang-parse-pattern lc2 '(x y))
              (lang-parse-template lc2 '(x y))
              '())
      (let-values ([(pat names) (lang-parse-pattern lc2 '(name rest _) #:bound-names? #t)])
        (clause (lang-parse-pattern lc2 '(x y z z_rest ...))
                (lang-parse-template lc2 '(x rest) names)
                (list (list pat
                            (lang-parse-template lc2 '(cons-vars y z z_rest ...)))))))))))
(register-metafunction! lc2 mf1)

(lang-add-test-equal! lc2 '(cons-vars a b) '(a b))
(lang-add-test-equal! lc2 '(cons-vars a b c) '(a (b c)))
(lang-add-test-equal! lc2 '(cons-vars a b c d) '(a (b (c d))))

(lang-add-test-equal! lc2 '(cons-vars a b x) '(a (b x)))

(lang-add-test-not-equal! lc2 'a 'x)

(check-not-exn (lambda () (jam-test lc2 #:on-fail fail)))

(define env-lang (lang-info 'env0
                            '((x) (v)) '((variable-not-otherwise-mentioned)
                                         (integer))
                            '(((xi rho) (environment x v)))))

(check-match (lang-nonterminals env-lang)
             (list-no-order 'x 'v 'xi 'rho))

(check-match (lang-parse-pattern env-lang 'xi)
             (name 'xi (nonterminal 'xi)))

(check-false (lang-metafunction-name? env-lang 'lookup))
(for ([f '(xi-lookup xi-empty xi-bound? xi-extend xi-extend1)])
  (check-true (lang-metafunction-name? env-lang f)))

(let-values ([(_ mod)
              (lang-grammar-module env-lang)])
  (check-match mod
               `(module ,_ ,_ ,_
                        ,@(list-no-order
                           (define:* 'nt-xi? (proc* _ _))
                           (define:* 'nt-rho? (proc* _ _))
                           _ ...))))

(let-values ([(_ mod)
              (lang-metafunction-module env-lang
                                        #:grammar (list (grammar-handle 'env0)))])
  (check-match mod
             `(module ,_ ,_ ,_
                      ,@(list-no-order
                         (define:* 'xi-lookup (proc* _ _))
                         (define:* 'xi-empty (proc* _ _))
                         (define:* 'xi-bound? (proc* _ _))
                         (define:* 'xi-extend (proc* _ _))
                         (define:* 'xi-extend1 (proc* _ _))
                         _ ...))))

;; XXX If I want to have metafunctions that return booleans, I need
;; terms that are booleans (and then templates/patterns for dealing
;; with booleans). A hacky alternative would be to make environment
;; lookup take a sentinel to return if the key isn't bound, and then
;; every lookup site has to know what it can pass as a sentinel that
;; won't collide with the values in the environment. Slightly less
;; hacky I could require the constructor for environments to take a
;; default value that gets returned, and then the construction site is
;; all that has to know what overlaps with the values. With either of
;; those I can avoid adding booleans for the mean time, but I really
;; don't want to have to resort to either of them.

(lang-add-test-not-equal! env-lang '(xi-empty) 0)
(check-not-exn (lambda () (jam-test env-lang #:on-fail fail)))

(check-false (lang-transition-name? env-lang 'step))
(check-not-exn
 (lambda ()
   (lang-add-transition! env-lang 'step
                         '(env) '(env) '(()))))
(check-true (lang-transition-name? env-lang 'step))

(check-false (lang-evaluator-name? env-lang 'eval))
(check-not-exn
 (lambda ()
   (lang-add-evaluator!
    env-lang 'eval 'step
    '(0 (empty-env) ())
    '(env 1 ())
    '(env env ()))))
(check-true (lang-evaluator-name? env-lang 'eval))

(let-values ([(_ emod) (lang-evaluator-module env-lang)])
  (check-match emod
               `(module ,_ ,_ ,_
                        ,@(list-no-order
                           (evaluator* 'eval _ _ _ _)
                           (define:* 'eval-load _)
                           (define:* 'eval-unload _)
                           (define:* 'eval-control-string _)
                           _ ...))))

(check-exn
 #rx"main evaluator that is defined"
 (lambda () (lang-modules env-lang #:main-evaluator 'foo)))

(check-not-exn
 (lambda () (lang-modules env-lang #:main-evaluator 'eval)))
