#lang racket
(require jam)
(provide pl)

(define-language pl
  #:data ([env (environment x V)]
          [mvec (mutable-sequence V)]
          [ivec (immutable-sequence V)]
          [file (file)])

  (P     ::= (t ...))
  (t     ::= e (define-values (x ...) e))
  (e     ::= x l (quote c) (e e ...) (if e e e)
             (let-values ([(x ...) e] ...) e e ...)
             (letrec-values ([(x ...) e] ...) e e ...)
             (begin e e ...))
  (l     ::= (lambda (x ...) e e ...)
             (lambda x e e ...)
             (lambda (x ...) (dot x) e e ...))

  (x y z ::= variable-not-otherwise-mentioned)
  (c     ::= integer real boolean string (#%s string))

  (V     ::= {env l} c mvec ivec file
             #%+ #%- #%* #%zero? #%exact-integer? #%inexact? #%= #%<
             #%inexact->exact #%exact->inexact #%number?
             (#%cons V V) #%null #%cons #%car #%cdr #%null? #%pair? #%list
             #%apply #%void #%values #%call-with-values
             #%vector #%vector-immutable #%vector-ref #%vector-length #%vector-set!
             #%vector?
             #%current-command-line-arguments
             #%boolean? #%not
             #%string? #%string-append #%string=?
             #%raise ;; XXX FYFF gives a semantics where raise isn't prim
             #%write-string #%current-output-port #%current-error-port
             #%number->string
             #%symbol? #%symbol=? #%symbol->string
             #%current-inexact-milliseconds)

  (k     ::= k1 k*)
  (k1    ::= (appk env (e ...) (V ...) k) (ifk env e e k))
  (k*    ::= (topk env P) (defk (x ...) env P) (cwvk V k)

             ;; env               environment for remaining RHS
             ;; (x ...)           variables the current RHS results will be bound to
             ;; ([(x ...) e] ...) remaining variables to bind/RHS to evaluate
             ;; ((x V) ...)       variables/values for evaluated RHS so far
             ;; (e e ...)         body expressions
             ;;
             ;; (We could keep the list of variables/values as two
             ;; lists instead of one zipped one if we had an explicit
             ;; way to check that #values returned to the continuation
             ;; matched #variables for the current RHS)
             (letk env (x ...) ([(x ...) e] ...) ((x V) ...) (e e ...) k)

             ;; Like letk but RHS and the body are evaluated in the
             ;; same environment, and values are set in that
             ;; environment once they're available, so no need for a
             ;; separate list of variables/values so far
             (letreck env (x ...) ([(x ...) e] ...) (e e ...) k)

             (begink env (e e ...) k)))
(module+ test
  (current-test-language pl))

(define-metafunction pl
  [(init-env (x_toplevel ...))
   env

   (where env (env-empty))
   (where env (env-extend
               env
               (  +   -   *   zero?   exact-integer?   inexact?   =   <
                  inexact->exact   exact->inexact   number?
                  cons   null   car   cdr   null?   pair?   list
                  apply   void   values   call-with-values
                  vector   vector-immutable   vector-ref   vector-length   vector-set!
                  vector?
                  current-command-line-arguments
                  boolean?   not
                  string?   string-append   string=?
                  raise
                  write-string   current-output-port   current-error-port
                  number->string
                  symbol?   symbol=?   symbol->string
                  current-inexact-milliseconds)
               (#%+ #%- #%* #%zero? #%exact-integer? #%inexact? #%= #%<
                #%inexact->exact #%exact->inexact #%number?
                #%cons #%null #%car #%cdr #%null? #%pair? #%list
                #%apply #%void #%values #%call-with-values
                #%vector #%vector-immutable #%vector-ref #%vector-length #%vector-set!
                #%vector?
                #%current-command-line-arguments
                #%boolean? #%not
                #%string? #%string-append #%string=?
                #%raise
                #%write-string #%current-output-port #%current-error-port
                #%number->string
                #%symbol? #%symbol=? #%symbol->string
                #%current-inexact-milliseconds)))
   (where env (env-extend-cells env (x_toplevel ...)))])

(define-metafunction pl
  [(toplevel-names ())
   ()]

  [(toplevel-names (e t ...))
   (toplevel-names (t ...))]

  [(toplevel-names ((define-values (x ...) _) t ...))
   (append (x ...) (toplevel-names (t ...)))])

(define-metafunction pl
  [(flatten-vars ())
   ()]
  [(flatten-vars (() (x ...) ...))
   (flatten-vars ((x ...) ...))]
  [(flatten-vars ((x_0 x_rest ...) (x ...) ...))
   (x_0 x_flattened ...)
   (where (x_flattened ...) (flatten-vars ((x_rest ...) (x ...) ...)))])

(define-metafunction pl
  [(append () ((name any _) ...))
   (any ...)]
  [(append ((name any_first _) (name any_rest _) ...)
           ((name any _) ...))
   (any_first appended ...)
   (where ((name appended _) ...) (append (any_rest ...) (any ...)))])

(define-metafunction pl
  [(load-pl string_path)
   P
   (where P (system*/json-term "/usr/bin/env" "racket" "/Users/blachance/projects/jam/examples/pycketlite-util.rkt" string_path))])

(module+ test
  (test-equal (flatten-vars ((x y))) (x y))
  (test-equal (flatten-vars ((x y) () (z))) (x y z))

  (test-equal (append () (#t)) (#t))
  (test-equal (append (1 2 3) (#t #f #t)) (1 2 3 #t #f #t))
  (test-equal (append (1 #t 2) ()) (1 #t 2))

  (test-not-equal (load-pl "/Users/blachance/projects/jam/examples/racket/predefined.rkt") ()))

(define-metafunction pl
  [(apply-op #%+ (integer_1 integer_2))
   (integer-add integer_1 integer_2)]

  [(apply-op #%- (integer_1 integer_2))
   (integer-subtract integer_1 integer_2)]

  [(apply-op #%* (integer_1 integer_2))
   (integer-multiply integer_1 integer_2)]

  [(apply-op #%+ (real_1 real_2))
   (real-add real_1 real_2)]

  [(apply-op #%- (real_1 real_2))
   (real-subtract real_1 real_2)]

  [(apply-op #%* (real_1 real_2))
   (real-multiply real_1 real_2)]

  [(apply-op #%exact-integer? (integer))
   #t]

  [(apply-op #%exact-integer? (V))
   #f]

  [(apply-op #%inexact? (real))
   #t]

  [(apply-op #%inexact? (integer))
   #f]

  [(apply-op #%zero? (0))
   #t]

  [(apply-op #%zero? (0.0))
   #t]

  [(apply-op #%zero? (-0.0))
   #t]

  [(apply-op #%zero? (V))
   #f]

  [(apply-op #%number? (integer))
   #t]

  [(apply-op #%number? (real))
   #t]

  [(apply-op #%number? (V))
   #f]

  [(apply-op #%= (integer))
   #t]

  [(apply-op #%= (real))
   #t]

  [(apply-op #%= (integer_1 integer_2))
   (integer-= integer_1 integer_2)]

  [(apply-op #%= (real_1 real_2))
   (real-= real_1 real_2)]

  [(apply-op #%= (integer real))
   (apply-op #%= (integer (real->integer real)))]

  [(apply-op #%= (real integer))
   (apply-op #%= ((real->integer real) integer))]

  [(apply-op #%< (integer_1 integer_2))
   (integer-< integer_1 integer_2)]

  [(apply-op #%< (real_1 real_2))
   (real-< real_1 real_2)]

  [(apply-op #%< (integer real))
   (real-< (integer->real integer) real)]

  [(apply-op #%< (real integer))
   (real-< real (integer->real integer))]

  [(apply-op #%exact->inexact (integer))
   (integer->real integer)]

  [(apply-op #%exact->inexact (real))
   real]

  ;; XXX This isn't quite right since real->integer truncates,
  ;; but until I have rationals it's the best I can do
  [(apply-op #%inexact->exact (real))
   (real->integer real)]

  [(apply-op #%inexact->exact (integer))
   integer]

  [(apply-op #%cons (V_1 V_2))
   (#%cons V_1 V_2)]

  [(apply-op #%car ((#%cons V _)))
   V]

  [(apply-op #%cdr ((#%cons _ V)))
   V]

  [(apply-op #%null? (#%null))
   #t]

  [(apply-op #%null? (V))
   #f]

  [(apply-op #%pair? ((#%cons _ _)))
   #t]

  [(apply-op #%pair? (V))
   #f]

  [(apply-op #%list ())
   #%null]

  [(apply-op #%list (V V_rest ...))
   (#%cons V (apply-op #%list (V_rest ...)))]

  [(apply-op #%void (V ...))
   #%void]

  [(apply-op #%vector (V ...))
   (mvec-of-elements V ...)]

  [(apply-op #%vector-immutable (V ...))
   (ivec-of-elements V ...)]

  [(apply-op #%vector-ref (mvec integer))
   (mvec-element-at mvec integer)]

  [(apply-op #%vector-ref (ivec integer))
   (ivec-element-at ivec integer)]

  [(apply-op #%vector-length (mvec))
   (mvec-length mvec)]

  [(apply-op #%vector-length (ivec))
   (ivec-length ivec)]

  [(apply-op #%vector-set! (mvec integer V))
   #%void
   (where () (mvec-set mvec integer V))]

  [(apply-op #%vector? (mvec))
   #t]

  [(apply-op #%vector? (ivec))
   #t]

  [(apply-op #%vector? (V))
   #f]

  [(apply-op #%current-command-line-arguments ())
   (ivec-of-elements)]

  [(apply-op #%boolean? (boolean))
   #t]

  [(apply-op #%boolean? (V))
   #f]

  [(apply-op #%not (#f))
   #t]

  [(apply-op #%not (V))
   #f]

  [(apply-op #%string? (string))
   #t]

  [(apply-op #%string? (V))
   #f]

  [(apply-op #%string-append ()) ""]

  [(apply-op #%string-append (string_0 string ...))
   (string-append string_0 (apply-op #%string-append (string ...)))]

  [(apply-op #%string=? (string_1 string_2))
   (string-= string_1 string_2)]

  [(apply-op #%current-output-port ())
   (file-stdout)]

  [(apply-op #%current-error-port ())
   (file-stderr)]

  [(apply-op #%write-string (string file))
   (string-length string)
   (where () (file-write file string))]

  [(apply-op #%write-string (string))
   (apply-op #%write-string (string (file-stdout)))]

  [(apply-op #%number->string (integer))
   (integer-string integer)]

  [(apply-op #%number->string (real))
   (real-string real)]

  [(apply-op #%symbol? ((#%s string)))
   #t]

  [(apply-op #%symbol? (V))
   #f]

  [(apply-op #%symbol=? (((name _1 #%s) string_1) ((name _2 #%s) string_2)))
   (string-= string_1 string_2)]

  [(apply-op #%symbol->string ((#%s string)))
   string]

  [(apply-op #%current-inexact-milliseconds ())
   (integer->real (clock-milliseconds))])

(define-metafunction pl
  [(prefix-and-rest () (V_rest ...))
   (() (apply-op #%list (V_rest ...)))]
  [(prefix-and-rest (x y ...) (V_0 V ...))
   ((V_0 V_prefix ...) V_rest)
   (where ((V_prefix ...) V_rest) (prefix-and-rest (y ...) (V ...)))])

(define-metafunction pl
  [(begink* env () k) k]
  [(begink* env (e e_rest ...) k) (begink env (e e_rest ...) k)])

(define-transition pl
  step
  [--> (topk env (t t_rest ...))
       (t (topk env (t_rest ...)))]

  [--> (e (topk env P))
       (e env (topk env P))]

  [--> ((define-values (x ...) e) (topk env P))
       (e env (defk (x ...) env P))]

  [--> (x env k)
       (V k)
       (where V (env-lookup env x))]

  [--> (l env k)
       ({env l} k)]

  [--> ((quote c) env k)
       (c k)]

  [--> ((e e_args ...) env k)
       (e env (appk env (e_args ...) () k))]

  [--> ((if e_test e_then e_else) env k)
       (e_test env (ifk env e_then e_else k))]

  [--> ((let-values () e e_rest ...) env k)
       (e env (begink* env (e_rest ...) k))]

  [--> ((let-values ([(x_first ...) e_first] [(x_rest ...) e_rest] ...) e_body ...) env k)
       (e_first env (letk env (x_first ...) ([(x_rest ...) e_rest] ...)
                          () (e_body ...) k))]

  [--> ((letrec-values () e e_rest ...) env k)
       (e env (begink* env (e_rest ...) k))]

  [--> ((letrec-values ([(x ...) e] ...) e_body ...) env k)
       (e_first env_rec (letreck env_rec (x_first ...) ([(x_rest ...) e_rest] ...) (e_body ...) k))
       (where ([(x_first ...) e_first] [(x_rest ...) e_rest] ...) ([(x ...) e] ...))
       (where env_rec (env-extend-cells env (flatten-vars ((x ...) ...))))]

  [--> ((begin e e_rest ...) env k)
       (e env (begink* env (e_rest ...) k))]

  [--> (V k*)
       ((#%values V) k*)]
  [--> ((#%values V) k1)
       (V k1)]

  [--> ((#%values V ...) (topk env_top P))
       (topk env_top P)]

  [--> ((#%values V ...) (defk (x ...) env_top P))
       (topk env_top P)
       (where () (env-set-cells env_top (x ...) (V ...)))]

  [--> (V_0 (appk env (e_arg e_args ...) (V ...) k))
       (e_arg env (appk env (e_args ...) (V_0 V ...) k))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e (begink* env_e (e_rest ...) k))
       (where ({env_op (lambda (x ...) e e_rest ...)} V ...) (reverse (V_0 V ...)))
       (where env_e (env-extend env_op (x ...) (V ...)))
       (where () (can-enter! e))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e (begink* env_e (e_rest ...) k))
       (where ({env_op (lambda x e e_rest ...)} V ...) (reverse (V_0 V ...)))
       (where env_e (env-extend env_op (x) ((apply-op #%list (V ...)))))
       (where () (can-enter! e))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e (begink* env_e (e_rest ...) k))
       (where ({env_op (lambda (x ...) (dot y) e e_rest ...)} V ...) (reverse (V_0 V ...)))
       (where ((V_prefix ...) V_rest) (prefix-and-rest (x ...) (V ...)))
       (where env_e (env-extend env_op
                                (append (x ...) (y))
                                (append (V_prefix ...) (V_rest))))
       (where () (can-enter! e))]

  [--> (V_0 (appk env () (V ...) k))
       (V_arglast (appk env () (V_argother ...) k))
       (where (#%apply V_fun V_args ...) (reverse (V ...)))
       (where #%null V_0)
       (where (V_arglast V_argother ...) (reverse (V_fun V_args ...)))]

  [--> (V_0 (appk env () (V ...) k))
       (V_cdr (appk env () (V_car V ...) k))
       (where (#%apply V_fun V_args ...) (reverse (V ...)))
       (where (#%cons V_car V_cdr) V_0)]

  [--> (V_0 (appk _ () (V ...) k))
       ((#%values V_vals ...) k)
       (where (#%values V_vals ...) (reverse (V_0 V ...)))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env (begink* env (e_rest ...) (cwvk V_consumer k)))
       (where (#%call-with-values V_producer V_consumer) (reverse (V_0 V ...)))
       (where {env (lambda () e e_rest ...)} V_producer)
       (where () (can-enter! e))]

  [--> ((#%values V ...) (cwvk V_consumer k))
       (V_lastval (appk (env-empty) () (V ...) k))
       (where (V_lastval V ...) (reverse (V_consumer V ...)))]

  [--> (V (appk _ () (#%raise) k))
       (topk (env-empty) ())]

  [--> (V_0 (appk _ () (V ...) k))
       (V_result k)
       (where (V_op V ...) (reverse (V_0 V ...)))
       (where V_result (apply-op V_op (V ...)))]

  [--> ((#%values V_new ...) (letk env_e (x_new ...) ([(x ...) e] [(x_rest ...) e_rest] ...)
                                   (name sofar _) (e_body ...) k))
       (e env_e (letk env_e (x ...) ([(x_rest ...) e_rest] ...)
                      (append ((x_new V_new) ...) ((x_sofar V_sofar) ...))
                      (e_body ...) k))
       (where ((x_sofar V_sofar) ...) sofar)]

  [--> ((#%values V_new ...) (letk env (x_new ...) ()
                                   ((x_sofar V_sofar) ...) (e e_rest ...) k))
       (e env_body (begink* env_body (e_rest ...) k))
       (where env_body (env-extend env
                                   (append (x_new ...) (x_sofar ...))
                                   (append (V_new ...) (V_sofar ...))))]

  [--> ((#%values V_new ...) (letreck env_rec (x_new ...)
                                      ([(x ...) e] [(x_rest ...) e_rest] ...)
                                      (e_body ...) k))
       (e env_rec (letreck env_rec (x ...)
                         ([(x_rest ...) e_rest] ...)
                         (e_body ...) k))
       (where () (env-set-cells env_rec (x_new ...) (V_new ...)))]

  [--> ((#%values V_new ...) (letreck env_rec (x_new ...) () (e e_rest ...) k))
       (e env_rec (begink* env_rec (e_rest ...) k))
       (where () (env-set-cells env_rec (x_new ...) (V_new ...)))]

  [--> ((#%values V ...) (begink env (e e_rest ...) k))
       (e env (begink* env (e_rest ...) k))]

  [--> (#f (ifk env _ e_else k))
       (e_else env k)]

  [--> (V (ifk env e_then _ k))
       (e_then env k)])

(define-evaluator pl
  eval

  #:load [--> P_user (topk (init-env (toplevel-names P)) P)
              (where P_predef (load-pl "/Users/blachance/projects/jam/examples/racket/predefined.rkt"))
              (where P (append P_predef P_user))]

  #:unload [--> (topk _ ()) ()] ;; XXX maybe call an exit metafunction
                                ;; here, indicating a succesful
                                ;; termination?
  #:transition step
  #:control-string [(e _ _) e])

(define-metafunction pl
  [(unload {env l}) l]
  [(unload V) V])

;; For now, eval-e is only really useful for internal testing. I don't
;; know/have a good way to set things up to use it with the --repl
;; flag while ensuring that it's built; right now the --build flag
;; only controls building a single evaluator, and I don't know how to
;; generalize that to work with the expression evaluator and the
;; --repl flag. Adding an argument to --build sounds annoying...
(define-evaluator pl
  eval-e

  #:load [--> e (topk (init-env ()) (e))]
  #:unload [--> ((#%values V) (topk _ ())) (unload V)]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (test-equal (run-eval-e '5) 5)
  (test-equal (run-eval-e '#f) #f)
  (test-equal (run-eval-e (+ '1 '2)) 3)
  (test-equal (run-eval-e (- '2 '1)) 1)
  (test-equal (run-eval-e (lambda (x) (x x))) (lambda (x) (x x)))
  (test-equal (run-eval-e (lambda y y)) (lambda y y))
  (test-equal (run-eval-e ((lambda (x) x) '10)) 10)
  (test-equal (run-eval-e ((lambda (x y) x) '10 '11)) 10)
  (test-equal (run-eval-e ((lambda (x y) y) '10 '11)) 11)
  (test-equal (run-eval-e ((lambda (n) (+ '1 n)) '10)) 11)
  (test-equal (run-eval-e (((lambda (x) (lambda (y) x)) '5) '6))
              5)
  (test-equal (run-eval-e ((lambda (f x) (f x)) zero? '0)) #t)
  (test-equal (run-eval-e ((lambda (f x) (f x)) (lambda (n) (+ n '1)) '0)) 1)

  (test-equal (run-eval-e
               ((lambda (fib) (fib fib '8))
                (lambda (rec n)
                  (if (zero? n)
                      '0
                      (if (zero? (- n '1))
                          '1
                          (+ (rec rec (- n '1))
                             (rec rec (- n '2))))))))
              21)

  (test-equal (run-eval-e
               ((lambda (fact) (fact fact '10))
                (lambda (rec n)
                  (if (zero? n)
                      '1
                      (* n (rec rec (- n '1)))))))
              3628800)

  (test-equal (run-eval
               ((define-values (id) (lambda (x) x))
                (+ (id '0) (id '1))
                (+ '3 '4)
                (+ '5 '6)))
              ())

  (test-equal (run-eval
               ((define-values (fact)
                  (lambda (n)
                    (if (zero? n)
                        '1
                        (* n (fact (- n '1))))))
                (fact '10)))
              ())

  (test-equal (run-eval
               ((define-values (fib)
                  (lambda (n)
                    (if (zero? n)
                        '0
                        (if (zero? (- n '1))
                            '1
                            (+ (fib (- n '1))
                               (fib (- n '2)))))))
                (fib '8)))
              ())

  (test-equal (run-eval
               ((define-values (even?)
                  (lambda (n)
                    (if (zero? n)
                        '#t
                        (odd? (- n '1)))))
                (define-values (odd?)
                  (lambda (n)
                    (if (zero? n)
                        '#f
                        (even? (- n '1)))))
                (even? '10)))
              ())

  (test-equal (run-eval
               ((values)
                (values '#t)
                (+ '1 (values '2))
                (+ (values '1) '2)
                (values (+ '1 '2) '3)))
              ())

  (test-equal (run-eval
               ((define-values () (values))
                (define-values (x) (values '1))
                (define-values (y z) (values '2 '3))
                (+ x (+ y z))))
              ())

  (test-equal (run-eval-e (null? null)) #t)
  (test-equal (run-eval-e (null? (cons '1 '2))) #f)
  (test-equal (run-eval-e (null? '#t)) #f)
  (test-equal (run-eval-e (pair? (cons '3 '4))) #t)
  (test-equal (run-eval-e (pair? null)) #f)
  (test-equal (run-eval-e (pair? '#t)) #f)

  (test-equal (run-eval-e (list)) #%null)
  (test-equal (run-eval-e (list '1 '2 '3))
              (#%cons 1 (#%cons 2 (#%cons 3 #%null))))

  (test-equal (run-eval-e ((lambda x x))) #%null)
  (test-equal (run-eval-e ((lambda x x) '1 '#f '3))
              (#%cons 1 (#%cons #f (#%cons 3 #%null))))

  (test-equal (run-eval-e ((lambda (x1 x2) (dot x3) (cons x2 (cons x1 x3)))
                           '5 '6 '7 '8 '9))
              (#%cons 6 (#%cons 5 (#%cons 7 (#%cons 8 (#%cons 9 #%null))))))

  (test-equal (run-eval-e (apply (lambda (x y) (+ x y)) '1 (list '2)))
              3)
  (test-equal (run-eval-e (apply (lambda (x y) (+ x y)) (list '3 '4)))
              7)
  (test-equal (run-eval-e (apply + '5 '6 null)) 11)
  (test-equal (run-eval-e (apply (lambda () '0) null)) 0)

  (test-equal (run-eval-e (void)) #%void)
  (test-equal (run-eval-e (void void)) #%void)
  (test-equal (run-eval-e (void '1 '2 '3)) #%void)

  (test-equal (run-eval-e (call-with-values (lambda () (values))
                                            (lambda () '42)))
              42)
  (test-equal (run-eval-e (call-with-values (lambda () '1)
                                            (lambda (x) (+ x '42))))
              43)
  (test-equal (run-eval-e (call-with-values (lambda () (values '2))
                                            (lambda (x) (* x '21))))
              42)
  (test-equal (run-eval-e (call-with-values (lambda () (values '1 '2))
                                            (lambda (x y) (+ x y))))
              3)

  (test-equal (run-eval-e (let-values () '0)) 0)
  (test-equal (run-eval-e (let-values ([() (values)]) '42)) 42)
  (test-equal (run-eval-e (let-values ([(x) '10]) (+ x '1))) 11)
  (test-equal (run-eval-e (let-values ([(x) '1]
                                       [(y z) (values '2 '3)])
                            (- x (+ y z))))
              -4)
  (test-equal (run-eval-e (let-values ([(y z) (values '2 '3)]
                                       [(x) '1])
                            (- x (+ y z))))
              -4)

  (test-equal (run-eval-e (letrec-values () '0)) 0)
  (test-equal (run-eval-e (letrec-values ([() (values)]) '1)) 1)

  (test-equal (run-eval-e
               (letrec-values
                   ([(even?)
                     (lambda (n)
                       (if (zero? n)
                           '#t
                           (odd? (- n '1))))]
                    [(odd?)
                     (lambda (n)
                       (if (zero? n)
                           '#f
                           (even? (- n '1))))])
                 (even? '10)))
              #t)

  (test-equal (run-eval-e
               (letrec-values
                   ([(even? odd?)
                     (values
                      (lambda (n)
                        (if (zero? n)
                            '#t
                            (odd? (- n '1))))
                      (lambda (n)
                        (if (zero? n)
                            '#f
                            (even? (- n '1)))))])
                 (even? '10)))
              #t)

  (test-equal (run-eval-e '"") "")
  (test-equal (run-eval-e '"hello") "hello")
  (test-equal (run-eval-e (string? '"")) #t)
  (test-equal (run-eval-e (string? '"cheese")) #t)
  (test-equal (run-eval-e (string? '#t)) #f)
  (test-equal (run-eval-e (string? '0)) #f)

  ;; XXX In the test form (string-append) parses as a metafunction
  ;; application, not as an object-language application expression. I
  ;; don't yet have a good way to write terms in jam that won't clash
  ;; with the specification. So, don't try to test string-append with
  ;; test-equal.
  ;; (test-equal (run-eval-e (string-append)) "")

  (test-equal (run-eval-e (vector-length (current-command-line-arguments))) 0)
  (test-equal (run-eval-e (vector? (vector))) #t)
  (test-equal (run-eval-e (vector? (vector-immutable))) #t)
  (test-equal (run-eval-e (vector? '1)) #f)
  (test-equal (run-eval-e (vector? '"hello")) #f)

  (test-equal (run-eval-e (begin '1)) 1)
  (test-equal (run-eval-e (begin '1 '2)) 2)
  (test-equal (run-eval-e (begin '1 '2 '3)) 3)
  (test-equal (run-eval-e (begin (values) '4)) 4)

  (test-equal (run-eval
               ('1
                (raise '#f)
                ((lambda (x) (x x)) (lambda (x) (x x)))))
              ())

  (jam-test))

(module+ main
  (require syntax/location "pycketlite-util.rkt")
  (define dest (build-path (syntax-source-directory #'here) "pycketlite"))
  (define interpreter-mode (make-parameter 'plain))
  (define run (make-parameter #f))
  (define build? (make-parameter #f))

  (command-line
   #:program "pycketlite"

   #:once-any
   ["--translated" "Use the translated interpreter"
                  (interpreter-mode 'translate)]
   ["--plain" "Use the untranslated interpreter (default)"
              (interpreter-mode 'plain)]

   #:once-any
   ["--repl" "Start a REPL where each input is run as a separate program"
             (run 'repl)]
   ["--stdin" "Read a single program from stdin, and run it"
              (run 'stdin)]
   ["--racket" path "Translate the Racket path to pycketlite and run it"
               (run path)]

   #:once-each
   ["--build" "Build the interpreter"
              (build? #t)])

  (unless (xor (build?) (run))
    (raise-user-error
     'pycketlite
     "Must do exactly one of run or build"))

  (define translate? (equal? (interpreter-mode) 'translate))

  (when (build?)
    (jam-build pl eval
       #:dest/delete dest
       #:translate? translate?))

  (match (run)
    ['repl
     (jam-run pl eval
       #:path dest
       #:translate? translate?)]
    ['stdin
     (parameterize ([read-accept-reader #f]
                    [read-accept-lang #f])
       (define input (read))
       (unless (eof-object? input)
         (parameterize ([current-input-port (open-input-string (~a input))])
           (jam-run pl eval
             #:path dest
             #:translate? translate?
             #:prompt? #f))))]
    [(? path-string? p)
     (define forms (path->pycketlite p))
     (parameterize ([current-input-port (open-input-string (~s forms))])
       (jam-run pl eval
         #:path dest
         #:translate? translate?
         #:prompt? #f))]
    [#f (void)]))

(module+ test
  (require syntax/location rackunit)
  (define racket (find-executable-path "racket"))

  (define (get-expect p)
    (define source (open-input-file p))
    (define expect/default "()\n")
    (define expect
      (match (read-string 2 source)
        ["#;" ;quote-terminated comment for racket-mode highlighting"
         (match (read source)
           [`(testout ,(? string? expect)) expect]
           [d
            (eprintf "unexpected datum in file ~a; got ~s\n" p d)
            expect/default])]
        [_
         expect/default]))

    (close-input-port source)
    expect)

  (define base (syntax-source-directory #'here))
  (parameterize ([current-output-port (open-output-nowhere)])
    (void (system* racket (quote-source-file) "--build")))
  (for ([p (directory-list (build-path base "racket") #:build? #t)]
        #:when (path-has-extension? p ".rkt")
        #:unless (member (path->string (file-name-from-path p))
                         '("info.rkt" "predefined.rkt")))
    (define out (open-output-string))
    (parameterize ([current-output-port out]
                   [current-error-port out])
      (system* racket (quote-source-file) "--racket" p))

    (check-equal? (get-output-string out) (get-expect p))))
