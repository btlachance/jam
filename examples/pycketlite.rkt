#lang racket
(require jam)
(provide pl)

(define-language pl
  #:data ([env (environment x V)])

  (P     ::= (t ...))
  (t     ::= e (define-values (x) e)) ;; general-top-level-form but
                                      ;; only with single-val define
  (e     ::= x l (quote c) (e e ...)
             (if e e e))
  (l     ::= (lambda (x ...) e) (lambda x e) (lambda (x ...) (dot x) e))

  (x y z ::= variable-not-otherwise-mentioned)
  (c     ::= integer boolean)

  (V ::= {env l} c
         #%+ #%- #%* #%zero?
         (#%cons V V) #%null #%cons #%car #%cdr #%null? #%pair? #%list
         #%apply)
  (k ::= (appk env (e ...) (V ...) k) (ifk env e e k)
         (defk (x) env P) (topk env P)))

(define-metafunction pl
  [(init-env (x_toplevel ...))
   env

   (where env (env-empty))
   (where env (env-extend
               env
               (  +   -   *   zero?
                  cons   null   car   cdr   null?   pair?   list
                  apply)
               (#%+ #%- #%* #%zero?
                #%cons #%null #%car #%cdr #%null? #%pair? #%list
                #%apply)))
   (where env (env-extend-cells env (x_toplevel ...)))])

(define-metafunction pl
  [(toplevel-names ())
   ()]

  [(toplevel-names (e t ...))
   (toplevel-names (t ...))]

  [(toplevel-names ((define-values (x) _) t ...))
   ;; Current template language doesn't allow (x ... x_rest ...)
   ;; which looks a lot like appending two lists
   (x x_rest ...)
   (where (x_rest ...) (toplevel-names (t ...)))])

(define-metafunction pl
  [(apply-op #%+ (integer_1 integer_2))
   (integer-add integer_1 integer_2)]

  [(apply-op #%- (integer_1 integer_2))
   (integer-subtract integer_1 integer_2)]

  [(apply-op #%* (integer_1 integer_2))
   (integer-multiply integer_1 integer_2)]

  [(apply-op #%zero? (0))
   #t]

  [(apply-op #%zero? (V))
   #f]

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
   (#%cons V (apply-op #%list (V_rest ...)))])

(define-metafunction pl
  [(prefix-and-rest () (V_rest ...))
   (() (apply-op #%list (V_rest ...)))]
  [(prefix-and-rest (x y ...) (V_0 V ...))
   ((V_0 V_prefix ...) V_rest)
   (where ((V_prefix ...) V_rest) (prefix-and-rest (y ...) (V ...)))])

(define-transition pl
  step
  [--> (topk env (t t_rest ...))
       (t (topk env (t_rest ...)))]

  [--> (e (topk env P))
       (e env (topk env P))]

  [--> ((define-values (x) e) (topk env P))
       (e env (defk (x) env P))]

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


  [--> (V (topk env_top P))
       (topk env_top P)]

  [--> (V (defk (x) env_top P))
       (topk env_top P)
       (where () (env-set-cells env_top (x) (V)))]

  [--> (V_0 (appk env (e_arg e_args ...) (V ...) k))
       (e_arg env (appk env (e_args ...) (V_0 V ...) k))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e k)
       (where ({env_op (lambda (x ...) e)} V ...) (reverse (V_0 V ...)))
       (where env_e (env-extend env_op (x ...) (V ...)))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e k)
       (where ({env_op (lambda x e)} V ...) (reverse (V_0 V ...)))
       (where env_e (env-extend env_op (x) ((apply-op #%list (V ...)))))]

  [--> (V_0 (appk _ () (V ...) k))
       (e env_e k)
       (where ({env_op (lambda (x ...) (dot y) e)} V ...) (reverse (V_0 V ...)))
       (where ((V_prefix ...) V_rest) (prefix-and-rest (x ...) (V ...)))
       ;; With append-like templates, this would instead be
       ;; (env-extend env_op (x ... y) (V_prefix ... V_rest))
       (where env_e (env-extend env_op (x ...) (V_prefix ...)))
       (where env_e (env-extend env_e (y) (V_rest)))]

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
       (V_result k)
       (where (V_op V ...) (reverse (V_0 V ...)))
       (where V_result (apply-op V_op (V ...)))]

  [--> (#f (ifk env _ e_else k))
       (e_else env k)]

  [--> (V (ifk env e_then _ k))
       (e_then env k)])

(define-evaluator pl
  eval

  #:load [--> P (topk (init-env (toplevel-names P)) P)]

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
  #:unload [--> (V (topk _ ())) (unload V)]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (current-test-language pl)
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
                (even? '100)))
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

  (jam-test))

(module+ main
  (require syntax/location)
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
   ;; TODO support running a program at a particular path. If we want
   ;; to cache the term->json process, though, then we need to either
   ;; change the evaluation handler or not go through the REPL (which
   ;; is hard-coded into jam-run) since it does its own term->json
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
     (parameterize ([read-accept-reader #t]
                    [read-accept-lang #t]
                    [current-namespace (make-base-namespace)]
                    [current-input-port (open-input-file p)])
       (define stx (read-syntax))
       (begin0 (unless (eof-object? stx)
                 (define p (module->pycketlite (expand stx)))
                 (parameterize ([current-input-port (open-input-string (~a p))])
                   (jam-run pl eval
                     #:path dest
                     #:translate? translate?
                     #:prompt? #f)))
         (close-input-port (current-input-port))))]
    [#f (void)]))

(require syntax/parse)
(define (module->pycketlite stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(module name lang
       (#%module-begin mod-config
                       forms ...))
     (map form->pycketlite (attribute forms))]))

(define (form->pycketlite f)
  (syntax-parse f
    #:literal-sets (kernel-literals)
    #:datum-literals (call-with-values)
    [(#%plain-app call-with-values (lambda () e) print-values)
     (expr->pycketlite #'e)]

    [(define-values (x) e)
     `(define-values (,(syntax-e #'x)) ,(expr->pycketlite #'e))]))

(define (expr->pycketlite e)
  (syntax-parse e
    #:literal-sets (kernel-literals)
    [(#%plain-lambda (x ...) e)
     `(lambda ,(map syntax-e (attribute x)) ,(expr->pycketlite #'e))]

    [(#%plain-lambda x:id e)
     `(lambda ,(syntax-e #'x) ,(expr->pycketlite #'e))]

    [(#%plain-lambda (x ... . y) e)
     `(lambda ,(map syntax-e (attribute x)) (dot ,(syntax-e #'y))
              ,(expr->pycketlite #'e))]

    [(if e1 e2 e3)
     `(if ,(expr->pycketlite #'e1)
          ,(expr->pycketlite #'e2)
          ,(expr->pycketlite #'e3))]

    [(quote {~or :exact-integer :boolean}) (syntax->datum this-syntax)]

    [(#%plain-app e e* ...)
     (cons (expr->pycketlite #'e) (map expr->pycketlite (attribute e*)))]

    [x:id (syntax-e #'x)]))

(module+ test
  (require syntax/location rackunit)
  (define racket (find-executable-path "racket"))

  (match-define-values (base _ _) (split-path (quote-source-file)))
  (void (system* racket (quote-source-file) "--build"))
  (define out (open-output-nowhere))
  (for ([p (directory-list (build-path base "racket") #:build? #t)]
        #:when (equal? (path-get-extension p) ".rkt")
        #:unless (equal? (path->string (file-name-from-path p)) "info.rkt"))
    (check-true
     (parameterize ([current-output-port out])
       (system* racket (quote-source-file) "--racket" p)))))
