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
  (k ::= mt (appk env (e ...) (V ...) k) (ifk env e e k)))

(define-metafunction pl
  [(init-env)
   (env-extend
    env
    (+ - * zero?)
    ({env prim+} {env prim-} {env prim*} {env primzero?}))
   (where env (env-empty))])

(define-metafunction pl
  [(apply-op (lambda (x ...) e) env (V ...))
   (ret (env-extend env (x ...) (V ...)) e)]

  [(apply-op prim+ _ ({_ integer_1} {_ integer_2}))
   (ret (integer-add integer_1 integer_2))]

  [(apply-op prim- _ ({_ integer_1} {_ integer_2}))
   (ret (integer-subtract integer_1 integer_2))]

  [(apply-op prim* _ ({_ integer_1} {_ integer_2}))
   (ret (integer-multiply integer_1 integer_2))]

  [(apply-op primzero? _ ({_ 0}))
   (ret #t)]

  [(apply-op primzero? _ ({_ v}))
   (ret #f)])

(define-transition pl
  step
  [--> (x env k)
       (v env_v k)
       (where {env_v v} (env-lookup env x))]

  [--> ((e e_args ...) env k)
       (e env (appk env (e_args ...) () k))]

  [--> ((if e_test e_then e_else) env k)
       (e_test env (ifk env e_then e_else k))]

  [--> (v env_v (appk env (e_arg e_args ...) (V ...) k))
       (e_arg env (appk env (e_args ...) ({env_v v} V ...) k))]

  [--> (v env_v (appk _ () (V ...) k))
       (e env_e k)
       (where ({env_op v_op} V ...) (reverse ({env_v v} V ...)))
       (where (env_e e) (apply-op v_op env_op (V ...)))]

  [--> (#f _ (ifk env _ e_else k))
       (e_else env k)]

  [--> (v _ (ifk env e_then _ k))
       (e_then env k)])

(define-metafunction pl
  [(ret v) ((env-empty) v)]
  [(ret env e) (env e)])

(define-evaluator pl
  eval
  #:load [--> e (e (init-env) mt)]
  #:unload [--> (v _ mt) v]
  #:transition step
  #:control-string [(e _ _) e])

(module+ test
  (current-test-language pl)
  (test-equal (run-eval (+ 1 2)) 3)
  (test-equal (run-eval ((lambda (x) x) 10)) 10)
  (test-equal (run-eval (((lambda (x) (lambda (y) x)) 5) 6))
              5)
  (test-equal (run-eval ((lambda (f x) (f x)) zero? 0)) #t)
  (test-equal (run-eval ((lambda (f x) (f x)) (lambda (n) (+ n 1)) 0)) 1)

  (test-equal (run-eval
               ((lambda (fib) (fib fib 8))
                (lambda (rec n)
                  (if (zero? n)
                      0
                      (if (zero? (- n 1))
                          1
                          (+ (rec rec (- n 1))
                             (rec rec (- n 2))))))))
              21)

  (test-equal (run-eval
               ((lambda (fact) (fact fact 10))
                (lambda (rec n)
                  (if (zero? n)
                      1
                      (* n (rec rec (- n 1)))))))
              3628800)

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
   ["--repl" "Start a REPL where each input is run run as a separate program"
             (run 'repl)]
   ["--stdin" "Read a single program from stdin, and run it"
              (run 'stdin)]

   #:once-each
   ["--build" "Build the interpreter"
              (build? #t)])

  (when (and (not (build?)) (not (run)))
    (raise-user-error
     'pycketlite
     "Must at least run or build an interpreter"))

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
     (parameterize* ([read-accept-reader #f]
                     [read-accept-lang #f])
       (define input (read))
       (unless (eof-object? input)
         (parameterize ([current-input-port (open-input-string (~a input))])
           (jam-run pl eval
             #:path dest
             #:translate? translate?
             #:prompt? #f))))]
    [#f (void)]))
