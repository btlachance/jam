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

(define-language env
  #:data ([env (environment integer integer)]))

;; Defining a metafunction is the closest thing we have to writing
;; sequential code; Something like Redex's term-let seems useful for
;; testing.
(define-metafunction env
  [(envtest)
   ((env-lookup env 3)
    (env-lookup env 2)
    (env-lookup env 1))
   (where env (env-extend-cells (env-empty) (1 2 3)))
   (where () (env-set-cells env (1 2 3) (4 5 6)))
   (where #f (env-bound? env 4))])
(define-metafunction env
  [(extend1test)
   ((env-lookup env 1)
    (env-lookup env 10)
    (env-lookup env 100))
   (where env (env-extend1 (env-empty) 1 9))
   (where env (env-extend1 env 10 90))
   (where env (env-extend1 env 100 900))])

(module+ test
  (current-test-language env)
  (test-equal (envtest) (6 5 4))
  (test-equal (extend1test) (9 90 900))

  (test-not-equal (clock-milliseconds) 0)
  (test-equal (integer-multiply (clock-milliseconds) 0) 0)
  (jam-test))

(define-language vec
  #:data ([mvec (mutable-sequence boolean)]
          [ivec (immutable-sequence boolean)]))
(define-metafunction vec
  [(mut-test)
   (mvec-element-at mvec 1)
   (where mvec (mvec-of-elements #t #t #t))
   (where () (mvec-set mvec 1 #f))])
(module+ test
  (current-test-language vec)
  (test-equal (mvec-length (mvec-of-elements)) 0)
  (test-equal (mvec-length (mvec-of-elements #t #f)) 2)
  (test-equal (mut-test) #f)

  (test-equal (ivec-length (ivec-of-elements)) 0)
  (test-equal (ivec-length (ivec-of-elements #t #f #t)) 3)
  (jam-test))

(define-language str
  (s ::= string))
(define-metafunction str
  [(str-test)
   (string-append string_1 string_2)
   (where (string_1 string_2) ("toast" "jam"))])
(module+ test
  (current-test-language str)
  (test-equal (str-test) "toastjam")
  (test-not-equal (str-test) "jamtoast")
  (test-equal (string-length "") 0)
  (test-equal (string-length "fish") 4)
  (test-not-equal (string-length "chips") 0)
  (jam-test))

(define-language file
  #:data ([file (file)]))
(module+ test
  (current-test-language file)
  (test-equal (file-write (file-stdout) "bread") ())
  (test-equal (file-write (file-stderr) "butter") ())
  (jam-test))

(define-language under
  (e ::= x (lambda (x) _) (_ _))
  (x ::= variable-not-otherwise-mentioned))
(module+ test
  (current-test-language under))

(define-metafunction under
  [(append () ((name ys _) ...))
   (ys ...)]
  [(append ((name x _) (name xs _) ...) ((name ys _) ...))
   (x zs ...)
   (where ((name zs _) ...) (append (xs ...) (ys ...)))])

(module+ test
  (test-equal (append () ()) ())
  (test-equal (append (1 #t 3) (4 #f 6)) (1 #t 3 4 #f 6)))

(define-metafunction under
  [(vars-of x) (x)]
  [(vars-of (lambda (x) e)) (vars-of e)]
  [(vars-of (e_1 e_2))
   (append (x_1 ...) (x_2 ...))
   (where (x_1 ...) (vars-of e_1))
   (where (x_2 ...) (vars-of e_2))])

(module+ test
  (test-equal (vars-of x) (x))
  (test-equal (vars-of (lambda (y) x)) (x))
  (test-equal (vars-of ((x y) x)) (x y x))

  (test-equal (system*/json-term "/bin/echo" "{\"integer\": 1}") 1)
  (test-equal (system*/json-term "/bin/echo" "{\"string\": \"sslothh\"}")
              "sslothh")
  (test-equal (system*/json-term "/bin/echo" "{\"boolean\": false}")
              #f)

  (jam-test))

(define-language real)
(define-metafunction real
  [(add real_1 real_2)
   real_result
   (where real_result (real-add real_1 real_2))])

(module+ test
  (current-test-language real)
  (test-equal 1.0 1.0)
  (test-equal (real-add 1.0 1.0) 2.0)
  (test-equal (real-multiply 10.0 0.0) 0.0)
  (test-equal (real-subtract 5.0 4.0) 1.0)
  (test-equal (add 1.0 1.0) 2.0)
  (test-not-equal 0.0 0.1)

  (test-equal (integer->real 1) 1.0)
  (test-equal (real->integer 0.0) 0)
  (test-equal (real->integer 0.5) 0)
  (test-equal (real->integer 1.9) 1)

  (test-equal (integer-= 1 1) #t)
  (test-equal (integer-= 5 1) #f)
  (test-equal (integer-< 1 5) #t)
  (test-equal (integer-< 5 1) #f)
  (test-equal (real-= 5.0 5.0) #t)
  (test-equal (real-= 5.0 -1.0) #f)
  (test-equal (real-< 4.0 5.0) #t)
  (test-equal (real-< 5.0 4.0) #f)

  (test-equal (string-= "" "") #t)
  (test-equal (string-= "hello" "chips") #f)
  (test-equal (string-= "chips" "chips") #t)

  (jam-test))
