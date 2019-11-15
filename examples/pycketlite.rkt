#lang racket
(require jam)
(provide pl)

(define-language pl
  #:data ([env (environment x loc)]
          [store (store loc _)]
          [loc (location)]
          [mvec (mutable-sequence _)]
          [ivec (immutable-sequence _)]
          [file (file)])

  (P     ::= (t ...))
  (t     ::= e (define-values (x ...) e))
  (e     ::= x l (quote c) (e e ...) (if _ _ _)
             (let-values ([(x ...) _] ...) _ _ ...)
             (letrec-values ([(x ...) _] ...) _ _ ...)
             (begin _ _ ...)
             (set! x _))
  (l     ::= (lambda (x ...) _ _ ...)
             (lambda x _ _ ...)
             (lambda (x ...) (dot x) _ _ ...))

  (x y z ::= variable-not-otherwise-mentioned)
  (c     ::= integer real boolean string (#%s string))

  ;; XXX If locations aren't values, then it's tricky to implement
  ;; things like eq? using location-equality: Since the interface to
  ;; eq? is just like any other function, the argument expressions are
  ;; evaluted to values. So the value for a cons would have to contain
  ;; its location if we want eq? to be able to take a value and
  ;; somehow know its location.
  ;;
  ;; Alternatively, if expressions evaluate to locations, then even
  ;; things like an integer constant get stored in a location. That's
  ;; consistent at least with Racket's documentation on variables and
  ;; locations.
  ;;
  ;; We could also split the difference (at the cost of some
  ;; complexity) and have certain expressions evaluate to locations
  ;; and others evaluate just to their value.

  (V     ::= {env l} c mvec ivec file (cont _)
             #%+ #%- #%* #%/ #%zero? #%exact-integer? #%inexact? #%= #%<
             #%inexact->exact #%exact->inexact #%number?
             #%sin #%quotient #%remainder
             (#%cons _ _) #%null #%cons #%car #%cdr #%null? #%pair? #%list
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
             #%current-inexact-milliseconds
             #%call-with-current-continuation)

  (k     ::= k1 k*)
  (k1    ::= (appk env (e ...) (V ...) e _) (ifk env e e _) (setk x env _))
  ;; It's a little funky that we keep the store also in topk but it's
  ;; an artifact of how we initialize the machine. An alternative
  ;; would be an initial state like (store env (topk P)). Which gives
  ;; me an idea that defk could be changed to (defk (x ...) P)
  (k*    ::= (topk env store P) (defk (x ...) env P) (cwvk V _)

             ;; env               environment for remaining RHS
             ;; (x ...)           variables the current RHS results will be bound to
             ;; ([(x ...) e] ...) remaining variables to bind/RHS to evaluate
             ;; (x ...)           variables and
             ;; (V ...)           values for evaluated RHS so far
             ;; (e e ...)         body expressions
             ;;
             ;; (We could keep the list of variables/values as two
             ;; lists instead of one zipped one if we had an explicit
             ;; way to check that #values returned to the continuation
             ;; matched #variables for the current RHS)
             (letk env (x ...) ([(x ...) e] ...) (x ...) (V ...) (e e ...) _)

             ;; Like letk but RHS and the body are evaluated in the
             ;; same environment, and values are set in that
             ;; environment once they're available, so no need for a
             ;; separate list of variables/values so far
             (letreck env (x ...) ([(x ...) e] ...) (e e ...) _)

             (begink env (e e ...) _)))

(module+ test
  (current-test-language pl))

(define-metafunction pl
  [(init-env-store (x_toplevel ...))
   (env store)
   (where ((x ...) (V ...))
              ((  +   -   *   /   zero?   exact-integer?   inexact?   =   <
                  inexact->exact   exact->inexact   number?
                  sin   quotient   remainder
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
                  current-inexact-milliseconds
                  call-with-current-continuation)
               (#%+ #%- #%* #%/ #%zero? #%exact-integer? #%inexact? #%= #%<
                #%inexact->exact #%exact->inexact #%number?
                #%sin #%quotient #%remainder
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
                #%current-inexact-milliseconds
                #%call-with-current-continuation)))
   (where store (store-empty))
   (where (loc ...) (store-fresh-distinct-locations store (x ...)))
   (where env (env-extend (env-empty) (x ...) (loc ...)))
   (where () (store-extend store (loc ...) (V ...)))
   (where (loc ...) (store-fresh-distinct-locations store (x_toplevel ...)))
   (where env (env-extend env (x_toplevel ...) (loc ...)))])

(define-metafunction pl
  [(appk-header (appk _ () _ e_orig _)) e_orig]
  [(appk-header (appk _ (e _ ...) _ _ _)) e]
  [(appk-header _) ()])

(define-metafunction pl
  [(return-loop (e _ _ k)) (appk-header k)]
  [(return-loop (V _ k)) (appk-header k)]
  [(return-loop ((#%values V) _ k)) (appk-header k)]
  [(return-loop _) ()])

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
  [(flatten-vars (cons* () (name rest ((x ...) ...))))
   (flatten-vars rest)]
  [(flatten-vars (cons* (cons* x_0 (name xs (x_rest ...))) (name rest ((x ...) ...))))
   (cons* x_0 flat)
   (where (name flat (x_flattened ...)) (flatten-vars (cons* xs rest)))])

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

  ;; XXX Really need rationals here
  [(apply-op #%/ (integer_1 integer_2))
   (integer-divide integer_1 integer_2)]

  [(apply-op #%+ (real_1 real_2))
   (real-add real_1 real_2)]

  [(apply-op #%- (real_1 real_2))
   (real-subtract real_1 real_2)]

  [(apply-op #%* (real_1 real_2))
   (real-multiply real_1 real_2)]

  [(apply-op #%/ (real_1 real_2))
   (real-divide real_1 real_2)]

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

  [(apply-op #%sin (real))
   (real-sin real)]

  [(apply-op #%sin (integer))
   0
   (where 0 integer)]

  [(apply-op #%sin (integer))
   (real-sin (integer->real integer))]

  [(apply-op #%quotient (integer_1 integer_2))
   integer_q
   (where (integer_q _) (integer-divmod integer_1 integer_2))]

  [(apply-op #%remainder (integer_1 integer_2))
   integer_r
   (where (_ integer_r) (integer-divmod integer_1 integer_2))]

  [(apply-op #%quotient (real_1 real_2))
   real_q
   (where (real_q _) (real-divmod real_1 real_2))]

  [(apply-op #%remainder (real_1 real_2))
   real_r
   (where (_ real_r) (real-divmod real_1 real_2))]

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
  [(prefix-and-rest () (name rest (V_rest ...)))
   (() (apply-op #%list rest))]
  [(prefix-and-rest (cons* x (name ys (y ...))) (cons* V_0 (name vs (V ...))))
   ((cons* V_0 prefix) V_rest)
   (where ((name prefix (V_prefix ...)) V_rest) (prefix-and-rest ys vs))])

(define-metafunction pl
  [(begink* env () k) k]
  [(begink* env (name es (e e_rest ...)) k) (begink env es k)])

(define-metafunction pl
  [(reverse-args-onto (cons* #%null (name vs (V ...))))
   vs]
  [(reverse-args-onto (cons* (#%cons V_1 V_2) (name vs (V ...))))
   (reverse-args-onto (cons* V_2 (cons* V_1 vs)))])

(define-metafunction pl
  [(apply-proc {env_op (name callee _)} (name vs (V ...)) e_orig store k)
   (e env_e store (begink* env_e es k))
   (where (cons* lambda (cons* (name xs _) (cons* e (name es (e_rest ...))))) callee)
   (where (x ...) xs)
   (where (name locs (loc ...)) (store-fresh-distinct-locations store xs))
   (where env_e (env-extend env_op xs locs))
   (where () (store-extend store locs vs))
   (where () (register-call e_orig callee (appk-header k)))]

  [(apply-proc {env_op (cons* lambda (cons* x (cons* e (name es (e_rest ...)))))} (name vs (V ...)) e_orig store k)
   (e env_e store (begink* env_e es k))
   (where (loc) (store-fresh-distinct-locations store (x)))
   (where env_e (env-extend env_op (x) (loc)))
   (where () (store-extend store (loc) ((apply-op #%list vs))))
   (where () (can-enter! e))]

  [(apply-proc {env_op l} (name vs (V ...)) e_orig store k)
   (e env_e store (begink* env_e es k))
   (where (cons* lambda (cons* (name xs (x ...)) (cons* (dot y) (cons* e (name es (e_rest ...)))))) l)
   (where ((name prefix (V_prefix ...)) V_rest) (prefix-and-rest xs vs))
   (where (name args (x_args ...)) (append xs (y)))
   (where (name locs (loc ...)) (store-fresh-distinct-locations store args))
   (where env_e (env-extend env_op
                            args
                            locs))
   (where () (store-extend store locs (append prefix (V_rest))))
   (where () (can-enter! e))]

  [(apply-proc #%apply (cons* V_fun (name args (V_args ...))) e_orig store k)
   (apply-proc V_fun (reverse (reverse-args-onto args)) e_orig store k)
   (where (name args (V ...)) (reverse args))]

  [(apply-proc #%values (name vals (V_vals ...)) e_orig store k)
   ((cons* #%values vals) store k)]

  [(apply-proc #%call-with-values (V_producer V_consumer) e_orig store k)
   (e env store (begink* env es (cwvk V_consumer k)))
   ;; XXX This isn't exactly what Racket does; if the producer has a
   ;; 0-arg body then the 0-arg body is used. Otherwise an error is
   ;; raised. What I currently have rules out things like (lambda x e
   ;; e_rest ...)
   (where {env (cons* lambda (cons* () (cons* e (name es (e_rest ...)))))} V_producer)
   (where () (can-enter! e))]

  ;; XXX this isn't quite right in terms of top-level begin
  ;; expressions but it's enough for fibc
  [(apply-proc #%call-with-current-continuation (V) e_orig store k)
   ((cont k) store (appk env () (V) e_orig k))]

  [(apply-proc (cont k) (name rest (V_rest ...)) e_orig store _)
   ((cons* #%values rest) store k)]

  [(apply-proc V_op (name vs (V ...)) e_orig store k)
   (V_result store k)
   (where V_result (apply-op V_op vs))])

(define-transition pl
  step

  [--> (topk env store (cons* t (name rest (t_rest ...))))
       (t (topk env store rest))]

  [--> (e (topk env store P))
       (e env store (topk env store P))]

  [--> ((define-values (name vars (x ...)) e) (topk env store P))
       (e env store (defk vars env P))]

  [--> (x env store k)
       (V store k)
       (where V (store-dereference store (env-lookup env x)))]

  [--> (l env store k)
       ({env l} store k)]

  [--> ((quote c) env store k)
       (c store k)]

  [--> ((name orig e) env store k)
       (e env store (appk env args () orig k))
       (where (cons* e (name args (e_args ...))) orig)]

  [--> ((if e_test e_then e_else) env store k)
       (e_test env store (ifk env e_then e_else k))]

  [--> ((cons* let-values (cons* () (cons* e (name rest (e_rest ...))))) env store k)
       (e env store (begink* env rest k))]

  [--> ((cons* let-values (cons* (cons* [(name first (x_first ...)) e_first]
                                        (name rest ([(x_rest ...) e_rest] ...)))
                                 (name body (e_body ...)))) env store k)
       (e_first env store (letk env first rest
                                () () body k))]

  [--> ((cons* letrec-values (cons* () (cons* e (name rest (e_rest ...))))) env store k)
       (e env store (begink* env rest k))]

  [--> ((cons* letrec-values (cons* (name bps _) (name body (e_body ...)))) env store k)
       (e_first env_rec store (letreck env_rec first rest body k))
       (where ([(x ...) e] ...) bps)
       (where (cons* [(name first (x_first ...)) e_first] (name rest ([(x_rest ...) e_rest] ...))) bps)
       (where (name xs (x_vars ...)) (flatten-vars ((x ...) ...)))
       (where (name locs (loc ...)) (store-fresh-distinct-locations store xs))
       (where env_rec (env-extend env xs locs))]

  [--> ((cons* begin (cons* e (name rest (e_rest ...)))) env store k)
       (e env store (begink* env rest k))]

  [--> ((set! x e) env store k)
       (e env store (setk x env k))]

  [--> (V store k*)
       ((#%values V) store k*)]
  [--> ((#%values V) store k1)
       (V store k1)]

  [--> ((#%values V ...) store (topk env_top _ P))
       (topk env_top store P)]

  [--> ((cons* #%values (name vs (V ...))) store (defk (x ...) env_top P))
       (topk env_top store P)
       (where (name locs (loc ...)) ((env-lookup env_top x) ...))
       (where () (store-extend store locs vs))]

  [--> (V_0 store (appk env (cons* e_arg (name es (e_args ...))) (name vs (V ...)) e_orig k))
       (e_arg env store (appk env es (cons* V_0 vs) e_orig k))]

  [--> (V store (appk _ () (#%raise) e_orig k))
       (topk (env-empty) store ())]

  [--> (V_0 store (appk _ () (name vs (V ...)) e k))
       (apply-proc V_proc args e store k)
       (where (cons* V_proc (name args (V_args ...))) (reverse (cons* V_0 vs)))]

  [--> ((cons* #%values (name vs (V ...))) store (cwvk V_consumer k))
       (V_lastval store (appk (env-empty) () vs (quote #f) k))
       (where (cons* V_lastval (name vs (V ...))) (reverse (cons* V_consumer vs)))]

  [--> ((cons* #%values (name Vnew _))
        store
        (letk env_e (name xnew _) (name remaining _)
              (name xsofar _) (name Vsofar _)
              (name body _) k))
       (e env_e store (letk env_e xs rest
                            (append xnew xsofar)
                            (append Vnew Vsofar)
                            body k))
       (where #t (same-length? xnew Vnew))
       (where (cons* [(name xs (x ...)) e] (name rest ([(x_rest ...) e_rest] ...))) remaining)]

  [--> ((cons* #%values (name new (V_new ...)))
        store
        (letk env (name xs _) ()
              (name xsofar _) (name Vsofar _)
              (cons* e (name rest _)) k))
       (e env_body store (begink* env_body rest k))
       (where #t (same-length? xs new))
       (where (name all _) (append xs xsofar))
       (where (name locs _) (store-fresh-distinct-locations store all))
       (where env_body (env-extend env
                                   all
                                   locs))
       (where () (store-extend store locs (append new Vsofar)))]

  [--> ((cons* #%values (name new (V_new ...)))
        store
        (letreck env_rec (x_new ...)
                 (name remaining _)
                 (name body (e_body ...)) k))
       (e env_rec store (letreck env_rec xs
                                 rest
                                 body k))
       (where (cons* [(name xs (x ...)) e] (name rest ([(x_rest ...) e_rest] ...))) remaining)
       (where (name locs (loc ...)) ((env-lookup env_rec x_new) ...))
       (where () (store-extend store locs new))]

  [--> ((cons* #%values (name new (V_new ...)))
        store
        (letreck env_rec (x_new ...) () (cons* e (name rest (e_rest ...))) k))
       (e env_rec store (begink* env_rec rest k))
       (where (name locs (loc ...)) ((env-lookup env_rec x_new) ...))
       (where () (store-extend store locs new))]

  [--> ((#%values V ...) store (begink env (cons* e (name rest (e_rest ...))) k))
       (e env store (begink* env rest k))]

  [--> (#f store (ifk env _ e_else k))
       (e_else env store k)]

  [--> (V store (ifk env e_then _ k))
       (e_then env store k)]

  [--> (V store (setk x env k))
       (#%void store k)
       (where loc (env-lookup env x))
       (where () (store-update-location store loc V))])

(define-evaluator pl
  eval

  #:load [--> P_user (topk env_init store_init P)
              (where P_predef (load-pl "/Users/blachance/projects/jam/examples/racket/predefined.rkt"))
              (where P (append P_predef P_user))
              (where (env_init store_init) (init-env-store (toplevel-names P)))]

  #:unload [--> (topk _ _ ()) ()] ;; XXX maybe call an exit metafunction
                                ;; here, indicating a succesful
                                ;; termination?
  #:transition step
  #:control-string [(e _ _ _) e])

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

  #:load [--> e (topk env_init store_init (e))
              (where (env_init store_init) (init-env-store ()))]
  #:unload [--> ((#%values V) _ (topk _ _ ())) (unload V)]
  #:transition step
  #:control-string [(e _ _ _) e])

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

  (test-equal (run-eval-e (apply (lambda x x) '1 (list '2 '3)))
              (#%cons 1 (#%cons 2 (#%cons 3 #%null))))
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

  (test-equal (run-eval-e (let-values ([(x) '0])
                            (if (< x '0)
                                (begin
                                  (set! x (+ x '1))
                                  x)
                                x)))
                          0)
  (test-equal (run-eval-e (let-values ([(x) '0])
                            (set! x (+ '1 x))
                            (set! x (+ '1 x))
                            x))
              2)
  (test-equal (run-eval-e (let-values ([(x) '0])
                            (let-values ([(inc)
                                          (lambda ()
                                            (set! x (+ '1 x))
                                            x)])
                              (inc)
                              (inc)
                              (inc))))
              3)

  (test-equal (run-eval-e (call-with-current-continuation
                           (lambda (k) (/ '0 (k '1)))))
              1)

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

#;(module+ test
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

    (with-check-info
      (['source p])
      (check-equal? (get-output-string out) (get-expect p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Run
;;      racket pycketlite.rkt --build --plain
;;  
;;  Then hack up pycketlite/pl_evaluator.py by copying the Python mess
;;  below, and replacing everything in pycketlite/pl_evaluator.py from
;;  the definition of eval_driver down with the copied Python mess.
;;  
;;  Then, translate the binary by running
;;      (cd pycketlite && JAM_BINARY_NAME=eval rpython -Ojit target.py)
;;
;;  Run a foo.rkt using the translated binary by running
;;      racket pycketlite.rkt --racket foo.rkt --translated

#|
def get_printable_location(c, prev_c, ret):
  if ret.is_none():
    return c.to_toplevel_string()
  else:
    enter = "Enter " if ret.can_enter_return() else ""
    return '%s (%s%s)' % (c.to_toplevel_string(), enter, ret.to_toplevel_string())
eval_driver = jit.JitDriver(reds = (["t", "tmp"]), greens = (["c", "prev_c", "ret"]), get_printable_location = get_printable_location)
def eval(t):
  try:
    t = eval_load(t)
    tmp = core.make_none()
    c = core.make_none()
    prev_c = core.make_none()
    ret = core.make_none()
    t.mark_static()
    core.set_surrounding_lambda(t)
    while True:
      eval_driver.jit_merge_point(c = c, prev_c = prev_c, ret = ret, t = t, tmp = tmp)
      eval_unload(t)
      t = step(t)
      tmp = eval_control_string(t)
      if tmp.static:
        if not c.is_none():
          prev_c = c
        c = tmp
      else:
        c = core.make_none()

      tmp = pl_metafun.return_loop(core.term_list([t]))
      if tmp.static and not core.is_nil(tmp):
        ret = tmp
      else:
        ret = core.make_none()

      if c.can_enter():
        eval_driver.can_enter_jit(c = c, prev_c = prev_c, ret = ret,
                                  t = t, tmp = tmp)
      elif ret.can_enter_return():
        eval_driver.can_enter_jit(c = c, prev_c = prev_c, ret = ret,
                                  t = t, tmp = tmp)
  except core.JamDone as d:
    return d.v
  except core.JamError as e:
    print("Jam Error: %s" % e.s)
    if t:
      print("Current term: %s" % t.to_toplevel_string())
    else:
      print("No current term")
    return core.make_none()
  except Exception as e:
    print("Internal Error: %s" % e)
    print("Current term:\n%s" % t.to_toplevel_string())
    return core.make_none()
  finally:
    import os
    # For some reason os.getenv would complain about the number of
    # arguments, so instead just access os.environ directly
    dest = os.environ.get('JAM_CALLGRAPH_FILE')
    if dest is not None:
      if dest == '': # Just setting JAM_CALLGRAPH_FILE= means to use a default dest
        dest = 'callgraph.dot'
      with open(dest, 'w') as out:
        core.call_graph.write_dot_file(out)
    if core.stdout:
      core.stdout.flush()
    if core.stderr:
      core.stderr.flush()
|#
