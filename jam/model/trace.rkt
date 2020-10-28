#lang racket
(require redex syntax/parse/define pict)

(define-language trace-source
  ;; object language
  (     x ::= variable-not-otherwise-mentioned)
  (     v ::= #t #f integer '() (cons v v))
  (     p ::= boolean? integer? null? cons? zero? positive? negative?
          cons car cdr + * -)
  (     e ::= x (app x e ...) (app p e ...) (if e e e) (lit v))

  (     d ::= ((x (x ...) e) ...))
  (     r ::= ((x v) ...)))

(define-metafunction trace-source
  ;; TODO add more cases
  [(apply-prim* cons v_1 v_2)
   (cons v_1 v_2)]
  [(apply-prim* null? '()) #t]
  [(apply-prim* null? v) #f
   (side-condition (not (null? (term v))))]
  [(apply-prim* car (cons v_1 v_2)) v_1]
  [(apply-prim* cdr (cons v_1 v_2)) v_2])

(module+ test
  (test-equal (term (apply-prim* null? 1)) #f)
  (test-equal (term (apply-prim* null? '())) #t))

(define-judgment-form trace-source
  #:contract (apply-prim p (v ...) v)
      #:mode (apply-prim I I       O)
  [(where v_out (apply-prim* p v ...))
   -------------------------------------
   (apply-prim p (v ...) v_out)])

(define rewrite-apply-prim
  (match-lambda
    [(list _ _ p vs v _)
     (list "" "δ(" p "," vs ") = " v "")]))

(define-extended-language trace-target trace-source
  ;; trace language

  ;; I want every call in the trace language to either be a prim call
  ;; or a trace call, and (m m ...) as a body is a little too general,
  ;; it allows arbitrary variables, lambdas, and values in the
  ;; function position---a type system could rule that out, sure, but
  ;; I'll just make the syntax a little clearer. (For trace calls, I
  ;; need a separate syntactic form then, e.g. a new form of q for
  ;; naming a trace or a different call form)

  ( env y ::= variable-not-otherwise-mentioned)
  (     f ::=
          y
          (p y ...)
          (if y f f)
          (lit v)
          (lookup env 'x)
          (let ([y f] [y f] ...) f)
          (extend env (['x y] ...))
          (exit env 'e))

  (     t ::= (lambda (env) f))
  (     C ::= ((y t) ...)))

(define-union-language trace trace-source trace-target)

(module+ test
  (define-simple-macro (test-trace? e) (test-match trace t (term e)))
  (define-simple-macro (test-no-trace? e) (test-no-match trace t (term e)))

  ;; Note: if prims can be curried, which they could be when body
  ;; forms included (body a ...), then if we shuffle the arguments
  ;; order for lookup, trace for x can just be
  ;; 
  ;;     (lookup 'x) = (lambda (env k) ((lookup 'x) env k))
  ;;
  ;; not sure if that pays off as a way to simplify other traces,
  ;; though

  ;; x
  (test-trace? (lambda (env) (lookup env 'x)))

  ;; (if x 0 1), x true
  (test-trace? (lambda (env) (let ([t1 (lookup env 'x)])
                               (if t1
                                   (lit 0)
                                   (exit env '(lit 1))))))

  ;; (integer? (if x 0 1)), x true
  (test-trace? (lambda (env) (let ([t1 (let ([t2 (lookup env 'x)])
                                         (if t2
                                             (lit 0)
                                             (exit env '(lit 1))))])
                               (integer? t1))))

  ;; (integer? x)
  (test-trace? (lambda (env) (let ([t1 (lookup env 'x)])
                               (integer? t1))))

  ;; (f x) where (define f (x) (integer? x))
  (test-trace? (lambda (env) (let ([t1 (lookup env 'x)]
                                   [env (extend env (['x t1]))])
                               (let ([t2 (lookup env 'x)])
                                 (integer? t2)))))
  )

(define-metafunction trace
  basil-extend : r (x v) ... -> r
  [(basil-extend ((x v) ...) (x_0 v_0) ...)
   ((x_0 v_0) ... (x v) ...)])

(define rewrite-basil-extend
  (match-lambda
    [(list _ _ r (struct* lw ([e (list _ x v _)])) (and dot (struct* lw ([e '...]))) _)
     (list "" r "{" x "↦" v "," dot "}" "")]))

(define-metafunction trace
  basil-lookup : r x -> v
  [(basil-lookup ((x_0 v_0) ... (x v) (x_n v_n) ...) x) v
   ;; r may contain multiple bindings for x, so match only the
   ;; first instance of it, starting from the left
   (side-condition (not (set-member? (term (x_0 ...)) (term x))))])

(module+ test
  (test-equal (term (basil-lookup ((xs 1) (xs 2)) xs)) 1))

(define rewrite-basil-lookup
  (match-lambda
    [(list _ _ r x _)
     (list "" r "(" x ")" "")]))

(define-metafunction trace
  basil-function-lookup* : d x -> ((x ...) e)
  [(basil-function-lookup*
    ((x_0 _ _) ... (x_fun (x_arg ...) e) (x_n _ _) ...)
    x_fun)
   ((x_arg ...) e)])

(module+ test
  (test-equal (term (basil-function-lookup* ((add1 (x) (app + x (lit 1)))) add1))
              (term ((x) (app + x (lit 1))))))

(define-judgment-form trace
  #:contract (basil-function-lookup d x ((x ...) e))
      #:mode (basil-function-lookup I I O)

  [(basil-function-lookup d x (basil-function-lookup* d x))])

(define rewrite-basil-function-lookup
  (match-lambda
    [(list _ _ d x result _)
     (list "" d "(" x ") = " result "")]))
  

(define-judgment-form trace
  #:contract (fresh-var y)
      #:mode (fresh-var O)
  [------------------------
   (fresh-var (fresh-var*))])

(define-judgment-form trace
  #:contract (fresh-var/prefix y y)
      #:mode (fresh-var/prefix I O)
  [-----------------------------------
   (fresh-var/prefix y (fresh-var* y))])

(define rewrite-fresh-var
  (match-lambda
    [(list _ _ var _)
     (list "" var " fresh" "")]))
(define rewrite-fresh-var/prefix
  (match-lambda
    [(list _ _ _ var _)
     (list "" var " fresh" "")]))

(define-judgment-form trace
  #:contract (fresh-vars/prefix (any ...) y (y ...))
      #:mode (fresh-vars/prefix I       I O)
  [----------------------------------------------------------
   (fresh-vars/prefix (any ...) y (fresh-vars/prefix* (any ...) y))])

(define count 0)

;; not sure how to disable it just for this metafunction, so disable
;; all the caches!
(caching-enabled? #f)
(define-metafunction trace
  [(fresh-var*) (fresh-var* ,'t)]
  [(fresh-var* y) ,(let ([prefix (string-trim (~a (term y)) #px"\\d+")])
                    (set! count (+ 1 count))
                    (string->symbol (format "~a~a" prefix count)))])

;; x_n many fresh-vars with prefix x
(define-metafunction trace
  [(fresh-vars/prefix* (any ...) x)
   ,(map (lambda _ (term (fresh-var* x))) (term (any ...)))])

(define rewrite-fresh-vars/prefix
  (match-lambda
    [(list _ _ _ _ vars _)
     (list "" vars " fresh and distinct" "")]))

(module+ test
  (test-match trace y (term (fresh-var*)))
  (test-match trace y (term (fresh-var* b))))


;; XXX define a form define-trace-judgment that defines a judgment
;; named by #:id, with optional #:modeless? parameter (default #f,
;; i.e. moded). The defined judgment includes all the rules for
;; expressions plus any additional rules that are specified in the
;; define-trace-judgment clause. Example sketches:
;;
;; (define-trace-judgment
;;   #:id trace-e)
;;
;; (define-trace-judgment
;;   #:id trace-e/nondet
;;   #:modeless? #t
;;
;;   [----- "T-Cache"
;;     ...])
;;
;; Then, I can use the deterministic judgment and the nondeterministic
;; judgments. I think I have to go this route because
;; define-extended-judgment-form effectively just adds rules to an
;; existing judgment, and so the modes have to be the same; I wouldn't
;; be able to define a moded version with a modeless extension.
;;
;; All this is a little hacky since I have to write the deterministic
;; judgment with the cache already threaded through. Oh well.

(define rewrite-trace-e
  (match-lambda
    [(list _ _ C d r e v f _)
     `(""
       ,@(add-between (list C d r) ",")
       "⊢"
       ,e
       "⇓"
       ,v
       "⇝"
       ,f)]))

(define-judgment-form trace
                   ;; C,ϕ,ρ⊢e⇓v,f
  #:contract (trace-e C d r e v f)
      #:mode (trace-e I I I I O O)

  [------------------------ "T-Variable"
   (trace-e C d r x (basil-lookup r x) (lookup ρ 'x))]

  [------------------------ "T-Literal"
   (trace-e C d r (lit v) v (lit v))]

  [(trace-e C d r e_1 #t f_1) (trace-e C d r e_2 v_2 f_2)

   (fresh-var y)
   (where f (let ([y f_1])
              (if y
                  f_2
                  (exit ρ 'e_2))))
   ------------------------------------------- "T-IfTrue"
   (trace-e C d r (if e_1 e_2 e_3) v_2 f)]

  [(trace-e C d r e_1 #f f_1) (trace-e C d r e_3 v_3 f_3)

   (fresh-var y)
   (where f (let ([y f_3])
              (if y
                  (exit ρ 'e_2)
                  f_3)))
   ------------------------------------------- "T-IfFalse"
   (trace-e C d r (if e_1 e_2 e_3) v_3 f)]

  [(basil-function-lookup d x ((x_n ..._1) e))

   (trace-e C d r e_n v_n f_n) ...

   (trace-e C d (basil-extend r (x_n v_n) ...) e v f_e)

   (fresh-vars/prefix (x_n ...) ,'y (y_n ...))

   (where f (let ([y_n f_n] ...)
              (let ([ρ (extend ρ (['x_n y_n] ...))])
                f_e)))
   -------------------------------------- "T-AppUser"
   (trace-e C d r (app x e_n ..._1) v f)]

  [(trace-e C d r e v_n f_n) ...

   (fresh-vars/prefix (e ...) ,'y (y_n ...))

   (apply-prim p (v_n ...) v)

   (where f (let ([y_n f_n] ...)
              (p y_n ...)))
   -------------------------------------- "T-AppPrim"
   (trace-e C d r (app p e ...) v body)]

  )

(module+ test
  (judgment-holds (trace-e () () ((x 0)) x 0 f) f)
  (judgment-holds (trace-e () () ((x 0)) (lit #t) #t f) f)
  (judgment-holds (trace-e () () ((x #t)) x #t f) f)
  (judgment-holds (trace-e () () ((x #t)) (if x (lit 0) (lit 1)) 0 f) f)

  (judgment-holds (trace-e () ((f (x) (if x (lit 0) (lit 1)))) ((x #t)) (app f x) 0 f) f)

  (judgment-holds (trace-e () ((g (x y) (if (lit #t) x y))) ((w 0) (v 1)) (app g w v) 0 f) f)

  (test-judgment-holds (trace-e () () ((m 0)) (app cons m (lit 1)) (cons 0 1) f))
  (test-judgment-holds (trace-e () () () (app cons (lit 1) (lit 2)) (cons 1 2) f))
  (test-judgment-holds (trace-e () () () (app car (lit (cons 1 2))) 1 f))
  (test-judgment-holds (trace-e () () () (app cdr (lit (cons 1 2))) 2 f))
  (test-judgment-holds
   (trace-e
    ()
    ((append (xs ys) (if (app null? xs)
                         ys
                         (app cons (app car xs)
                              (app append (app cdr xs) ys)))))
    ()
    (app append (lit (cons 1 '())) (lit '()))
    v
    f))
  )

(define (call-with-trace-rewriters proc)
  (parameterize ([non-terminal-style '(italic . swiss)]
                 [literal-style 'modern])
    (with-atomic-rewriters
      (['r "ρ"]
       ['d "ϕ"]
       ['lambda "λ"]
       ['env (lambda () (text "ρ" 'modern))]
       ['cont (lambda () (text "κ" 'modern))]
       #;['y (lambda () (text "y" 'modern))])
      (with-compound-rewriters
        (['trace-e rewrite-trace-e]
         ['basil-lookup rewrite-basil-lookup]
         ['basil-extend rewrite-basil-extend]
         ['basil-function-lookup rewrite-basil-function-lookup]
         ['fresh-var rewrite-fresh-var]
         ['fresh-var/prefix rewrite-fresh-var/prefix]
         ['fresh-vars/prefix rewrite-fresh-vars/prefix]
         ['apply-prim rewrite-apply-prim])
        (proc)))))

(define-simple-macro (with-trace-rewriters e ...)
  (call-with-trace-rewriters (lambda () e ...)))

(module+ render

  (define destdir
    (match (current-command-line-arguments)
      [(vector) (current-directory)]
      [(vector path) path]))

  (parameterize ([current-directory destdir])
    (with-trace-rewriters
      (render-language trace-source "basil-language.pdf"
                       #:nts '(e v p x d r))
      (render-language trace-target "trace-language.pdf"
                       #:nts '(env y f t C))
      (render-judgment-form trace-e "trace-judgment.pdf")
      (render-term trace
                   (lambda (env)
                     (let ([t1 (lookup ρ 'm)]
                           [t2 (lit 1)])
                       (cons t1 t2)))
                   "trace-exprim.pdf"))))

(provide with-trace-rewriters trace trace-e)
