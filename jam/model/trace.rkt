#lang racket
(require redex syntax/parse/define)

(define-language trace-source
  ;; object language
  (     x ::= variable-not-otherwise-mentioned)
  (     v ::= #t #f integer '() (cons v v))
  (     p ::= boolean? integer? null? cons? zero? positive? negative?
          cons car cdr + * -)
  (     e ::= x (app x e ...) (app p e ...) (if e e e) (lit v))

  (     f ::= ((x (x ...) e) ...))
  (     r ::= ((x v) ...)))

(define-extended-language trace-target trace-source
  ;; trace language
  (     m ::= a w lam (extend a (['x a] ...)))
  (     w ::= v (quote e))
  (     q ::= p lookup lit exit guard)
  ( a b y ::= variable-not-otherwise-mentioned)
  (  body ::= (let ([a m]) body) (q m ...) (m m ...))
  (   lam ::= (lambda (a) body body ...) (lambda () body body ...))

  (     t ::= (lambda (a b) body))
  (     C ::= ((a t) ...)))

(define-union-language trace trace-source trace-target)

(module+ test
  (define-simple-macro (test-body? e) (test-match trace body (term e)))

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
  (test-trace? (lambda (env k) (lookup env (quote x) k)))

  ;; (if x 0 1)
  (test-trace? (lambda (env k) (let ([k1 (lambda (v1)
                                           (guard v1 #t (lambda () (exit (quote (lit 1)) env k)))
                                           (lit 0 env k))])
                                 (lookup env (quote x) k1))))

  ;; (add1 (if x 0 1))
  (test-trace? (lambda (env k) (let ([k2 (lambda (v2) (add1 v2 k))])
                                 (let ([k1 (lambda (v1)
                                             (guard v1 #t (lambda () (exit (quote (lit 1)) env k2)))
                                             (lit 0 env k2))])
                                   (lookup env (quote x) k1)))))

  ;; (add1 x)
  (test-trace? (lambda (env k)
                 (let ([k1 (lambda (v1) (add1 v1 k))])
                   (lookup env (quote x) k1))))

  ;; (f x) where (define f (x) (add1 x))
  (test-trace? (lambda (env k)
                 (let ([k1 (lambda (v1)
                             (let ([env* (extend env (['x v1]))])
                               (let ([k2 (lambda (v2) (add1 v2 k))])
                                 (lookup env* (quote x) k2))))])
                   (lookup env (quote x) k1))))
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
  [(basil-lookup ((x_0 v_0) ... (x v) (x_n v_n) ...) x) v])

(define rewrite-basil-lookup
  (match-lambda
    [(list _ _ r x _)
     (list "" r "(" x ")" "")]))

(define-metafunction trace
  basil-function-lookup* : f x -> ((x ...) e)
  [(basil-function-lookup*
    ((x_0 _ _) ... (x_fun (x_arg ...) e) (x_n _ _) ...)
    x_fun)
   ((x_arg ...) e)])

(module+ test
  (test-equal (term (basil-function-lookup* ((add1 (x) (app + x (lit 1)))) add1))
              (term ((x) (app + x (lit 1))))))

(define-judgment-form trace
  #:contract (basil-function-lookup f x ((x ...) e))
      #:mode (basil-function-lookup I I O)

  [(basil-function-lookup f x (basil-function-lookup* f x))])

(define rewrite-basil-function-lookup
  (match-lambda
    [(list _ _ f x result _)
     (list "" f "(" x ") = " result "")]))
  

(define count 0)

 ;; not sure how to disable it just for this metafunction, so disable
 ;; all the caches!

(define-judgment-form trace
  #:contract (fresh-var a)
      #:mode (fresh-var O)
  [------------------------
   (fresh-var (fresh-var*))])

(define-judgment-form trace
  #:contract (fresh-var/prefix a b)
      #:mode (fresh-var/prefix I O)
  [-----------------------------------
   (fresh-var/prefix a (fresh-var* a))])

(define rewrite-fresh-var
  (match-lambda
    [(list _ _ var _)
     (list "" var " fresh" "")]))
(define rewrite-fresh-var/prefix
  (match-lambda
    [(list _ _ _ var _)
     (list "" var " fresh" "")]))

(define-judgment-form trace
  #:contract (fresh-vars/prefix (a ...) a (b ...))
      #:mode (fresh-vars/prefix I       I O)
  [----------------------------------------------------------
   (fresh-vars/prefix (a ...) b (fresh-vars/prefix* (a ...) b))])

(caching-enabled? #f)
(define-metafunction trace
  [(fresh-var*) (fresh-var* ,'t)]
  [(fresh-var* a) ,(let ([prefix (string-trim (~a (term a)) #px"\\d+")])
                    (set! count (+ 1 count))
                    (string->symbol (format "~a~a" prefix count)))])

;; x_n many fresh-vars with prefix x
(define-metafunction trace
  [(fresh-vars/prefix* (x_n ...) x)
   ,(map (lambda _ (term (fresh-var* x))) (term (x_n ...)))])

(define rewrite-fresh-vars/prefix
  (match-lambda
    [(list _ _ _ _ vars _)
     (list "" vars " fresh and distinct" "")]))

(define-metafunction trace
  [(seq-bodies-then () b () body_e) body_e]

  [(seq-bodies-then (body body_n ...) b (y y_n ...) body_e)
   (let ([b (lambda (y) (seq-bodies-then (body_n ...) b (y_n ...) body_e))])
     body)])

(module+ test
  (test-match trace a (term (fresh-var*)))
  (test-match trace a (term (fresh-var* b))))


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
    [(list _ _ C a b f r e v body _)
     `(""
       ,@(add-between (list C a b f r) ",")
       "⊢"
       ,e
       "⇓"
       ,v
       ","
       ,body)]))

(define-judgment-form trace
                   ;; C,a,b,ϕ,ρ⊢e⇓v,body
  #:contract (trace-e C a b f r e v body)
      #:mode (trace-e I I I I I I O O)

  [------------------------ "T-Variable"
   (trace-e C a b f r x (basil-lookup r x) (lookup a (quote x) b))]

  [------------------------ "T-Literal"
   (trace-e C a b f r (lit v) v (lit v b))]

  [(fresh-var/prefix b b_1) (trace-e C a b_1 f r e_1 #t  body_1) (trace-e C a b   f r e_2 v_2 body_2)

   (fresh-var y)
   (where body (let ([b_1 (lambda (y)
                            (guard y #t (lambda () (exit (quote e_3) a b)))
                            body_2)])
                 body_1))
   ------------------------------------------- "T-IfTrue"
   (trace-e C a b f r (if e_1 e_2 e_3) v_2 body)]

  [(fresh-var/prefix b b_1) (trace-e C a b_1 f r e_1 #f  body_1) (trace-e C a b   f r e_3 v_3 body_3)

   (fresh-var y)
   (where body (let ([b_1 (lambda (y)
                            (guard y #f (lambda () (exit (quote e_2) a b)))
                            body_3)])
                 body_1))
   ------------------------------------------- "T-IfFalse"
   (trace-e C a b f r (if e_1 e_2 e_3) v_3 body)]

  [(basil-function-lookup f x ((x_n ..._1) e))

   (fresh-var/prefix b b_0) (trace-e C a b_0 f r e_n v_n body_n) ...

   (fresh-var/prefix a a_e) (trace-e C a_e b f (basil-extend r (x_n v_n) ...) e v body_e)

   (fresh-vars/prefix (x_n ...) ,'y (y_n ...))

   ;; XXX if every call is to the nearest enclosing continuation,
   ;; might only need one b_n here?
   (where body (seq-bodies-then (body_n ...) b_0 (y_n ...)
                                (let ([a_e (extend a (['x_n y_n] ...))])
                                  body_e)))
   -------------------------------------- "T-AppUser"
   (trace-e C a b f r (app x e_n ..._1) v body)]

  )

(module+ test
  (judgment-holds (trace-e () ρ k () ((x 0)) x 0 body) body)
  (judgment-holds (trace-e () ρ k () ((x 0)) (lit #t) #t body) body)
  (judgment-holds (trace-e () ρ k () ((x #t)) x #t body) body)
  (judgment-holds (trace-e () ρ k () ((x #t)) (if x (lit 0) (lit 1)) 0 body) body)

  (judgment-holds (trace-e () ρ k ((f (x) (if x (lit 0) (lit 1)))) ((x #t)) (app f x) 0 body) body)

  (judgment-holds (trace-e () ρ k ((g (x y) (if (lit #t) x y))) ((w 0) (v 1)) (app g w v) 0 body) body))

(define (call-with-trace-rewriters proc)
  (parameterize ([non-terminal-style '(italic . swiss)]
                 [literal-style 'modern])
    (with-atomic-rewriters
      (['r "ρ"]
       ['f "ϕ"]
       ['lambda "λ"])
      (with-compound-rewriters
        (['trace-e rewrite-trace-e]
         ['basil-lookup rewrite-basil-lookup]
         ['basil-extend rewrite-basil-extend]
         ['basil-function-lookup rewrite-basil-function-lookup]
         ['fresh-var rewrite-fresh-var]
         ['fresh-var/prefix rewrite-fresh-var/prefix]
         ['fresh-vars/prefix rewrite-fresh-vars/prefix])
        (proc)))))

(define-simple-macro (with-trace-rewriters e ...)
  (call-with-trace-rewriters (lambda () e ...)))

(module+ render
  (with-trace-rewriters
    (render-language trace-source "basil-language.pdf"
                     #:nts '(e v p x f r))
    (render-language trace-target "trace-language.pdf"
                     #:nts '(m w q a b y body lam t C))
    (render-metafunctions seq-bodies-then
                          #:file "trace-metafunctions.pdf")
    (render-judgment-form trace-e "trace-judgment.pdf")))

(provide with-trace-rewriters trace trace-e)
