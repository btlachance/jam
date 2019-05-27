#lang racket
(provide module->pycketlite path->pycketlite)
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
    #:datum-literals (call-with-values print-values)
    [(#%plain-app call-with-values (lambda () e) print-values)
     (expr->pycketlite #'e)]

    [(#%plain-app e0 e ...)
     (expr->pycketlite this-syntax)]

    [(define-values (x ...) e)
     `(define-values ,(map syntax-e (attribute x)) ,(expr->pycketlite #'e))]))

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

    [((~and form (~or let-values letrec-values)) ([(x ...) e] ...) e_body)
     (let ([x* (syntax->datum #'((x ...) ...))]
           [e* (map expr->pycketlite (attribute e))])
       `(,(syntax-e #'form) ,(map list x* e*)
                            ,(expr->pycketlite #'e_body)))]

    [(quote {~or :exact-integer :boolean :string})
     (syntax->datum this-syntax)]

    [(#%plain-app e e* ...)
     (cons (expr->pycketlite #'e) (map expr->pycketlite (attribute e*)))]

    [x:id (syntax-e #'x)]))

(define (path->pycketlite p [ns? #t])
  ;; XXX I don't fully understand why, but when calling this
  ;; function from phase 1 the lexical context that gets added by
  ;; expand produces identifiers that don't match racket's
  ;; bindings---when I was still setting the current-namespace to a
  ;; new base-namespace, that is. But when calling this function
  ;; from phase 1 and I just use the current-namespace and don't
  ;; install a new one then the identifiers match fine. In phase 0
  ;; uses though I still need to set the current-namespace.
  (parameterize ([read-accept-reader #t]
                 [read-accept-lang #t]
                 [current-namespace (if ns?
                                        (make-base-namespace)
                                        (current-namespace))]
                 [current-input-port (open-input-file p)])
    (begin0 (module->pycketlite (expand (read-syntax)))
      (close-input-port (current-input-port)))))