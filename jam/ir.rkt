#lang racket
(require
 racket/generic
 syntax/parse/define
 (for-syntax
  racket/syntax
  racket/struct-info
  "ir-util.rkt"))

(provide get-annotation annotate)

;; (define-ir name (fields ...)) creates an immutable, transparent
;; struct that works with gen:annotatable and get-annotation. The
;; struct also implements gen:equal+hash such that two ir made from
;; the same struct are equal? if their fields are equal? (annotations
;; are ignored).
;;
;; Creates name*, a struct-info that lets you omit the annotation
;; field in match patterns. Also creates a smart constructor for
;; making instances of name with an empty set of annotations; using
;; name* as an expression expands to the smart constructor. Provides
;; (struct-out name) and name*.
;;
;; Notes:
;;
;; - It's not useful to use name* with struct-copy because it tries to
;;   use accessors of the form name*-field. (Even if it did use the
;;   right accessors, the docs aren't clear what constructor
;;   struct-copy would use---either name* itself or the name inside
;;   name*'s struct-info should work, though, since the former expands
;;   to the latter.)
;;
;; - The struct is transparent mostly so that no new code is needed
;;   for printing. We have to implement our own gen:equal+hash though
;;   since the base ir struct is opaque (unless there's some other way
;;   to work with equal?).
(define-simple-macro (define-ir name:id (fields:id ...))
  #:with name? (format-id #'name "~a?" #'name)
  #:with name* (format-id #'name "~a*" #'name)
  #:with ctor (generate-temporary #'name*)
  #:with (accessors ...)
  (for/list ([f (attribute fields)])
    (format-id #'name "~a-~a" #'name f))

  (begin
    (struct name ir (fields ...)
      #:transparent
      #:methods gen:annotatable
      [(define (annotate target key value)
         (define new-ann (set-ann target key value))
         ;; Bummer: can't use name in a struct-copy here because it's
         ;; not yet bound to the structure type
         (name new-ann (accessors target) ...))]
      #:methods gen:equal+hash
      [(define (equal-proc v w _)
         (and (equal? (accessors v) (accessors w))
              ...))
       ;; hash code recipe from Effective Java, 2E
       (define (hash-proc v _)
         (for/fold ([result 17])
                   ([field-v (in-list (list (accessors v) ...))])
           (+ (* 31 result)
              (equal-hash-code field-v))))
       (define (hash2-proc v _)
         (for/fold ([result 17])
                   ([field-v (in-list (list (accessors v) ...))])
           (+ (* 31 result)
              (equal-secondary-hash-code field-v))))])

    (define ctor
      (procedure-rename
       (lambda (fields ... [ann empty-ann])
         (name ann fields ...))
       'name*))

    (define-syntax name*
      (ir-struct-info #'ctor #'name?
                      (list #'accessors ...)))

    (provide (struct-out name) name*)))

(struct ir (annotations))

(define empty-ann (hash))
(define (set-ann ir key value) (hash-set (ir-annotations ir) key value))
(define (get-ann ir key fail-v) (hash-ref (ir-annotations ir) key fail-v))
(define-generics annotatable
  [annotate annotatable key value])

(define (get-annotation ir key [failure-result #f])
  (get-ann ir key failure-result))

(define-ir lexical-var (symbol))
(define-ir module-var (modname symbol))
(define-ir test (ir)) ;; ir must evaluate to a proc
(define-ir fail-test (message witness))
(define-ir pass-test ())
(define-ir lett (var rhs body))
(define-ir proc (formals body))
(define-ir define: (name rhs))
(define-ir noop ())
(define-ir done (result))
(define-ir evaluator (name transition load unload control-string))
(define-ir py-from (modname imports))
(define-ir print-term (ir))
(define-ir none ())

(module+ test
  (require (submod "..") rackunit)

  (check-true
   (match #f
     [(lexical-var _ _) #f]
     [_ #t]))

  (check-true
   (match (module-var (hash) 'runtime '=)
    [(module-var* 'runtime '=) #t]
    [(module-var* '= 'runtime) #f]
    [(lexical-var* 'x) #f]))

  (check-equal? (lexical-var* 'x) (lexical-var* 'x))
  (check-equal? (equal-hash-code (lexical-var* 'x))
                (equal-hash-code (lexical-var* 'x)))

  (define ir0 (annotate (lexical-var* '=) 'py-name 'atoms_equal))
  (define ir1 (annotate ir0 'py-name 'is_equal))
  (check-equal? ir0 ir1)
  (check-equal? (get-annotation ir0 'py-name) 'atoms_equal)
  (check-equal? (get-annotation ir1 'py-name) 'is_equal))

;; XXX the compiler doesn't generate ir as general as this definition
;; says, so we don't need runtime support this general; e.g. = is only
;; ever given an atom as the first arg, = doesn't need to be a general
;; equality predicate.

;; an ir is one of
;; - var
;; - '(nil)
;; - (none)
;; - `(pair ,ir ,ir)
;; - `(symbol ,symbol)
;; - `(integer ,integer)
;; - `(boolean ,boolean)

;; - `(hd ,ir)
;; - `(tl ,ir)

;; - string
;; - integer
;; - boolean

;; - `(= ,ir ,ir)
;; - `(if ,ir ,ir ,ir)
;; - `(not ,ir)
;; - `(and ,@(listof ir))
;; - `(or ,@(listof ir))
;; - `(nil? ,ir)
;; - `(pair? ,ir)
;; - `(symbol? ,ir)
;; - `(integer? ,ir)
;; - `(string? ,ir)
;; - `(boolean? ,ir)
;; - `(list? ,ir)
;; - `(all? ,ir ,ir)
;; - `(produced-by? (lang ,symbol) (nt ,symbol) ,ir)
;; - `(terminal? (lang ,symbol) ,ir)
;; - (print-term ir)

;; - `(list ,@(listof ir))
;; - `(map ,ir ,ir)

;; - `(mf-apply (lang ,symbol) ,symbol ,ir)

;; - (proc (listof symbol) ir)
;; - `(decompose-values ,ir ,ir)
;; - '(error)
;; - (fail-test string ir)
;; - (pass-test)
;; - (done ir)
;; - `(call ,var ,@(listof ir))

;; a var is one of
;; - (lexical-var symbol)
;; - (module-var symbol symbol)
;;   * where the first symbol is the module's name and the second is
;;     the variable's

;; a module is a
;; - `(module ,symbol
;;      (require ,@(listof require))
;;      (provide ,@(listof symbol))
;;      ,@(listof toplevel))

;; like python: cyclic references between modules are OK as long as
;; the bindings of those modules are not forced when the module is
;; loaded (e.g. they're inside a proc that doesn't get called on load)

;; a require is one of
;; - symbol
;; - (py-from (nelistof symbol) (nelistof symbol))

;; a toplevel is one of
;; - (define: symbol ir-or-prim)
;; - (test ir)
;; - ir
;; - (evaluator symbol ir ir ir ir)
;;   * where the symbol is the evaluator's name; all the ir must be variables
;;     bound to procedures:
;;       - the first is a unary proc, a transition function
;;       - the second is a unary proc, a load function
;;       - the third is a unary proc, an unload function
;;       - the fourth is a binary proc (term, control string) that
;;         returns a new control string if the term has one or the
;;         given control string otherwise

;; Note: toplevel's don't allow body-A because there's nowhere to put
;; the bindings

;; a ir-or-prim is one of
;; - `(prim-class ,symbol)
;; - `(prim-procedure ,symbol)
;; - ir
;; where for prim-class and prim-procedure, the symbol doubles as the
;; Python-level name

;; a body-A is one of
;; - (lett symbol A body-A)
;; - (if ir body-A body-A)
;; - (noop)
;; - A

;; INV: the only free variables in a proc are the names of other
;; proc's.

;;;;
;; a core+grammar+mf-ir (cgmir) is one of
;; - var
;; - string
;; - integer
;; - boolean
;; - `(if ,cgmir ,cgmir ,cgmir)
;; - `(not ,cgmir)
;; - `(and ,@(listof cgmir))
;; - `(or ,@(listof cgmir))
;; - `(produced-by? (lang ,symbol) (nt ,symbol) ,cgmir)
;; - `(terminal? (lang ,symbol) ,cgmir)
;; - `(mf-apply (lang ,symbol) ,symbol ,cgmir)
;; - (proc (listof symbol) body-cgmir)
;; - `(call ,var ,@(listof cgmir))

;; a core+mf-ir (cmir) is one of
;; - var
;; - string
;; - integer
;; - boolean
;; - `(if ,cmir ,cmir ,cmir)
;; - `(not ,cmir)
;; - `(and ,@(listof cmir))
;; - `(or ,@(listof cmir))
;; - `(mf-apply (lang ,symbol) ,symbol ,cmir)
;; - (proc (listof symbol) body-cmir)
;; - `(call ,var ,@(listof cmir))

;; a core-ir (cir) is one of
;; - var
;; - string
;; - integer
;; - boolean
;; - `(if ,cir ,cir ,cir)
;; - `(not ,cir)
;; - `(and ,@(listof cir))
;; - `(or ,@(listof cir))
;; - (proc (listof symbol) body-cir)
;; - `(call ,var ,@(listof cir))

;; a proc-free core-ir (pfcir) is one of
;; - var
;; - string
;; - integer
;; - boolean
;; - `(if ,pfcir ,pfcir ,pfcir)
;; - `(not ,pfcir)
;; - `(and ,@(listof pfcir))
;; - `(or ,@(listof pfcir))
;; - `(call ,var ,@(listof pfcir))
