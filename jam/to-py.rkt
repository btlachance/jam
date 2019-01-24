#lang at-exp racket
(require "lang-rep.rkt" "python-ast.rkt" "ir.rkt"
         "pattern.rkt"
         python-tokenizer "util.rkt"
         racket/syntax)
(provide format-modules write-modules)

(define (toplevel->py t)
  (match t

    [(define:* name (proc* formals body))
      `(def ,(pythonify-name name) ,(map pythonify-name formals)
         ,(body-ir->py-stmt body))]

    [(define:* name ir)
     (let ([name (or (get-annotation t 'py-name) name)])
       `(,(pythonify-name name) assign ,(ir->py-exp ir)))]

     [(test* ir)
      (define-values (s-exn f-exn)
        (values (ir->py-exp (get-annotation t 'success-exn))
                (ir->py-exp (get-annotation t 'failure-exn))))

      `(if (__name__ binop == "__test__")
           (try (app ,(ir->py-exp ir))
                (,s-exn (pass))
                (,f-exn as t (app print ("Test failed: %s" binop % (t dot message))))))]

     [(evaluator* name transition
                  load maybe-unload control-string)
      (define driver-class
        `(,(get-annotation t 'rpython-jit-prefix) dot JitDriver))
      (define driver-name (pythonify-name (format-symbol "~a-driver" name)))
      (define done-exception (ir->py-exp (get-annotation t 'jam-done-exn)))
      `(do (,driver-name assign (app ,driver-class
                                     (reds binop = (list "t"))
                                     (greens binop = (list "c"))
                                     (get_printable_location
                                      binop =
                                      (lambda (c) (app (c dot to_toplevel_string))))))
           (def ,name (t)
             (t assign (app ,(pythonify-name (ir->py-exp load)) t))
             (c assign t)
             (app (t dot mark_static))
             (try
              (while #t
                (app (,driver-name dot jit_merge_point)
                     (c binop = c)
                     (t binop = t))
                (app ,(pythonify-name (ir->py-exp maybe-unload)) t)
                (t assign (app ,(pythonify-name (ir->py-exp transition)) t))
                (c assign (app ,(pythonify-name (ir->py-exp control-string)) t c))
                (if (app (c dot can_enter))
                    (app (,driver-name dot can_enter_jit)
                         (c binop = c)
                         (t binop = t))))
              (,done-exception as d (return (d dot v))))))]

     [ir (ir->py-stmt ir)]))

(define (format-modules mods)  
  (define (require->py r)
    (match r
      [(? symbol? s) `(import ,(pythonify-name s))]

      [(py-from* mod imports)

       (define (modname->name m)
         (match m
           [(list s) s]
           [(cons a (cons b m*))
            (define m*-name (modname->name (cons b m*)))
            `(,a dot ,@(if (symbol? m*-name)
                           (list m*-name)
                           m*-name))]))

       `(from ,(modname->name mod) import ,@imports)]))

  (define (contains-test? m)
    (match m
      [`(module ,_
          ,_
          ,_
          ,@tops)
       (for/or ([top tops])
         (match top
           [(struct test _) #t]
           [_ #f]))]))

  (define (format-mod m)
    (match m
      [`(module ,_
          (require ,@requires)
          ,_ ;; provides don't have corresponding python code
          ,@tops)

       (define test-runner
         (and (contains-test? m)
              `(if (__name__ binop == "__main__")
                   (do (import os)
                       (if ("JAM_TEST" binop in (os dot environ))
                           (do (import runpy)
                               (app (runpy dot run_path) __file__ None "__test__")))))))

       (with-output-to-string
         (lambda ()
           (pp-python-stmt
            `(do ,@(map require->py requires)
                 ,@(map toplevel->py tops)
                 ,@(if test-runner
                       (list test-runner)
                       '())))))]))

  (define (module-name m)
    (match m
      [`(module ,name . ,_) name]))
  
  (for/hash ([m mods])
    (values (format "~a.py" (pythonify-name (module-name m))) (format-mod m))))

(define (write-modules mods [dest-dir (current-directory)])
  (unless (directory-exists? dest-dir)
    (make-directory dest-dir))
  (define files-to-write (format-modules mods))
  (define files-to-copy
    (hash "pycket_json_adapter.py" (python-file "pycket_json_adapter.py")
          "core.py" (python-file "core.py")
          "target.py" (python-file "target.py")))

  (parameterize ([current-directory dest-dir])
    (for ([(path contents) (in-hash files-to-write)])
      (with-output-to-file path (lambda () (display contents))))
    (for ([(dest src) (in-hash files-to-copy)])
      (copy-file src dest))
    (copy-directory/files (python-directory "pycket") "pycket")))

(define (pythonify-name name)
  (define result
    (regexp-replaces (symbol->string name)
                     '((#rx"-"  "_")
                       (#rx"\\?$" ""))))

  (match (sequence->list (generate-tokens (open-input-string result)))
    [(list `(NAME ,result . ,_) `(ENDMARKER . ,_))
     (string->symbol result)]
    [ts
     (error 'pythonify-name "expected a symbol that tokenizes as a python name\n\
  original symbol: ~a\n\
  after replacements: ~a\n\
  tokens: ~a" name result ts)]))

(define (ir->py-exp ir)  
  (match ir
    [(lexical-var* t)
     (match (get-annotation ir 'py-name)
       [(? symbol? rename) (pythonify-name rename)]
       [_ (pythonify-name t)])]

    [(module-var* modname name)
     `(,(pythonify-name modname)
       dot
       ,(match (get-annotation ir 'py-name)
          [(? symbol? rename) (pythonify-name rename)]
          [_ (pythonify-name name)]))]

    [(? string? s) s]
    [(? exact-integer? n) n] ;; XXX What if n is a bignum? Error?
    [(? boolean? b) b]

    [`(if ,e1 ,e2 ,e3)
     `(ifx ,(ir->py-exp e1)
           ,(ir->py-exp e2)
           ,(ir->py-exp e3))]

    [`(not ,arg) `(unop not ,(ir->py-exp arg))]

    [`(,(and op (or 'and 'or)) ,@args)
     (match args
       ['() (match op
              ['and #t]
              ['or #f])]
       [(list arg) (ir->py-exp arg)]
       [(list arg args ...)
        `(,(ir->py-exp arg) binop ,op ,@(map ir->py-exp args))])]

    [`(call ,op ,@args)
     `(app ,(ir->py-exp op) ,@(map ir->py-exp args))]))

(define (body-ir->py-stmt ir)
  (match ir
    [(lett* bv (proc* args procbody) body)
     `(do (def ,bv ,args
            ,(body-ir->py-stmt procbody))
          ,(body-ir->py-stmt body))]

    [(lett* bv rhs body)
     `(do (,(pythonify-name bv) assign ,(ir->py-exp rhs))
          ,(body-ir->py-stmt body))]

    [`(if ,e ,then ,else)
     `(if ,(ir->py-exp e)
          ,(body-ir->py-stmt then)
          ,(body-ir->py-stmt else))]

    [(noop*) '(pass)]

    [_ (ir->py-stmt ir)]))

(define (ir->py-stmt ir)
  (define (return py) `(return ,py))
  (match ir
    [`(if ,e1 ,e2 ,e3)
     `(if ,(ir->py-exp e1)
          ,(ir->py-stmt e2)
          ,(ir->py-stmt e3))]

    [_
     (return (ir->py-exp ir))]))
