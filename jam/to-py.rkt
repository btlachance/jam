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
                (,f-exn as t
                 (do (app print ("Test failed: %s" binop % (t dot message)))
                     (if (t dot witness)
                         (app print ("Got: %s" binop % (app (t dot witness to_toplevel_string)))))))))]

     [(evaluator* name transition
                  load maybe-unload control-string)
      (define driver-class
        `(,(get-annotation t 'rpython-jit-prefix) dot JitDriver))
      (define driver-name (pythonify-name (format-symbol "~a-driver" name)))

      ;; XXX making a module-var+call out of thin air is a hack and
      ;; duplicates what's in pattern.rkt; this should be passed in on
      ;; an annotated ir or similar
      (define none (ir->py-exp `(call ,(module-var* 'core 'none))))

      (define done-exception (ir->py-exp (get-annotation t 'jam-done-exn)))
      `(do (,driver-name assign (app ,driver-class
                                     (reds binop = (list "t" "tmp"))
                                     (greens binop = (list "c" "prev_c"))
                                     (get_printable_location
                                      binop =
                                      (lambda (c prev_c) (app (c dot to_toplevel_string))))))
           (def ,(pythonify-name name) (t)
             (try
              (do
                (t assign (app ,(pythonify-name (ir->py-exp load)) t))
                (tmp assign ,none)
                (c assign ,none)
                (prev_c assign ,none)

                (app (t dot mark_static))
                (while #t
                  (app (,driver-name dot jit_merge_point)
                       (c binop = c)
                       (prev_c binop = prev_c)
                       (t binop = t)
                       (tmp binop = tmp))
                  (app ,(pythonify-name (ir->py-exp maybe-unload)) t)
                  (t assign (app ,(pythonify-name (ir->py-exp transition)) t))

                  (tmp assign (app ,(pythonify-name (ir->py-exp control-string)) t))
                  (if (tmp dot static)
                      (do (if (unop not (app (c dot is_none)))
                              (prev_c assign c))
                          (c assign tmp))
                      (c assign ,none))

                  (if (app (c dot can_enter))
                      (app (,driver-name dot can_enter_jit)
                           (c binop = c)
                           (prev_c binop = prev_c)
                           (t binop = t)
                           (tmp binop = tmp)))))
              (,done-exception as d (return (d dot v)))
              (,(ir->py-exp (module-var* 'core 'JamError))
               as e
               (do (app print ("Jam Error: %s" binop % (e dot s)))
                   (if t
                       (app print ("Current term: %s" binop % (app (t dot to_toplevel_string))))
                       (app print "No current term"))
                   (return ,none)))
              (Exception
               as e
               (do (app print ("Internal Error: %s" binop % e))
                   (app print ("Current term:\n%s" binop % (app (t dot to_toplevel_string))))
                   (return ,none)))
              (finally
               (do (if ,(ir->py-exp (module-var* 'core 'stdout))
                       (app (,(ir->py-exp (module-var* 'core 'stdout)) dot flush)))
                   (if ,(ir->py-exp (module-var* 'core 'stderr))
                       (app (,(ir->py-exp (module-var* 'core 'stderr)) dot flush))))))))]

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
                     '((#rx"->" "_arrow_")
                       (#rx"-"  "_")
                       (#rx"\\?$" "")
                       (#rx"/" "")
                       (#rx"\\*" "star"))))

  (match (sequence->list (generate-tokens (open-input-string result)))
    [(list `(NAME ,result . ,_) `(ENDMARKER . ,_))
     (string->symbol result)]
    [ts
     (error 'pythonify-name "expected a symbol that tokenizes as a python name\n\
  original symbol: ~a\n\
  after replacements: ~a\n\
  tokens: ~a" name result ts)]))

(define py-core-names
  (hash 'nil 'make_nil
        'none 'make_none
        'pair 'make_pair
        'symbol 'make_symbol
        'integer 'make_integer
        'real 'make_real
        'integer_of_real 'integer_of_real
        'real_of_integer 'real_of_integer
        'string 'make_string
        'boolean 'make_boolean
        'hd 'get_hd
        'tl 'get_tl
        '= 'atoms_equal
        'nil? 'is_nil
        'pair? 'is_pair
        'symbol? 'is_symbol
        'integer? 'is_integer
        'real? 'is_real
        'string? 'is_string
        'boolean? 'is_boolean
        'list? 'is_list
        'print-term 'print_term
        'all? 'all_terms
        'map 'map_terms
        'decompose-values 'decompose_values
        'error 'error
        'fail-test 'fail_test
        'pass-test 'pass_test
        'done 'done
        'from-json-string 'string_to_term
        'JamDone 'JamDone
        'JamError 'JamError
        'ExnTestSuccess 'ExnTestSuccess
        'ExnTestFailure 'ExnTestFailure
        'list_reverse 'list_reverse
        'integer_add0 'integer_add0
        'integer_subtract0 'integer_subtract0
        'integer_multiply0 'integer_multiply0
        'real_add 'real_add
        'real_subtract 'real_subtract
        'real_multiply 'real_multiply
        'is_environment 'is_environment
        'environment_lookup 'environment_lookup
        'environment_is_bound 'environment_is_bound
        'environment_extend1 'environment_extend1
        'environment_extend 'environment_extend
        'environment_extend_cells 'environment_extend_cells
        'environment_set_cells 'environment_set_cells
        'environment_empty 'environment_empty
        'clock_milliseconds 'clock_milliseconds
        'mutable_sequence_of 'mutable_sequence_of
        'immutable_sequence_of 'immutable_sequence_of
        'is_mutable_sequence 'is_mutable_sequence
        'is_immutable_sequence 'is_immutable_sequence
        'sequence_element_at 'sequence_element_at
        'sequence_set 'sequence_set
        'sequence_length 'sequence_length
        'string_append 'string_append
        'string_length 'string_length
        'is_file 'is_file
        'file_write 'file_write
        'get_stdout 'get_stdout
        'get_stderr 'get_stderr
        'stdout 'stdout
        'stderr 'stderr
        'systemstar_json_term 'systemstar_json_term
        ))
;; A cheap way to test that this hash is partly consistent with
;; core.py is to generate a python module that tries to import all of
;; the values in py-core-names from the core module. The easiest way
;; to load the core module, I think, would be to extend PYTHONPATH
;; with the directory core.py is in. If that gets unwieldly then
;; something in Python's site module might be helpful
(define (core-name->py name) (hash-ref py-core-names name))

(define (ir->py-exp ir)  
  (match ir
    [(lexical-var* t)
     (match (get-annotation ir 'py-name)
       [(? symbol? rename) (pythonify-name rename)]
       [_ (pythonify-name t)])]

    [(module-var* (== core-handle) name) `(core dot ,(core-name->py name))]

    [(module-var* modname name)
     `(,(pythonify-name modname)
       dot
       ,(match (get-annotation ir 'py-name)
          [(? symbol? rename) (pythonify-name rename)]
          [_ (pythonify-name name)]))]

    [(? string? s) s]
    [(? flonum? f) f]
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
