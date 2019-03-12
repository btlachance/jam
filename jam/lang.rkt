#lang racket
(require
 json
 make
 "lang-rep.rkt"
 "to-py.rkt"
 "term-to-json.rkt"
 (for-syntax
  syntax/parse
  syntax/modresolve
  syntax/location
  racket/syntax))

(provide
 define-language
 define-metafunction
 define-transition
 define-evaluator
 current-test-language
 test-equal
 test-not-equal
 jam-test
 jam-run)

(define current-test-language (make-parameter #f))

(begin-for-syntax
  (require "pattern.rkt" racket/match)
  (define-syntax-class nonterminal
    (pattern (~and :id (~not (~datum ...)) (~not (~datum _)))
             #:fail-when (pattern-keyword? (syntax-e this-syntax)) "pattern keyword can't be a nonterminal"
             #:fail-when (suffixed-underscore? this-syntax) "nonterminal in a define-language can't have underscore suffixes"))

  (define-splicing-syntax-class nonterminals
    #:attributes (nts)
    (pattern {~seq nt:nonterminal ...}
             #:fail-when (check-duplicate-identifier (attribute nt)) "duplicate nonterminal"
             #:attr nts (attribute nt)))

  (define-syntax-class production
    #:attributes (nts [rhss 1] data)
    (pattern (:nonterminals (~datum ::=) rhss:expr ...+)
             #:attr data (list (map syntax-e (attribute nts))
                               (map syntax->datum (attribute rhss)))))

  (define-syntax-class include
    #:attributes (nts data)
    (pattern [:nonterminals app]
             #:attr data (list (map syntax-e (attribute nts))
                               (syntax->datum #'app)))))

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id
        {~optional {~seq #:data (i:include ...)}
                   #:defaults ([(i.data 1) '()] [(i.nts 1) '()])}
        p:production ...)
     #:fail-when
     (let ([grammar-nts (apply append (attribute p.nts))]
           [data-nts (apply append (attribute i.nts))])
       (check-duplicate-identifier (append grammar-nts data-nts)))
     "duplicate nonterminal"
     (with-syntax ([((nts rhs) ...) (attribute p.data)]
                   [(includes ...) (attribute i.data)])
       #'(define name (lang-info 'name '(nts ...) '(rhs ...)
                                 '(includes ...))))]))

(begin-for-syntax
  (define-syntax-class where
    #:attributes (where)
    #:datum-literals (where)
    (pattern (where pattern template)
             #:attr where #'(pattern template)))

  (define-syntax-class plain-case
    #:attributes (arg rhs [wheres 1])
    (pattern (arg
              rhs
              {~seq :where ...})
             #:attr [wheres 1] (attribute where)))

  (define-syntax-class transition-case
    #:attributes (arg rhs [wheres 1])
    #:datum-literals (-->)
    (pattern [--> arg
                  rhs
                  {~seq :where ...}]
             #:attr [wheres 1] (attribute where)))

  (define-syntax-class metafunction-case
    #:attributes (name arg rhs [wheres 1])
    (pattern [(name:id . arg)
              rhs
              {~seq :where ...}]
             #:attr [wheres 1] (attribute where)))

  (define (any-different? xs)
    (match xs
      [`(,y0 ,y1 . ,ys)
       (if (not (free-identifier=? y0 y1))
           y1
           (any-different? (cons y1 ys)))]
      [_ #f]))

  (define-splicing-syntax-class metafunction-body
    #:attributes (mf-name args rhss wheress)
    (pattern {~seq c:metafunction-case ...+}
             #:fail-when (any-different? (attribute c.name))
             "the same name must be used in every case of a metafunction's body"
             #:attr mf-name (car (attribute c.name))
             #:attr args (attribute c.arg)
             #:attr rhss (attribute c.rhs)
             #:attr wheress (attribute c.wheres))))

(define-syntax (define-metafunction stx)
  (syntax-parse stx
    [(_ lang:id :metafunction-body)
     (syntax-local-lift-module-end-declaration
      (with-syntax ([(args ...) (attribute args)]
                    [(rhss ...) (attribute rhss)]
                    [(wheress ...) (attribute wheress)])
        #'(lang-register-metafunction!
           lang 'mf-name
           '(args ...) '(rhss ...)
           '(wheress ...))))
     #'(add-metafunction-name! lang 'mf-name)]))

(define-syntax (define-transition stx)
  (syntax-parse stx
    [(_ lang:id t-name:id :transition-case ...+)
     (with-syntax ([(args ...) (attribute arg)]
                   [(rhss ...) (attribute rhs)]
                   [(wheress ...) (attribute wheres)])
     #'(lang-add-transition!
        lang 't-name
        '(args ...) '(rhss ...)
        '(wheress ...)))]))

(define-syntax (define-evaluator stx)
  (syntax-parse stx
    [(_ lang:id e-name:id
        ;; XXX #:load and #:control-string should be optional,
        ;; defaulting to the identity transition and to a way to tell
        ;; the evaluator not to try and match a control string
        {~alt {~once {~seq #:load load:transition-case} #:name "#:load keyword"}
              {~once {~seq #:unload unload:transition-case} #:name "#:unload keyword"}
              {~once {~seq #:transition t-name:id} #:name "#:transition keyword"}
              {~once {~seq #:control-string cs:plain-case} #:name "#:control-string keyword"}}
        ...)
     (with-syntax ([load (list (attribute load.arg)
                               (attribute load.rhs)
                               (attribute load.wheres))]
                   [unload (list (attribute unload.arg)
                                 (attribute unload.rhs)
                                 (attribute load.wheres))]
                   [cs (list (attribute cs.arg)
                             (attribute cs.rhs)
                             (attribute cs.wheres))])
     #'(lang-add-evaluator!
        lang 'e-name 't-name
        'load 'unload 'cs))]))

(define-syntax (test-equal stx)
  (syntax-parse stx
    [(_ template pattern)
     #'(lang-add-test-equal! (current-test-language) 'template 'pattern)]))

(define-syntax (test-not-equal stx)
  (syntax-parse stx
    [(_ template pattern)
     #'(lang-add-test-not-equal! (current-test-language) 'template 'pattern)]))

(define (jam-test [lang (current-test-language)]
                  #:tmppath-fmt [tmppath-fmt (format "jam-~a-~~a" (lang-name lang))]
                  #:dest/delete [path/delete #f]
                  #:on-fail [on-fail void])
  (define mods (lang-modules lang))
  (define path*
    (if path/delete
        (begin
          (when (directory-exists? path/delete)
            (delete-directory/files path/delete))
          path/delete)
        (make-temporary-file tmppath-fmt 'directory)))

  (write-modules mods path*)

  (define (is-python? path) (regexp-match? #rx"\\.py$" path))
  (define python (find-executable-path "python"))
  (when python
    (define test-env (environment-variables-copy (current-environment-variables)))
    (parameterize ([current-environment-variables test-env])
      (putenv "JAM_TEST" "")
      (for ([py (in-directory path* is-python?)]
            #:when (file-exists? py))
        (define out (open-output-string))
        (define successful-call
          (parameterize ([current-output-port out])
            (system* python py)))

        (define printed (get-output-string out))
        (define success (and successful-call (not (regexp-match "failed" printed))))
        (unless success
          (displayln printed)
          (on-fail))))))

(require (for-syntax syntax/location racket/list))
(define-syntax (jam-run stx)
  (syntax-parse stx
    [(_ name:id e-name:id
        #:dest/delete dest:expr
        {~optional {~seq #:translate? translate:expr}
                   #:defaults ([translate #'#t])})
     (define lang-defining-path
       (resolve-module-path-index
        (first (identifier-binding #'name))
        (build-path (syntax-source-directory stx)
                    (syntax-source-file-name stx))))

     (unless (complete-path? lang-defining-path)
       (error 'jam-run
              "expected a language name that comes from a file\n\
  name: ~a\n\
  comes from: ~a" (syntax-e #'name) lang-defining-path))

     #`(begin
         (define evaluator
           (make-evaluator name 'e-name dest
                           ;; XXX This is an incomplete list of deps
                           ;; since it doesn't even track jam itself.
                           ;; But it's good enough to start.
                           (list #,lang-defining-path)
                           #:translate? translate))
         (parameterize ([current-read-interaction jam/read-interaction-handler]
                        [current-eval (jam/evaluation-handler evaluator)])
           (read-eval-print-loop)))]))

(define (make-evaluator lang name destdir deps
                        #:translate? [translate? #t])
  (define-values (target in-modules-dir evaluator)
    (if translate?
        (values (build-path destdir (~a name))
                (lambda ()
                  (putenv "JAM_BINARY_NAME" (~a name))
                  (define rpython (find-executable-path "rpython"))
                  (system* rpython "-Ojit" "target.py"))
                (lambda () (system* target)))
        (values (build-path destdir "target.py")
                void
                (lambda ()
                  (define pypy (find-executable-path "pypy"))
                  (system* pypy target)))))

  (parameterize ([make-print-checking #f])
    (make/proc
     `((,target
        ,deps
        ,(lambda ()
           (when (directory-exists? destdir)
             (delete-directory/files destdir))

           (define mods (lang-modules lang #:main-evaluator name))
           (write-modules mods destdir)

           (define env (environment-variables-copy (current-environment-variables)))
           (parameterize ([current-environment-variables env]
                          [current-directory destdir])
             (in-modules-dir)))))))
  evaluator)

(define ((jam/evaluation-handler evaluator) form)
  (match-define `(#%top-interaction . ,datum) form)

  (define-values (src sink) (make-pipe))
  (write-json (term-to-json datum) sink)
  (close-output-port sink)
  (parameterize ([current-input-port src])
    (void (evaluator))))

(define (jam/read-interaction-handler src in)
  (parameterize ([read-accept-reader #f]
                 [read-accept-lang #f])
    (read in)))
