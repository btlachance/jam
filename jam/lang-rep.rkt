
#lang racket
(require (except-in "pattern.rkt" nonterminal)
         "ir.rkt" "rep.rkt"
         racket/syntax)
(provide
 lang/c
 (rename-out [lang-info* lang-info])
 lang-name
 lang-nonterminals
 lang-parse-pattern
 lang-parse-template

 add-metafunction-name!
 register-metafunction!
 lang-register-metafunction!
 lang-metafunction-name?

 lang-add-transition!
 lang-transition-name?

 lang-add-evaluator!
 lang-evaluator-name?

 lang-grammar-module
 lang-metafunction-module
 lang-evaluator-module
 lang-modules
 lang-add-test-equal!
 lang-add-test-not-equal!)

(struct lang-info (name
                   nonterminals
                   nonterminal?
                   terminals
                   parse-pattern
                   parse-template
                   [names #:mutable]
                   [metafunctions #:mutable]
                   [transitions #:mutable]
                   [evaluators #:mutable]
                   [tests #:mutable]))

(define lang/c (rename-contract lang-info? 'lang/c))

(define (lang-name lang) (lang-info-name lang))

(define (lang-nonterminals lang)
  (apply append (map nonterminal-names (lang-info-nonterminals lang))))

(define (lang-parse-pattern lang pattern #:bound-names? [bound-names? #f])
  ((lang-info-parse-pattern lang) pattern bound-names?))

(define (lang-parse-template lang template [names '()])
  ((lang-info-parse-template lang) template names))

(define rep/c
  (rename-contract
   (or/c nt:plain? nt:environment?)
   "a nonterminal rep"))

(define (lang-grammar-module lang #:runtime runtime-handle)
  (grammar-module
   (lang-name lang)
   (map nonterminal-names (lang-info-nonterminals lang))
   (map nonterminal-rep (lang-info-nonterminals lang))
   (lang-info-terminals lang)
   #:runtime runtime-handle))

(define (lang-metafunction-module lang
                                  #:runtime runtime-handle
                                  #:grammar grammar-handles
                                  #:evaluator [evaluator-handle #f])
  (define mfs (lang-info-metafunctions lang))
  (metafunction-module
   (lang-name lang)
   (map metafunction-name mfs)
   (map metafunction-code mfs)
   #:runtime runtime-handle
   #:grammar grammar-handles
   #:evaluator evaluator-handle))

(define (lang-test-module lang runtime-handle other-handles)
  (test-module
   (lang-name lang)
   (lang-info-tests lang)
   runtime-handle
   other-handles))

(define (lang-evaluator-module lang
                               #:runtime runtime-handle
                               [other-handles '()])
  (evaluator-module
   (lang-name lang)
   (lang-info-evaluators lang)
   (lang-info-transitions lang)
   runtime-handle
   other-handles))

(define ((mk/parse-clause lang) arg rhs wheres)
  (define-values (p p-names) (lang-parse-pattern lang arg #:bound-names? #t))
  (define-values (ws names)
    (for/fold ([ws '()]
               [names p-names]
               #:result (values (reverse ws) names))
              ([w wheres])
      (match-define (list pattern template) w)
      (define-values (p p-names)
        (lang-parse-pattern lang pattern #:bound-names? #t))
      (define names* (set-union names p-names))
      (values
       (cons (list p (lang-parse-template lang template names*)) ws)
       names*)))
  (define t (lang-parse-template lang rhs names))
  (clause p t ws))

(define (lang-name-exists? lang name)
  (hash-has-key? (lang-info-names lang) name))

(define (lang-register-metafunction! lang mf-name args rhss wheress)
  (define parse-clause (mk/parse-clause lang))

  (register-metafunction!
   lang
   (metafunction
    mf-name
    (mf:plain
     (compile-clauses
      (lang-name lang)
      (map parse-clause args rhss wheress))))))

(define (add-metafunction-name! lang name)
  (when (lang-name-exists? lang name)
    (error 'add-metafunction-name!
           "name already exists\n  name: ~a"
           name))
  (set-lang-info-names!
   lang
   (hash-set (lang-info-names lang)
             name
             'metafunction)))

(define (lang-metafunction-name? lang x)
  (equal? (hash-ref (lang-info-names lang) x #f) 'metafunction))

;; register-metafunction! : lang metafunction -> void
;; Registers the metafunction to lang only if it's been added and a
;; metafunction with the same name has not already been registered.
(define (register-metafunction! lang mf)
  (define name (metafunction-name mf))
  (unless (lang-metafunction-name? lang name)
    (error 'register-metafunction!
           "metafunction's name isn't waiting to be registered\n  name: ~a"
           name))

  (define metafunctions (lang-info-metafunctions lang))
  (define (same-name? mf0 mf1)
    (define name-of metafunction-name)
    (equal? (name-of mf0) (name-of mf1)))
  (when (member mf metafunctions same-name?)
    (error 'register-metafunction!
           "metafunction's name is already registered\n  name: ~a"
           name))

  (set-lang-info-metafunctions!
   lang
   (cons mf metafunctions)))


(define (lang-add-evaluator! lang name transition-name load unload control-string)
  (define parse-clause (mk/parse-clause lang))

  (add-evaluator!
   lang
   name
   transition-name
   (evaluator:rep
    name
    transition-name
    (apply parse-clause load)
    (apply parse-clause unload)
    (apply parse-clause control-string)))

  (define run-evaluator (format-symbol "run-~a" name))
  (add-metafunction-name! lang run-evaluator)
  (register-metafunction! lang (metafunction run-evaluator (mf:call-evaluator name))))

(define (add-evaluator! lang name transition-name evaluator)
  (when (lang-name-exists? lang name)
    (error 'add-evaluator!
           "name already exists\n  name: ~a"
           name))
  (unless (lang-transition-name? lang transition-name)
    (error 'add-evaluator!
           "named transition doesn't exist\n  name: ~a" transition-name))

  (set-lang-info-names!
   lang
   (hash-set (lang-info-names lang)
             name
             'evaluator))

  (set-lang-info-evaluators!
   lang
   (cons evaluator (lang-info-evaluators lang))))

(define (lang-evaluator-name? lang name)
  (equal? (hash-ref (lang-info-names lang) name #f) 'evaluator))


(define (lang-add-transition! lang name args rhss wheress)
  (define parse-clause (mk/parse-clause lang))

  (add-transition!
   lang
   name
   (transition
    name
    (compile-clauses
     (lang-name lang)
     (map parse-clause args rhss wheress)))))

(define (add-transition! lang name transition)
  (when (lang-name-exists? lang name)
    (error 'add-transition!
           "name already exists\n  name: ~a"
           name))

  (set-lang-info-names!
   lang
   (hash-set (lang-info-names lang)
             name
             'transition))

  (set-lang-info-transitions!
   lang
   (cons transition (lang-info-transitions lang))))

(define (lang-transition-name? lang name)
  (equal? (hash-ref (lang-info-names lang) name #f) 'transition))


(define (add-test! lang ir)
  (set-lang-info-tests! lang (cons ir (lang-info-tests lang))))

(define (lang-add-test-equal! lang check expect)
  (add-test!
   lang
   (compile-test (lang-name lang)
                 (lang-parse-template lang check)
                 (lang-parse-template lang expect)
                 (format "expected ~a to equal ~a, but it didn't"
                         check
                         expect)
                 #:equal? #t)))

(define (lang-add-test-not-equal! lang check expect)
  (add-test!
   lang
   (compile-test (lang-name lang)
                 (lang-parse-template lang check)
                 (lang-parse-template lang expect)
                 (format "expected ~a to not equal ~a, but it did"
                         check
                         expect)
                 #:equal? #f)))

;; a data-include is a (list (nelistof symbol) data-app)
;;   where the data-app represents some datatype and the symbol is the
;;   name that datatype is bound to

;; a data-app is a (list (nelistof symbol) pattern ...)

;; a data-include* is a (list (nelistof pattern) pattern ...)
;;   where the first pattern for the nonterminal that this datatype is
;;   bound to

(define data-include-name first)
(define (data-include*-nonterminal names constructor include*)
  (nonterminal
   names
   (data-app-rep constructor (rest include*))))
(define (data-include*-metafunctions names constructor include*)
  (nonterminal-metafunctions
   names
   (first include*)
   (data-app-rep constructor (rest include*))))

(define (data-app-rep constructor args)
  (apply (hash-ref builtins constructor) args))

;; lang-info* : (symbol (listof (listof symbol)) (listof (listof s-exp)))
;;              ((listof data-include)) -> lang-info
(define (lang-info* name lhss rhss [includes '()])
  (define nonterminal-names
    (set-union
     (for/fold ([nonterminals (set)])
               ([lhs lhss])
       (set-union nonterminals (list->set lhs)))
     (list->set (apply append (map data-include-name includes)))))
  (define (nonterminal? x) (set-member? nonterminal-names x))

  (define-values (parse-pattern parse-grammar-pattern parse-template)
    ;; Making the metafunction-name? predicate here is a bit annoying, but I think
    ;; it'd be more annoying to split up parsers into two functions (one that makes
    ;; the pattern parsers and one that makes the template parser)
    (parsers name nonterminal? (lambda (x) (lang-metafunction-name? info x))))

  (define inamess (map data-include-name includes))
  (define iconstructors (map (lambda (i) (first (second i))) includes))
  (define includes*
    (for/list ([i includes])
      (define names (data-include-name i))
      (define (parse p) (parse-pattern p #f))
      (cons (map parse names)
            (map parse
                 (match i
                   [`(,nt (,constructor ,@rest)) rest])))))

  (define-values (terminals nonterminals)
    (for/fold ([terminals (set)]
               [nonterminals '()]
                #:result (values (set->list terminals) nonterminals))
               ([names lhss]
                [rhs rhss])

      (define (terminals-of p)
        (define (add-terminal lit terminals)
          (match lit
            [(literal (? symbol? s)) (set-add terminals lit)]
            [_ terminals]))
        (fold-pattern-literals add-terminal (set) p))

      (define patterns (map parse-grammar-pattern rhs))

      (values (apply set-union terminals (map terminals-of patterns))
              (cons (nonterminal names (nt:plain patterns)) nonterminals))))
  ;; TODO check for cycles/well-foundedness, e.g. no (e ::= (f e e))

  (define include-nonterminals
    (map data-include*-nonterminal
         inamess iconstructors includes*))
  (define include-metafunctions
    (apply append (map data-include*-metafunctions
                       inamess iconstructors includes*)))

  (define info
    (let ([metafunctions (append include-metafunctions predefined-metafunctions)])
      (lang-info name (append nonterminals include-nonterminals) nonterminal?
                 terminals parse-pattern parse-template

                 (for/hash ([mf-name (map metafunction-name metafunctions)])
                   (values mf-name 'metafunction))

                 metafunctions
                 '() #; transitions
                 '() #; evaluators
                 '() #; tests)))
  info)

(define no-duplicates/c
  (rename-contract
   (negate check-duplicates)
   "a list with no duplicates"))

(define (lang-modules lang
                      #:main-evaluator [main-evaluator #f])
  (when (and main-evaluator (not (lang-evaluator-name? lang main-evaluator)))
    (error 'lang-modules
           "expected name of a main evaluator that is defined\n\
  name: ~a\n\
  defined evaluators: ~a"
           main-evaluator
           (apply
            ~a
            #:separator ", "
           (for/list ([(name kind) (in-hash (lang-info-names lang))]
                      #:when (equal? kind 'evaluator))
             name))))

  (define-values (rmod-handle rmod) (runtime-module))

  (define-values (gmod-handle gmod) (lang-grammar-module
                                     lang
                                     #:runtime rmod-handle))

  (define-values (mmod-handle mmod) (lang-metafunction-module
                                     lang
                                     #:runtime rmod-handle
                                     #:grammar (list gmod-handle)
                                     #:evaluator (and (not (null? (lang-info-evaluators lang)))
                                                      (evaluator-handle (lang-name lang)))))

  (define main
    (if main-evaluator
        (main-module main-evaluator
                     #:runtime rmod-handle
                     #:evaluator (evaluator-handle (lang-name lang)))
        (default-main-module)))

  (define mods
    (append
     (if (null? (lang-info-tests lang))
         '()
         (let-values ([(_ tmod)
                       (lang-test-module
                        lang
                        rmod-handle
                        (list gmod-handle mmod-handle))])
           (list tmod)))
     (if (null? (lang-info-evaluators lang))
         '()
         (let-values ([(_ emod)
                       (lang-evaluator-module
                        lang
                        #:runtime rmod-handle
                        (list gmod-handle mmod-handle))])
           (list emod)))
     (list rmod gmod mmod main)))

  (translate-modules mods
                     #:runtime rmod-handle
                     #:grammar (list gmod-handle)
                     #:metafun (list mmod-handle)))

(define builtins
  (hash 'environment ((curry nt:environment) 'is_environment)))

(define predefined-metafunctions
  (list
   (metafunction
    'reverse
    (mf:data 'list_reverse (repeat-pattern '_)))
   (metafunction
    'integer-add
    (mf:data 'integer_add0 (pattern-of-ps (list 'integer 'integer))))
   (metafunction
    'integer-subtract
    (mf:data 'integer_subtract0 (pattern-of-ps (list 'integer 'integer))))
   (metafunction
    'integer-multiply
    (mf:data 'integer_multiply0 (pattern-of-ps (list 'integer 'integer))))))

(define (nonterminal-metafunctions nt-names nts rep)
  (match rep
    [(nt:environment _ kp vp)
     (apply
      append
      (for/list ([nt-name nt-names]
                 [nt nts])
        (define (mf-name suffix) (format-symbol "~a-~a" nt-name suffix))
        (list (metafunction
               (mf-name 'lookup)
               (mf:data 'environment_lookup (pattern-of-ps (list nt kp))))

              (metafunction
               (mf-name 'bound?)
               (mf:data 'environment_is_bound (pattern-of-ps (list nt kp))))

              (metafunction
               (mf-name 'extend1)
               (mf:data 'environment_extend1 (pattern-of-ps (list nt kp vp))))

              (let ([kps (repeat-pattern kp)]
                    [vps (repeat-pattern vp)])
                (metafunction
                 (mf-name 'extend)
                 (mf:data 'environment_extend (pattern-of-ps (list nt kps vps)))))

              (metafunction
               (mf-name 'empty)
               (mf:data 'environment_empty (pattern-of-ps '()))))))]))
