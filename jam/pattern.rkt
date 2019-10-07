#lang racket
(require syntax/parse racket/hash racket/syntax "ir.rkt"
         (except-in "rep.rkt" nonterminal)
         "term-to-json.rkt" json)
(provide parsers pattern-keyword?
         fold-pattern-literals suffixed-underscore?
         compile/guard compile/deconstruct compile/transcribe compile-clauses
         compile-test
         grammar-module metafunction-module test-module
         evaluator-module main-module default-main-module
         translate-modules lift-procs
         grammar-handle evaluator-handle core-handle
         (struct-out name) (struct-out literal) clause mf-apply pair
         nonterminal pattern-of-ps repeat-pattern integer-pattern
         string-pattern real-pattern)

(define real-pattern 'real)
(define integer-pattern 'integer)
(define string-pattern 'string)

;; a datum is one of
;; - symbol
;; - exact-integer
;; - flonum
;; - string
;; - boolean

;; a pattern is one of
;; - '_
;; - 'integer
;; - 'real
;; - 'string
;; - 'boolean
;; - 'variable-not-otherwise-mentioned
;; - (nonterminal symbol)
;; - (name symbol pattern)
;; - (literal datum)
;; - list-pattern
(struct nonterminal (nt) #:transparent)
(struct name (name pattern) #:transparent)
(struct literal (v) #:transparent)

;; a list-pattern is one of
;; - '()
;; - (repeat pattern)
;; - (pair pattern list-pattern)
(struct repeat (p) #:transparent)
(struct pair (head tail) #:transparent)

;; XXX If we wanted to instead use the surface syntax as our
;; representation for patterns (so that we wouldn't have to write an
;; unparser to show users where their errors were) we could define
;; match expanders to handle some of the repetitive things like
;; handling naming forms

(define datum/c (or/c symbol? string? flonum? exact-integer? boolean?))

(define (fold-pattern-literals f z p)
  (match p
    ['_ z]
    [(== integer-pattern) z]
    [(== real-pattern) z]
    [(== string-pattern) z]
    ['boolean z]
    ['variable-not-otherwise-mentioned z]
    [(nonterminal _) z]
    [(name _ p) (fold-pattern-literals f z p)]
    [(literal _) (f p z)]
    ['() z]
    [(repeat p) (fold-pattern-literals f z p)]
    [(pair p lp)
     (fold-pattern-literals f (fold-pattern-literals f z lp) p)]))

(define pattern-keywords (set '_ integer-pattern string-pattern real-pattern 'variable-not-otherwise-mentioned 'boolean))
(define (pattern-keyword? x)
  (match x
    [(? identifier? id)
     (pattern-keyword? (syntax-e id))]
    [(? symbol? s) (set-member? pattern-keywords s)]
    [_ #f]))

(define-values (pattern/c list-pattern/c)
  (flat-murec-contract
   ([pattern/c
     (or/c pattern-keyword?
           (struct/c literal datum/c)
           list-pattern/c)]

    [list-pattern/c
     (or/c '()
           (struct/c repeat pattern/c)
           (struct/c pair pattern/c list-pattern/c))])
   (values pattern/c list-pattern/c)))

(define (name-ocurrences-in p)
  (match p
    ['_ '()]
    [(name var p) (list var)]
    [(literal _) '()]
    ['() '()]
    [(repeat p) (name-ocurrences-in p)]
    [(pair p p*)
     (append (name-ocurrences-in p)
             (name-ocurrences-in p*))]))

(define (symbol-before-underscore name-str)
  (match (string-split name-str "_" #:trim? #f #:repeat? #f)
    [(list _) (string->symbol name-str)]
    [(list before _)
     (string->symbol before)]))

(define (underscore? id) (equal? (syntax-e id) '_))

(define (suffixed-underscore? id)
  (match (syntax-e id)
    [(? symbol? s)
     (define id-str (symbol->string s))
     (and (string-prefix? id-str "_")
          (string-prefix? (substring id-str 1) "_"))]
    [_ #f]))


(define-syntax-class jam-id
  (pattern x:id
           #:fail-when (and (equal? (syntax-e #'x) '...)
                            #'x)
           "ellipses must only appear at the end of parens"))

;; INV: for any symbol s, (not (and (nonterminal? s) (patten-keyword? s)))

(define (compile/guard p lang-id [source (lexical-var* 't)])
  (define (compile p [s source]) (compile/guard p lang-id s))
  (match p
    ['_
     #t]

    [(== integer-pattern)
     `(integer? ,source)]

    [(== real-pattern)
     `(real? ,source)]

    [(== string-pattern)
     `(string? ,source)]

    ['boolean
     `(boolean? ,source)]

    ['variable-not-otherwise-mentioned
     `(and (symbol? ,source)
           (not (terminal? (lang ,lang-id) ,source)))]

    [(nonterminal s)
     `(produced-by? (lang ,lang-id) (nt ,s) ,source)]

    [(name _ p) (compile p)]

    [(literal (? symbol? s))
     `(= (symbol ,s) ,source)]

    [(literal (? exact-integer? n))
     `(= (integer ,n) ,source)]

    [(literal (? flonum? n))
     `(= (real ,n) ,source)]

    [(literal (? string? s))
     `(= (string ,s) ,source)]

    [(literal (? boolean? b))
     `(= (boolean ,b) ,source)]

    ['()
     `(nil? ,source)]

    [(repeat p)
     `(and (list? ,source)
           (all? ,(proc* '(t) (compile p (lexical-var* 't))) ,source))]

    [(pair p lp)
     `(and (pair? ,source)
           ,(compile p `(hd ,source))
           ,(compile lp `(tl ,source)))]))

;; INV: p doesn't contain duplicate bindings
(define (compile/deconstruct p [source (lexical-var* 't)])
  (match p
    [(or '_
         '()
         ;; this means literal integers and nil in a template might
         ;; need to be freshly allocated
         (literal (? exact-integer? _))
         (literal (? flonum? _))
         (literal (? string? _))
         (literal (? boolean? _)))
     (hash)]

    [(name '_ _) ;; In the rare case that someone wants to match the
                 ;; same literal symbol in two different parts of a
                 ;; pattern, they have to use a name pattern: either
                 ;; by using the underscore as the name part to say
                 ;; they don't want the binding (handled by this part
                 ;; of the match) or by using distinct names in the
                 ;; name part. If we had constructors where you
                 ;; couldn't match on the name of the constructor then
                 ;; this would be even rarer
     (hash)]

    [(or (and s (or (== integer-pattern) (== real-pattern) (== string-pattern) 'variable-not-otherwise-mentioned 'boolean))
         (nonterminal s)
         (literal (? symbol? s))
         (name s _))
     (hash s (list 0 source))]

    [(repeat p)
     (for/hash ([(name info) (in-hash (compile/deconstruct p))])
       (match info
         [(list n selector)
          (values name (list (add1 n) `(map ,(proc* '(t) selector) ,source)))]))]

    [(pair p lp)
     (hash-union (compile/deconstruct p `(hd ,source))
                 (compile/deconstruct lp `(tl ,source)))]))

(define (free-vars p)
  (match p
    [(or '_ '()) (set)]
    [(or (and x (or (== integer-pattern) (== real-pattern) (== string-pattern) 'variable-not-otherwise-mentioned 'boolean))
         (literal (? symbol? x)))
     (set x)]
    [(name x _) (set x)]
    [(repeat p) (free-vars p)]
    [(pair p lp) (set-union (free-vars p) (free-vars lp))]
    [(mf-apply _ _ t) (free-vars t)]))

(define (compile/transcribe template env)
  (define (compile/t t) (compile/transcribe t env))
  (define (level-of i)
    (match (dict-ref env i)
      [(list level _) level]))

  (define (scalar? i) (zero? (level-of i)))

  (define (selector-of i)
    (match (dict-ref env i)
      [(list _ selector) selector]))

  (define (err:missing-ellipses p)
    (error 'compile/transcribe "an identifier can only be used in a template \
when its ellipses depth is zero\n  template: ~a\n  identifier: ~a\n  depth: ~a"
           template p (level-of p)))
  (define (err:not-controllable)
    (error 'compile/transcribe "ellipses can only be used when the template \
contains at least one variable with nonzero ellipses depth\n  template: ~a\n  depths: ~a"
           template
           (for/list ([i (free-vars template)])
             (list i (level-of i)))))

  (match template
    [(mf-apply lang-name name rand)
     `(mf-apply (lang ,lang-name) ,name ,(compile/t rand))]
    [(and x (or (== integer-pattern) (== real-pattern) (== string-pattern) 'variable-not-otherwise-mentioned 'boolean))
     (unless (dict-has-key? env x)
       (error 'compile/transcribe "keyword in template is unbound\n\
  keyword: ~a" x))
     (unless (scalar? x) (err:missing-ellipses x))
     (selector-of x)]

    ;; XXX This is a bit of a mess. Parsing a template apparently
    ;; never produces a (nonterminal x), it only produces nonterminals
    ;; in a name. When the two are the same then it wasn't an
    ;; underscored one, which means it may have been meant as a
    ;; literal symbol.
    [(or (nonterminal x)
         (name x (nonterminal x)))
     #:when (not (dict-has-key? env x))
     `(symbol ,x)]

    [(or (nonterminal x)
         (name x _))

     (unless (dict-has-key? env x)
       (error 'compile/transcribe "variable in template is unbound\n\
  variable: ~a" x))
     (unless (scalar? x) (err:missing-ellipses x))
     (selector-of x)]

    [(literal (? symbol? s))
     (if (dict-has-key? env s)
         (begin
           (unless (scalar? s) (err:missing-ellipses s))
           (selector-of s))
         `(symbol ,s))]

    [(literal (? exact-integer? n))
     `(integer ,n)]

    [(literal (? flonum? n))
     `(real ,n)]

    [(literal (? string? s))
     `(string ,s)]

    [(literal (? boolean? b))
     `(boolean ,b)]

    ['() `(nil)]
    [(repeat p)
     ;; XXX if p is a name pattern or if it's a symbol (and it's bound
     ;; in the environment at the appropriate depth) then we can just
     ;; look its selector up in the environment and return that---like
     ;; the "most common use of ellipses" referred to in the MBE paper
     ;; §5.

     (define frees (set->list (free-vars p)))
     (unless (ormap (compose not scalar?) frees) (err:not-controllable))

     (define decomp-env
       (for/fold ([decomp-env (hash)]
                  [source (lexical-var* 't)]
                  #:result decomp-env)
                 ([i frees])
         (define n (level-of i))

         (values (hash-set decomp-env
                           i (list (max 0 (sub1 n)) `(hd ,source)))
                 `(tl ,source))))

     (define (boxed-level x) `(integer ,(level-of x)))
     `(map ,(proc* '(t) (compile/transcribe p decomp-env))
           (decompose-values (list ,@(map boxed-level frees))
                             (list ,@(map selector-of frees))))]
    [(pair p lp)
     `(pair ,(compile/t p)
            ,(compile/t lp))]))

;; Redex docs often use the word term to refer to values and to
;; syntax; I'm distinguishing them: template is the syntax, term is
;; value.

;; a term is one of
;; - datum
;; - (listof term)

;; a template is one of
;; - pattern, except for _ and name forms whose pattern isn't a nonterminal
;; - (mf-apply symbol symbol template)
(struct mf-apply (lang-name rator rand) #:transparent)

(define-syntax-class (metafunction-app lang-name mf-name? parse)
  #:attributes (data)
  #:no-delimit-cut
  (pattern (rator:jam-id . rands)
           #:when (mf-name? (syntax-e #'rator))
           ;; This was really subtle: all of the arguments to a
           ;; metafunction have to be parsed as a single template.
           ;; Why? At least for now, it's how I can support parsing
           ;; something like (mf x ...)
           #:attr data (mf-apply lang-name (syntax-e #'rator) (parse #'rands)))
  (pattern rator:jam-id
           #:when (mf-name? (syntax-e #'rator))
           ;; #:cut
           #:attr data #f
           #:fail-when #'rator
           "metafunctions must be applied"))

(define (parsers lang-id nonterminal? metafunction-name?)
  (define (parse-template stx names)
    (define (parse stx) (parse-template stx names))
    (syntax-parse stx
      #:datum-literals (name)
      [{~var m (metafunction-app lang-id metafunction-name?
                                 parse)}
       (attribute m.data)]
      [{~or {~and {~datum _} ~! {~fail "underscores are only allowed in a pattern"}}
            {~and (name x:id _) ~! {~fail "name forms are only allowed in a pattern"}}}
       (error 'this-cant-happen)]

      [x:id
       (if (set-member? names (syntax-e #'x))
           ;; XXX Not certain the underscore pattern is the right thing
           ;; here but I don't know what other template I could possibly
           ;; produce. Need to update the definition of what a template is
           ;; since technically name forms aren't a template
           (name (syntax-e #'x) '_)
           (literal (syntax-e #'x)))]

      [_ (parse-pattern this-syntax #:recur parse)]))

  (define (parse-pattern stx #:recur [recur #f])
    (define recur* (or recur parse-pattern))
    (syntax-parse stx
      #:datum-literals (name)
      [x:jam-id
       #:when (pattern-keyword? #'x)
       (if (underscore? #'x)
           (syntax-e #'x)
           (name (syntax-e #'x) (syntax-e #'x)))]

      [x:jam-id
       #:fail-when (suffixed-underscore? #'x)  "underscores cannot have a suffix"
       #:do [(define name-str (symbol->string (syntax-e #'x)))
             (define prefix (symbol-before-underscore name-str))]
       #:fail-when (and (not (nonterminal? prefix))
                        (not (pattern-keyword? prefix))
                        #'x)
       "literal symbols cannot have a suffix"
       (name (syntax-e #'x) (if (pattern-keyword? prefix)
                                prefix
                                (nonterminal prefix)))]

      [{~or :jam-id :exact-integer :boolean :string}
       (literal (syntax-e this-syntax))]

      [r:expr
       #:when (flonum? (syntax-e #'r))
       (literal (syntax-e #'r))]

      [(name x:jam-id p)
       (name (syntax-e #'x) (recur* #'p))]


      [(_ ...)
       (parse-list-pattern this-syntax recur*)]))

  (define (parse-list-pattern stx parse-pattern)
    (syntax-parse stx
      [() '()]
      [(p {~datum ...})
       (repeat (parse-pattern #'p))]
      [(hd . rest)
       (pair (parse-pattern #'hd)
             (parse-list-pattern #'rest parse-pattern))]))

  (define (parse-pattern/no-duplicates stx bound-names?)
    (define result (parse-pattern stx))
    (define bound (name-ocurrences-in result))
    (match (check-duplicates bound)
      [(? symbol? dup)
       (error 'name "expected a pattern with no duplicate names\n\
  pattern: ~a\n\
  duplicated: ~a" stx dup)]
      [#f (if (not bound-names?) ;; XXX Instead we should have a
                                 ;; datatype for parse results (which
                                 ;; can then carry error information,
                                 ;; too)
              result
              (values result bound))]))

  (values parse-pattern/no-duplicates parse-pattern parse-template))

;; a clause is a (clause pattern template (listof (list pattern template)))
;; Note: the main pattern in the clause is matched against a list of
;; terms whereas the where-patterns are matched against the result of
;; the corresponding template
(struct clause (pattern template wheres) #:transparent)

(define (compile-clause lang-name p t ws
                        #:arg-name [arg-name #f]
                        #:with-match [with-match values]
                        #:no-match [no-clause-match '(error)])
  (define args (list (or arg-name (gensym 'cterm))))
  (define final-dest (gensym 'result))
  (define where-tmps (for/list ([_ ws]) (gensym 'tmp)))

  (define templates (append (map second ws) (list t)))
  (define patterns (cons p (map first ws)))
  (define dests (append where-tmps (list final-dest)))
  (define srcs (cons (lexical-var* (car args)) (map lexical-var* where-tmps)))
  (define envs (for/lists (envs)
                          ([p patterns]
                           [s srcs])
                 (if (null? envs)
                     (compile/deconstruct p s)
                     (let ([prev-env (car envs)])
                       (hash-union prev-env
                                   (compile/deconstruct p s)
                                   #:combine (lambda (_ v) v))))))
  (proc* args
         (foldr (lambda (p src dest t env body)
                  `(if ,(compile/guard p lang-name src)
                       ,(lett* dest (compile/transcribe t env)
                               body)
                       ,no-clause-match))
                (with-match (lexical-var* final-dest))
                patterns
                srcs
                dests
                templates
                envs)))

;; compile-clauses : symbol (listof ir) (#:no-match ir) -> ir
(define (compile-clauses lang-name cs #:no-match [no-clause-match '(error)])
  (define proc-names (for/list ([_ cs]) (gensym 'cproc)))
  (define arg-names (for/list ([_ cs]) (gensym 'cterm)))
  (define no-matches
    (append
     (for/list ([next-proc (cdr proc-names)]
                [current-arg arg-names])
       `(call ,(lexical-var* next-proc) ,(lexical-var* current-arg)))
     (list no-clause-match)))

  (define (compile-clause* c arg no-match)
    (match-define (clause p t ws) c)
    (compile-clause lang-name p t ws
                    #:arg-name arg
                    #:no-match no-match))
  (define procs (map compile-clause* cs arg-names no-matches))
  (define arg-name 't)
  (define call-first `(call ,(lexical-var* (car proc-names))
                            ,(lexical-var* arg-name)))

  (proc* `(,arg-name) (foldl lett* call-first proc-names procs)))

(define terminal?-name 'terminal?)

;; a module-handle is one of
;; - 'core
;; - (lang-module-handle symbol symbol)
(struct lang-module-handle (lang-id mod-id) #:transparent)

(define (grammar-handle lang-id)
  (define mod-id (format-symbol "~a-grammar" lang-id))
  (lang-module-handle lang-id mod-id))

;; XXX For now verything imports both core and runtime. Only things
;; that use the prim ir (e.g. a definition referring to a
;; prim-class/prim-procedure) need to import core, and eventually that
;; will be cleaned up so things that don't need core don't import
;; it. Thus the distinction between core and runtime.
(define core-handle 'core)
(define (builtin-handle? v) (eq? v core-handle))

(define (require-for-handle h)
  (match h
    [(? builtin-handle? v) v]
    [(lang-module-handle _ mod-id) mod-id]))
(define mod-id-for-handle require-for-handle)
;; XXX Check here and other places that we actually want a modvar with
;; no annotations (e.g. what annotations might we want clients of
;; modvar-for-handle to see? should those annotations come from the
;; handle?)
(define (modvar-for-handle h id)
  (match h
    [(? builtin-handle? v) (module-var* h id)]
    [(lang-module-handle _ mod-id) (module-var* mod-id id)]))

(define (annotate-test-exceptions v)
  (define (core s) (modvar-for-handle core-handle s))

  (annotate (annotate v 'success-exn (core 'ExnTestSuccess))
            'failure-exn (core 'ExnTestFailure)))

;; XXX uses of the runtime functions inside the runtime module is
;; currently very hacky. Any use of thiso function is likely
;; duplicating some of the work done in translate-runtime; see the
;; call to pass-test below as an example
(define (internal-ref name py-name)
  (annotate (lexical-var* name) 'py-name py-name))

(define (main-module ev-name
                     #:evaluator ev-handle)

  (define-values (result tmp) (values (gensym 'result) (gensym 'tmp)))
  `(module main
     (require ,@(map require-for-handle (list core-handle ev-handle)))
     (provide main)

     ,(define:* 'main
        (proc* '(t) (lett* result `(call ,(modvar-for-handle ev-handle ev-name)
                                      ,(lexical-var* 't))
                           (lett* tmp (print-term* (lexical-var* result))
                                  0))))))

(define (default-main-module)
  `(module main
     (require)
     (provide main)

     ,(define:* 'main (proc* '(t) 0))))

(define (pred-name nt-name) (format-symbol "nt-~a?" nt-name))

;; ir -> cgmir
(define (translate-runtime ir)
  (define (call-prim id . args)
    `(call ,(modvar-for-handle core-handle id) ,@args))

  (define translate translate-runtime)

  (define (translate-body ir)
    (match ir
      [(lett* _ rhs body)
       (struct-copy lett ir
                    [rhs (translate rhs)]
                    [body (translate-body body)])]
      [`(if ,ir ,then ,else)
       `(if ,(translate ir)
            ,(translate-body then)
            ,(translate-body else))]

      [(noop*) ir]

      [_ (translate ir)]))

  (match ir
    [(or (lexical-var* _) (module-var* _ _) (? string? _) (? exact-integer? _) (? flonum? _) (? boolean? _))
     ir]

    ['(nil) (call-prim 'nil)]
    [(none*) (call-prim 'none)]
    [`(pair ,hd ,tl) (call-prim 'pair (translate hd) (translate tl))]
    [`(symbol ,s) (call-prim 'symbol (symbol->string s))]
    [`(integer ,n) (call-prim 'integer n)]
    [`(real ,n) (call-prim 'real n)]
    [`(string ,s) (call-prim 'string s)]
    [`(boolean ,b) (call-prim 'boolean b)]

    [`(hd ,arg) (call-prim 'hd (translate arg))]
    [`(tl ,arg) (call-prim 'tl (translate arg))]

    [`(= ,arg0 ,arg1)
     (call-prim '= (translate arg1) (translate arg0))]
    [`(if ,e1 ,e2 ,e3) `(if ,(translate e1) ,(translate e2) ,(translate e3))]
    [`(not ,ir) `(not ,(translate ir))]
    [`(and ,@irs) `(and ,@(map translate irs))]
    [`(or ,@irs) `(or ,@(map translate irs))]
    [`(nil? ,arg) (call-prim 'nil? (translate arg))]
    [`(pair? ,arg) (call-prim 'pair? (translate arg))]
    [`(symbol? ,arg) (call-prim 'symbol? (translate arg))]
    [`(integer? ,arg) (call-prim 'integer? (translate arg))]
    [`(real? ,arg) (call-prim 'real? (translate arg))]
    [`(string? ,arg) (call-prim 'string? (translate arg))]
    [`(boolean? ,arg) (call-prim 'boolean? (translate arg))]
    [`(list? ,arg) (call-prim 'list? (translate arg))]
    [(print-term* ir) (call-prim 'print-term (translate ir))]

    [`(all? ,ir ,arg)
     (call-prim 'all? (translate ir) (translate arg))]

    [`(produced-by? ,lang ,nt ,ir) `(produced-by? ,lang ,nt ,(translate ir))]

    [`(terminal? ,lang ,ir) `(terminal? ,lang ,(translate ir))]

    ;; XXX This case bit me. Maybe the rest param in call-runtime
    ;; wasn't worth it in the end?
    [`(list ,@args)
     (define ir
       (foldr (lambda (arg termlist) `(pair ,arg ,termlist))
              '(nil)
              args))

     (translate ir)]

    [`(map ,ir ,arg)
     (call-prim 'map (translate ir) (translate arg))]

    [`(mf-apply ,lang ,name ,ir)
     `(mf-apply ,lang ,name ,(translate ir))]

    [(proc* _ body)
     (struct-copy proc ir
                  [body (translate-body body)])]

    [`(decompose-values ,levels ,values)
     (call-prim 'decompose-values (translate levels) (translate values))]

    ['(error) (call-prim 'error)]

    [(fail-test* s wit) (call-prim 'fail-test s (translate wit))]
    [(pass-test*) (call-prim 'pass-test)]

    [(done* ir) (call-prim 'done ir)]

    [`(call ,var ,@args)
     `(call ,var ,@(map translate args))]))

(define (grammar-module lang-id namess reps terminals)

  (define handle (grammar-handle lang-id))
  (define (compile/g p) (compile/guard p lang-id (lexical-var* 't)))
  (define (nt-fun guards) (proc* '(t) `(or ,@(map compile/g guards))))
  (define (error-if-not-same-prim key ir1 ir2)
    (match* (ir1 ir2)
      [(`(prim-procedure ,name1) `(prim-procedure ,name2))
       #:when (equal? name1 name2)
       ir1]
      [(_ _)
       (raise-arguments-error
        'compile-nonterminal-predicate
        "same key was mapped to two different ir"
        "key" key
        "ir" ir1
        "ir" ir2)]))

  ;; for nonterminals with more than 1 name, we emit multiple entries
  ;; but only the first one has the compiled pattern code; the
  ;; remaining simply delegate to the first.
  (define (compile-nonterminal-predicate names rep)
    (define primary-name (pred-name (car names)))
    (match rep
      [(nt:plain patterns)
       (hash-union
        (hash primary-name (nt-fun patterns))
        (for/hash ([name (cdr names)])
          (values (pred-name name) (proc* '(t) `(call ,(lexical-var* primary-name) ,(lexical-var* 't))))))]

      [(or (nt:environment pred-py-name _ _)
           (nt:mutable-sequence pred-py-name _)
           (nt:immutable-sequence pred-py-name _)
           (nt:file pred-py-name)
           (nt:location pred-py-name)
           (nt:store pred-py-name _ _))
       (define primary-ir
         (proc* '(t) `(call ,(internal-ref pred-py-name pred-py-name)
                            ,(lexical-var* 't))))
       (hash-union
        (hash primary-name primary-ir
              pred-py-name `(prim-procedure ,pred-py-name))
        (for/hash ([name (cdr names)])
          (values (pred-name name) (proc* '(t) `(call ,(lexical-var* primary-name) ,(lexical-var* 't))))))]))

  (define grammar-functions
    (apply hash-union
           (hash terminal?-name (nt-fun terminals))
           (map compile-nonterminal-predicate namess reps)
           ;; Want to support multiple uses of the same built-in eg
           ;; for two different kinds of environments (the Impcore
           ;; spec needs this) and since I want to include a reference
           ;; to the prim that's used by the nonterminal predicate, I
           ;; need some way to allow it to be included multiple times.
           #:combine/key error-if-not-same-prim))

  (values
   handle
   `(module ,(mod-id-for-handle handle)
      (require ,@(map require-for-handle (list core-handle)))
      (provide ,@(hash-keys grammar-functions))
      ,@(for/list ([(name proc) (in-hash grammar-functions)])
          (define:* name proc)))))

;; translate-grammar : (listof lang-module-handle) symbol cgmir -> cmir
(define (translate-grammar grammar-handles current-mod ir)
  (define (translate ir) (translate-grammar grammar-handles current-mod ir))
  (define (translate-body ir)
    (match ir
      [(lett* _ rhs body)
       (struct-copy lett ir
                    [rhs (translate rhs)]
                    [body (translate-body body)])]
      [`(if ,ir ,then ,else)
       `(if ,(translate ir)
            ,(translate-body then)
            ,(translate-body else))]

      [(noop*) ir]

      [_ (translate ir)]))

  (define (handle-for-lang lang-id)
    (findf
     (lambda (h) (equal? lang-id (lang-module-handle-lang-id h)))
     grammar-handles))

  (define (mod-id-for-lang lang)
    (match (handle-for-lang lang)
      [(lang-module-handle _ mod-id) mod-id]
      [#f (error 'translate-grammar
                 "couldn't find lang handle in handles\n\
  lang: ~a\n\
  handles: ~a" lang grammar-handles)]))

  (match ir
    [(module-var* x _)
     #:when (equal? x current-mod)
     (error 'translate-grammar
            "internal: got a grammar module that referred to itself\n\
  module: ~a" current-mod)]

    [(or (lexical-var* _) (module-var* _ _) (? string? _) (? exact-integer? _) (? flonum? _) (? boolean? _))
     ir]

    [`(if ,e1 ,e2 ,e3)
     `(if ,(translate e1) ,(translate e2) ,(translate e3))]

    [`(not ,ir) `(not ,(translate ir))]
    [`(and ,@irs) `(and ,@(map translate irs))]
    [`(or ,@irs) `(or ,@(map translate irs))]

    [`(produced-by? (lang ,lang) (nt ,nt) ,ir)
     (define mod-id (mod-id-for-lang lang))

     `(call
       ,(if (equal? current-mod mod-id)
            (lexical-var* (pred-name nt))
            (module-var* mod-id (pred-name nt)))
       ,(translate ir))]

    [`(terminal? (lang ,lang) ,ir)
     (define mod-id (mod-id-for-lang lang))
     `(call
       ,(if (equal? current-mod mod-id)
            (lexical-var* terminal?-name)
            (module-var* mod-id terminal?-name))
       ,(translate ir))]

    [`(mf-apply ,lang ,name ,ir)
     `(mf-apply ,lang ,name ,(translate ir))]

    [(proc* _ body)
     (struct-copy proc ir
                  [body (translate-body body)])]

    [`(call ,var ,@irs)
     `(call ,var ,@(map translate irs))]))

(define (metafunction-module lang-id mf-names mf-reps
                             #:grammar grammar-handles
                             #:evaluator [evaluator-handle #f])
  (define mod-id (format-symbol "~a-metafun" lang-id))
  (values
   (lang-module-handle lang-id mod-id)
   `(module ,mod-id
        (require ,@(map require-for-handle
                        (append (list core-handle)
                                (if evaluator-handle
                                    (list evaluator-handle)
                                    '())
                                grammar-handles)))
      (provide ,@mf-names)
      ,@(apply
         append
         (for/list ([name mf-names]
                    [rep mf-reps])
           (match rep
             [(mf:plain ir) (list (define:* name ir))]
             [(mf:data py-name args)
              (define internal (format-symbol "internal-~a" name))

              ;; XXX the way I produce code for defining a name bound
              ;; to a prim-procedure is causing problems: since it
              ;; ignores the name that it's defined as and just
              ;; produces the name in the prim-procedure, I can't have
              ;; a metafunction name that's the same as one of the
              ;; prim-procedure names, e.g. defining a metafunction
              ;; named reverse that uses a prim-procedure named
              ;; reverse
              (list (define:* internal `(prim-procedure ,py-name))
                    (define:* name
                      (proc* '(t)
                             `(if ,(compile/guard args lang-id (lexical-var* 't))
                                  (call ,(lexical-var* internal) ,(lexical-var* 't))
                                  (error)))))]
             [(mf:call-evaluator e)
              (unless evaluator-handle
                (error 'metafunction-module
                       "got a mf:call-evaluator but evaluator-handle was #f"))
              (list (define:* name
                      (proc* '(t)
                             `(if (and (pair? ,(lexical-var* 't))
                                       (nil? (tl ,(lexical-var* 't))))
                                  (call ,(modvar-for-handle evaluator-handle e)
                                        (hd ,(lexical-var* 't)))
                                  (error)))))]))))))

;; translate-metafunction : (listof module-handle) symbol cmir -> cir
(define (translate-metafunction metafun-handles current-mod ir)
  (define (translate ir) (translate-metafunction metafun-handles current-mod ir))

  (define (translate-body ir)
    (match ir
      [(lett* _ rhs body)
       (struct-copy lett ir
                    [rhs (translate rhs)]
                    [body (translate-body body)])]
      [`(if ,ir ,then ,else)
       `(if ,(translate ir)
            ,(translate-body then)
            ,(translate-body else))]

      [(noop*) ir]

      [_ (translate ir)]))

  (define (handle-for-lang lang-id)
    (findf
     (lambda (h) (equal? lang-id (lang-module-handle-lang-id h)))
     metafun-handles))

  (define (mod-id-for-lang lang)
    (match (handle-for-lang lang)
      [(lang-module-handle _ mod-id) mod-id]
      [#f (error 'translate-metafunction
                 "couldn't find lang handle in handles\n\
  lang: ~a\n\
  handles: ~a" lang metafun-handles)]))

  (match ir
    [(module-var* x _)
     #:when (equal? x current-mod)
     (error 'translate-metafunction
            "internal: got a metafunction module that referred to itself\n\
  module: ~a" current-mod)]

    [(or (lexical-var* _) (module-var* _ _) (? string? _) (? exact-integer? _) (? flonum? _) (? boolean? _))
     ir]

    [`(if ,e1 ,e2 ,e3)
     `(if ,(translate e1) ,(translate e2) ,(translate e3))]

    [`(not ,ir) `(not ,(translate ir))]
    [`(and ,@irs) `(and ,@(map translate irs))]
    [`(or ,@irs) `(or ,@(map translate irs))]

    [`(mf-apply (lang ,lang) ,name ,ir)
     (define mod-id (mod-id-for-lang lang))
     `(call
       ,(if (equal? current-mod mod-id)
            (lexical-var* name)
            (module-var* mod-id name))
       ,(translate ir))]

    [(proc* _ body)
     (struct-copy proc ir
                  [body (translate-body body)])]

    [`(call ,var ,@irs)
     `(call ,var ,@(map translate irs))]))

(define (test-module lang-id tests other-handles)
  (define mod-id (format-symbol "~a-test" lang-id))
  (values
   (lang-module-handle lang-id mod-id)
   `(module ,mod-id
      (require ,@(map require-for-handle
                      (append (list core-handle) other-handles)))
      (provide)

      ,@(for/list ([t '(() 5 x (x y) (let ([x 0] [y 1]) (+ x y)) #f #t "hello" 0.1)])
          (define test-message (format "smoke test ~a" t))
          (define cond
            `(call
              ,(modvar-for-handle core-handle 'from-json-string)
              ,(jsexpr->string (term-to-json t))))
          (define ir
            (proc* '() `(if ,cond
                            ,(pass-test*)
                            ,(fail-test* test-message (none*)))))
          (annotate-test-exceptions (test* ir)))

      ,@(for/list ([ir tests])
          (annotate-test-exceptions (test* ir))))))


(define (evaluator-handle lang-id)
  (define mod-id (format-symbol "~a-evaluator" lang-id))
  (lang-module-handle lang-id mod-id))
(define (evaluator-module lang-id evaluators transitions
                          other-handles)

  (define handle (evaluator-handle lang-id))
  (values
   handle
   `(module ,(mod-id-for-handle handle)
      (require ,@(map require-for-handle (cons core-handle other-handles))
               ,(py-from* '(rpython rlib) '(jit)))
      (provide)

      ,@(for/list ([t transitions])
          (match-define (transition name ir) t)
          (define:* name ir))

      ,@(apply
         append
         (for/list ([e evaluators])
           (match-define (evaluator:rep name tname load unload control-string) e)
           (define (e-name suffix) (format-symbol "~a-~a" name suffix))
           (define evaluator
             (evaluator* name
                         (lexical-var* tname)
                         (lexical-var* (e-name 'load))
                         (lexical-var* (e-name 'unload))
                         (lexical-var* (e-name 'control-string))))

           (list
            (define:* (e-name 'load)
              (match load
                [(clause init? t ws)
                 (compile-clause lang-id init? t ws)]))

            (define:* (e-name 'unload)
              (match unload
                [(clause final? result ws)
                 (maybe-unload lang-id final? result ws)]))

            (define:* (e-name 'control-string)
              (match control-string
                [(clause control-string? t ws)
                 (control-string-projection lang-id control-string? t ws)]))

            (annotate
             (annotate
              evaluator
              'rpython-jit-prefix 'jit)
             'jam-done-exn (modvar-for-handle core-handle 'JamDone))))))))

(define (control-string-projection lang-name control-string? t ws)
  (compile-clause
   lang-name
   control-string?
   t
   ws
   #:no-match (none*)))

(define (maybe-unload lang-name final? result ws)
  (compile-clause
   lang-name
   final?
   result
   ws
   #:with-match done*
   #:no-match (noop*)))

;; compile-test : symbol template pattern string #:equal? bool -> ir
(define (compile-test lang-id check expect message #:equal? equal?)
  (define bv (gensym 'check))

  (define-values (guard-succeeds guard-fails)
    (if equal?
        (values (pass-test*) (fail-test* message (lexical-var* bv)))

        ;; In the not-equal? case, I don't think we need to print out
        ;; the value that the check evaluated too when reporting a
        ;; failure---it's the same as the expect.
        (values (fail-test* message (none*)) (pass-test*))))

  (proc* '() (lett* bv
                    (compile/transcribe check (hash))
                    `(if ,(compile/guard expect lang-id (lexical-var* bv))
                         ,guard-succeeds
                         ,guard-fails))))

(define (link-prims-to-core mods)
  (define (link-toplevel t)
    (match t
      [(define:* _ (or `(prim-class ,name)
                       `(prim-procedure ,name)))
       (struct-copy define: t
                    [rhs (modvar-for-handle core-handle name)])]

      [_ t]))

  (define (link-mod m)
    (match m
      [`(module ,name ,requires ,provides ,@ts)
       `(module ,name ,requires ,provides ,@(map link-toplevel ts))]))

  (map link-mod mods))

;; mod cir -> mod pfcir
(define (lift-procs mod)
  (define (deproc-toplevel t)
    (match t
      [(or (define:* _ `(prim-class ,_))
           (define:* _ `(prim-procedure ,_)))
       (values t '())]

      [(define:* _ (and p (proc* formals body)))
       (define-values (body* procs) (deproc-body body))

       (values
        (struct-copy define: t
                     [rhs (struct-copy proc p [body body*])])
        procs)]

      [(define:* _ ir)
       (define-values (ir* procs) (deproc-ir ir))
       (values
        (struct-copy define: t
                     [rhs ir*])
        procs)]

      [(test* ir)
       (define-values (ir* procs) (deproc-ir ir))
       (values (struct-copy test t [ir ir*]) procs)]

      [(evaluator* _ transition load unload control-string)
       (deproc-irs (list transition load unload control-string)
                   (lambda (tr* lo* un* cs*)
                     (struct-copy evaluator t
                                  [transition tr*]
                                  [load lo*]
                                  [unload un*]
                                  [control-string cs*])))]

      ;; XXX this one causes some problems: because a proc in ir might
      ;; be evalated, we have to make sure that all of the proc
      ;; definitions are placed before (i.e. evaluated before) the
      ;; resulting ir
      [ir (deproc-ir ir)]))

  (define (deproc-irs irs remake-ir)
    (for/fold ([irs '()]
               [procs '()]
               #:result
               (values (apply remake-ir (reverse irs))
                       (reverse procs)))
              ([ir irs])
      (define-values (ir* procs*) (deproc-ir ir))

      (values (cons ir* irs) (append procs* procs))))

  (define (deproc-body ir)
    (match ir
      [(lett* name (and p (proc* _ procbody)) body)

       (define-values (procbody* procbody-procs) (deproc-body procbody))
       (define-values (body* body-procs) (deproc-body body))

       (values
        body*
        (cons (annotate (struct-copy proc p [body procbody*])
                        'lifted-name name)
         (append procbody-procs body-procs)))]

      [(lett* name rhs body)
       (define-values (rhs* rhs-procs)
         (match rhs
           [(proc* _ body)
            (define-values (body* body-procs) (deproc-body body))

            (values
             (struct-copy proc rhs
                          [body body*])
             body-procs)]
           [_ (deproc-ir rhs)]))

       (define-values (body* body-procs) (deproc-body body))
       (values
        (struct-copy lett ir
                     [rhs rhs*]
                     [body body*])
        (append rhs-procs body-procs))]

      [`(if ,ir ,then ,else)
       (define-values (ir* ir-procs) (deproc-ir ir))
       (define-values (then* then-procs) (deproc-body then))
       (define-values (else* else-procs) (deproc-body else))

       (values
        `(if ,ir* ,then* ,else*)
        (append ir-procs then-procs else-procs))]

      [(noop*)
       (values ir '())]

      [ir (deproc-ir ir)]))

  (define (deproc-ir ir)
    (match ir
      [(or (lexical-var* _) (module-var* _ _) (? string? _) (? exact-integer? _) (? flonum? _) (? boolean? _))
       (values ir '())]

      [`(if ,ir0 ,ir1 ,ir2)
       (deproc-irs
        (list ir0 ir1 ir2)
        (lambda (ir0* ir1* ir2*) `(if ,ir0* ,ir1* ,ir2*)))]

      [`(not ,ir)
       (define-values (ir* procs) (deproc-ir ir))
       (values `(not ,ir*) procs)]

      [`(and ,@irs)
       (deproc-irs
        irs
        (lambda irs* `(and ,@irs*)))]

      [`(or ,@irs)
       (deproc-irs
        irs
        (lambda irs* `(or ,@irs*)))]

      [(proc* _ body)
       (define this-name (gensym 'proc))
       (define-values (body* procs) (deproc-body body))
       (values
        ;; XXX really need to nail down the meaning of lexical vars
        ;; and module vars---should I be generating a module var for
        ;; the current module here, since we know this proc is going
        ;; to be lifted out to a top-level definition? or do we just
        ;; generate a lexical var and, since we know that it's from
        ;; generate-temporary, that it won't be captured?
        (lexical-var* this-name)

        (cons (annotate (struct-copy proc ir [body body*])
                        'lifted-name this-name)
              procs))]

      [`(call ,var ,@irs)
       (deproc-irs
        irs
        (lambda irs* `(call ,var ,@irs*)))]))

  (match mod
    [`(module ,name ,requires ,provides ,@toplevels)
     `(module ,name ,requires ,provides
              ,@(for/fold ([deprocd '()]
                           #:result
                           (reverse deprocd))
                          ([t toplevels])
                  (define-values (t* procs) (deproc-toplevel t))
                  (cons
                   t*
                   (append
                    (for/list ([proc procs])
                      (define:* (get-annotation proc 'lifted-name) proc))
                    deprocd))))]))

;; translate-modules : #:grammar (listof module-handle)
;;                     #:metafun (listof module-handle)
;;                     (listof module) -> (listof module)

;; (translate-modules #:grammar ghs #:metafun mhs mods)
;; translates all ir in mods to core-ir; translates prims into the
;; proper modvar reference. Annotates all module-var that refer to a
;; prim-class or prim-procedure with 'py-name and the corresponding
;; Python-level name.
(define (translate-modules #:grammar grammar-handles
                           #:metafun metafun-handles
                           modules)

  (define (translate-ir current-mod ir)
    (translate-metafunction
     metafun-handles current-mod
     (translate-grammar
      grammar-handles current-mod
      (translate-runtime ir))))

  (define ((mk/translate-toplevel current-mod) t)
    (define (translate ir-or-prim)
      (match ir-or-prim
        [(or `(prim-class ,_) `(prim-procedure ,_)) ir-or-prim]
        [ir (translate-ir current-mod ir)]))

    (match t
      [(define:* _ rhs)
       (struct-copy define: t
                    [rhs (translate rhs)])]
      [(test* ir)
       (struct-copy test t
                    [ir (translate ir)])]

      [(evaluator* _ transition load unload control-string)
       (struct-copy evaluator t
                    [transition (translate transition)]
                    [load (translate load)]
                    [unload (translate unload)]
                    [control-string (translate control-string)])]

      [_ (translate t)]))

  (define (translate-module m)
    (match m
      [`(module ,name ,requires ,provides ,@toplevels)
       ;; Note: do the optimizations from the MBE paper (and others)
       ;; before lift-procs; the optimizations might eliminate some
       ;; procs entirely, and I think it might be harder to figure out
       ;; which procs are unnecessary after lifting
       (lift-procs
        `(module ,name ,requires ,provides
                 ,@(map (mk/translate-toplevel name) toplevels)))]))

  (link-prims-to-core
   (map translate-module modules)))

(define (pattern-of-ps ps) (foldr pair '() ps))
(define (repeat-pattern p) (repeat p))
