#lang racket
(provide pp-python-stmt)

(define current-indent (make-parameter ""))
(define (do-indented proc)
  (parameterize ([current-indent (string-append (current-indent) "  ")])
    (proc)))
(define-syntax-rule (with-indented e ...) (do-indented (lambda () e ...)))
(define (do-parens proc)
  (display "(")
  (proc)
  (display ")"))
(define-syntax-rule (with-parens e ...) (do-parens (lambda () e ...)))

;; a name is one of
;; - symbol
;; - qualified-name

;; a qualified-name is a
;; - (,symbol dot ,@(nelistof symbol))

;; a python-stmt is one of
;; - `(import ,name)
;; - `(from ,name import ,@(nelistof symbol))
;; - `(class ,symbol ,symbol ,@(listof python-stmt))
;; - `(def ,symbol ,(listof symbol) ,@(listof python-stmt))
;; - `(do ,@(listof python-stmt))
;; - '(pass)
;; - `(if ,python-exp ,python-stmt)
;; - `(if ,python-exp ,python-stmt ,python-stmt)
;; - `(return ,python-exp)
;; - `(,python-exp assign ,@(nelistof python-exp))
;; - `(assert ,@(nelistof python-exp))
;; - `(while ,python-exp ,@(nelistof python-stmt))
;; - `(for ,python-exp ,@(nelistof python-stmt))
;; - '(continue)
;; - `(try ,stmt ,@(nelistof handler))
;; - python-exp

;; a handler is one of
;; `(,name ,stmt)
;; `(,name as ,symbol stmt)

;; a python-exp is one of
;; - `(lambda ,(listof symbol) ,python-exp)
;; - `(list ,@(listof python-exp)
;; - `(tuple ,@(listof python-exp)
;; - `(,unop ,symbol ,python-exp)
;; - `(,python-exp binop ,symbol ,@(nelistof python-exp))
;; - `(app ,python-exp ,@(listof python-exp))
;; - `(,python-exp dot ,@(nelistof symbol))
;; - `(ifx ,python-exp ,python-exp ,python-exp)
;; - `(listcomp ,python-exp for ,python-exp in ,python-exp)
;; - #t
;; - #f
;; - string
;; - symbol
;; - number

;; Note: these definitions aren't meant to make python programs with
;; SyntaxError's unrepresentable e.g. it allows numbers on the lhs of
;; an assignment

(define (format-name nm)
  (match nm
    [(? symbol? s) (symbol->string s)]
    [`(,name dot ,@names) (apply ~a name #:separator "." names)]))

;; pp-python-stmt : python-stmt -> void
;; Displays Python source code to current-output-port
(define (pp-python-stmt stmt)

  ;; Note: every case needs to end by writing a newline; if pretty
  ;; printing a nonempty list of stmts, then, a particular case's
  ;; newline might be written when pretty printing the last member of
  ;; the list
  (match stmt

    [`(import ,name as ,rename)
     (displayln (format "~aimport ~a as ~a"
                        (current-indent)
                        (format-name name)
                        (format-name rename)))]

    [`(import ,@names)
     (when (set-member? names 'as)
       (error 'pp-python-stmt "an import can't use 'as' as one of the names\n\
  names: ~a" names))
     (displayln (format "~aimport ~a"
                        (current-indent)
                        (apply ~a #:separator ", " (map format-name names))))]

    [`(from ,name import ,@names)
     (displayln (format "~afrom ~a import ~a"
                        (current-indent)
                        (format-name name)
                        (apply ~a #:separator ", " (map format-name names))))]

    [`(class ,name ,super
        ,@(list defs ...))

     (displayln (format "~aclass ~a(~a):" (current-indent) name super))
     (with-indented
       (for-each pp-python-stmt defs))]

    [`(def ,name ,(list params ...)
        ,@(list stmts ...))

     (define arg-list (apply ~a #:separator ", " params))
     (displayln (format "~adef ~a(~a):" (current-indent) name arg-list))
     (with-indented
       (for-each pp-python-stmt stmts))]

    [`(do ,s ,@stmts)
     (pp-python-stmt s)
     (for-each pp-python-stmt stmts)]

    [(or `(do) `(pass))
     ;; 'pass would've worked, but '(pass) doesn't overlap w/the form
     ;; of any expressions (the pass stmt can't be used as an expr)
     (displayln (~a (current-indent) "pass"))]

    [`(if ,test ,@(list branches ...))

     (display (~a (current-indent) "if "))
     (pp-python-exp test)
     (displayln ":")
     (match branches
       [(list then)
        (with-indented
          (pp-python-stmt then))]
       [(list then else)
        (with-indented
          (pp-python-stmt then))
        (displayln (~a (current-indent) "else:"))
        (with-indented
          (pp-python-stmt else))])]


    [`(return ,exp)

     (display (~a (current-indent) "return "))
     (pp-python-exp exp)
     (newline)]


    [`(,lhs assign ,@(list rhss ..1))

     (display (current-indent))
     (pp-python-exp lhs)
     (for ([rhs rhss])
       (display " = ")
       (pp-python-exp rhs))
     (newline)]

    [`(assert ,e ,@es)
     (display (current-indent))
     (with-indented
       (display "assert ")
       (pp-python-exp e)
       (for ([e es])
         (display ", ")
         (pp-python-exp e)))
     (newline)]

    [`(while ,e ,@stmts)
     (display (~a (current-indent) "while "))
     (pp-python-exp e)
     (displayln ":")
     (with-indented
       (for-each pp-python-stmt stmts))]

    [`(for ,e ,@stmts)
     (display (~a (current-indent) "for "))
     (pp-python-exp e)
     (displayln ":")
     (with-indented
       (for-each pp-python-stmt stmts))]

    ['(continue)
     (displayln (~a (current-indent) "continue"))]

    [`(try ,body ,@handlers)
     (displayln (~a (current-indent) "try:"))
     (with-indented
       (pp-python-stmt body))
     (for ([handler handlers])
       (match handler
         [`(,e ,rhs)
          (displayln (~a (current-indent) "except " (format-name e) ":"))
          (with-indented
            (pp-python-stmt rhs))]
         [`(,e as ,name ,rhs)
          (displayln (~a (current-indent) "except " (format-name e) " as " name ":"))
          (with-indented
            (pp-python-stmt rhs))]))]

    [_
     (display (current-indent))
     (pp-python-exp stmt)
     (newline)]))

;; XXX Not sure if this is safe but what I have in mind is that an
;; expression is atomic if it can be put in any expression context and
;; still be parsed as the same expression---e.g. ((x dot y) binop and
;; e), which prints as x.y and e, works; but I don't think arbitrary
;; binary operators work. I think I'd need to incorporate the parsing
;; precedence if I wanted to consider operators.
(define (atomic? exp)
  (match exp
    [(? integer? _) #t]
    [(? symbol? _) #t]
    [(? string? _) #t]
    [`(,x dot ,@xs) (and (atomic? x) (andmap atomic? xs))]
    [`(app ,rator . ,_) (atomic? rator)]
    [_ #f]))

(define (pp-python-exp exp)
  (match exp
    [`(lambda ,args ,body)
     (display "lambda")
     (display (string-join (map ~a args) ", "
                           #:before-first " "
                           #:after-last ": "))
     (pp-python-exp body)]

    [`(list ,@(list elements ...))

     (display "[")
     (when (pair? elements)
       (pp-python-exp (car elements))
       (for ([element (cdr elements)])
         (display ", ")
         (pp-python-exp element)))
     (display "]")]

    [`(tuple ,@args)
     (with-parens
       (match args
         ['() (void)]
         [(cons arg0 args)
          (pp-python-exp arg0)
          (if (null? args)
              (display ",")
              (for ([arg args])
                (display ", ")
                (pp-python-exp arg)))]))]

    [`(,lhs binop ,name ,@(list rhss ..1))
     (if (atomic? lhs)
         (pp-python-exp lhs)
         (with-parens (pp-python-exp lhs)))
     (for ([rhs rhss])
       (display (format " ~a " name))
       (if (atomic? rhs)
           (pp-python-exp rhs)
           (with-parens (pp-python-exp rhs))))]

    [`(unop ,name ,arg)
     (display name)
     (display " ")
     (if (atomic? arg)
         (pp-python-exp arg)
         (with-parens (pp-python-exp)))]

    [`(app ,rator ,@(list rands ...))
     (if (atomic? rator)
         (pp-python-exp rator)
         (with-parens (pp-python-exp rator)))
     (with-parens
       (when (pair? rands)
         (pp-python-exp (car rands))
         (for ([rand (cdr rands)])
           (display ", ")
           (pp-python-exp rand))))] 

    [`(,lhs dot ,@(list (? symbol? s) ..1))
     (pp-python-exp lhs)
     (for ([rhs s])
       (display ".")
       (pp-python-exp rhs))]

    [`(ifx ,test ,then ,else)
     (with-parens
       (with-parens (pp-python-exp then))
       (display " if ")
       (with-parens (pp-python-exp test))
       (display " else ")
       (with-parens (pp-python-exp else)))]

    [`(listcomp ,elem for ,vars in ,source)
     (display "[")
     (pp-python-exp elem)
     (display " for ")
     (pp-python-exp vars)
     (display " in ")
     (pp-python-exp source)
     (display "]")]

    [#t (display 'True)]
    [#f (display 'False)]
    [(? string? s) (write s)]
    [(or (? symbol? _)
         (? number? _))
     (display exp)]))

(module+ test
  (require rackunit)
  (define output
    (with-output-to-string
      (lambda ()
        (pp-python-stmt
         '(def f (a b c)
            a
            (class person object
              (def __init__ (self)
                (pass))
              (def name (self i j k)
                (if i j k)
                (return a))
              (def age (self n)
                (return n)))
            (def g (x y)
              (if x
                  (return person))
              (x assign a b)
              ((tuple a b) assign (tuple b a))
              (return y))
            (return b)))
        (pp-python-stmt
         '(do (a assign b c d 0)
              (import itertools)
              (import sys runpy)
              (import itertools as it)
              (from itertools import izip ifilter)
              (for (x binop in (list 1 2 3))
                (x binop + 0)
                (continue))
              (while #f 0)
              (assert True "hello")
              (import exceptions)
              (try 0
                   (Exception 1)
                   ((exceptions dot Exception) as e 2))))
        (for ([exp '((a dot __repr__)
                     (list a b c)
                     (tuple a)
                     (tuple)
                     (app (b dot __add__) c)
                     (tuple a b c)
                     (c binop + a b b)
                     (ifx a b c)
                     (#t binop and #f)
                     (app len "hello")
                     (lambda (x y z) (x binop + y z))
                     (listcomp x for x in (list 1 2 3))
                     (app (lambda (x) x) a))])
          (pp-python-exp exp)
          (newline)))))

  ;; Sorta annoying that testing this module shells out to python, but
  ;; I think it would be more annoying to test any other way.
  (let ([python (find-executable-path "python")])
    (when python
      (check-true
       (system* python "-c" output)))))
