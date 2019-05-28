#lang racket
(define (filter p? xs)
  (if (null? xs)
      null
      (if (p? (car xs))
          (cons (car xs)
                (filter p? (cdr xs)))
          (filter p? (cdr xs)))))
(filter null? null)
(filter null? (cons null (cons 1 (cons null (cons 2 null)))))
(filter pair? (cons 1 (cons (cons 2 3) (cons 4 (cons (cons 5 6) null)))))
(filter pair? (list 1 (cons 2 3) 4 (cons 5 6)))

(define (map f xs)
  (if (null? xs)
      null
      (cons (f (car xs)) (map f (cdr xs)))))
(define (list1 x) (cons x null))
(map list1 null)
(map list1 (cons #t (cons #f (cons 4 null))))
(map list1 (list #t #f 4))

(list 'a 'b (symbol? 'c))
