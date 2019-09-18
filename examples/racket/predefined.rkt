#lang racket
(define (newline) (write-string "\n"))

(define (cddr xs) (cdr (cdr xs)))
(define (cdar xs) (cdr (car xs)))
(define (cadr xs) (car (cdr xs)))
(define (caar xs) (car (car xs)))
(define (cdddr xs) (cdr (cddr xs)))
(define (cddar xs) (cdr (cdar xs)))
(define (cdadr xs) (cdr (cadr xs)))
(define (cdaar xs) (cdr (caar xs)))
(define (caddr xs) (car (cddr xs)))
(define (cadar xs) (car (cdar xs)))
(define (caadr xs) (car (cadr xs)))
(define (caaar xs) (car (caar xs)))

(define (<= v1 v2) (or (< v1 v2) (= v1 v2)))
(define (> v1 v2) (not (<= v1 v2)))
(define (>= v1 v2) (<= v2 v1))

(define (positive? n)
  (> n (if (exact-integer? n)
           0
           0.0)))
(define (negative? n)
  (< n (if (exact-integer? n)
           0
           0.0)))
(define (abs n)
  (if (positive? n)
      n
      (* n (if (exact-integer? n)
               -1
               -1.0))))

(define (length xs)
  (let loop ([xs xs]
             [n 0])
    (if (null? xs)
        n
        (loop (cdr xs) (+ n 1)))))

(define (reverse xs)
  (let loop ([xs xs]
             [rev null])
    (if (null? xs)
        rev
        (loop (cdr xs) (cons (car xs) rev)))))

(define (build-list n proc)
  (let loop ([i 0]
             [vs null])
    (if (= i n)
        (reverse vs)
        (loop (+ i 1) (cons (proc i) vs)))))

(define (list->vector xs) (apply vector xs))

(define (make-vector size . rest)
  (if (null? rest)
      (make-vector size 0)
      (if (null? (cdr rest))
          (let ([v (car rest)])
            (apply vector (build-list size (lambda (_) v))))
          (raise))))

(define (equal? v1 v2)
  (if (and (number? v1) (number? v2))
      (= v1 v2)
      (if (and (boolean? v1) (boolean? v2))
          (or (and v1 v2) (and (not v1) (not v2)))
          (if (and (string? v1) (string? v2))
              (string=? v1 v2)
              (if (and (null? v1) (null? v2))
                  #t
                  (if (and (symbol? v1) (symbol? v2))
                      (symbol=? v1 v2)
                      (if (and (pair? v1) (pair? v2))
                          (and (equal? (car v1) (car v2))
                               (equal? (cdr v1) (cdr v2)))
                          (if (and (vector? v1) (vector? v2))
                              (and (= (vector-length v1) (vector-length v2))
                                   (letrec ([n (vector-length v1)]
                                            [loop (lambda (i)
                                                    (or (= i n)
                                                        (and (equal? (vector-ref v1 i)
                                                                     (vector-ref v2 i))
                                                             (loop (+ i 1)))))])
                                     (loop 0)))
                              ;; XXX need ports
                              (raise)))))))))

(define (time-apply f vs)
  (let ([then (current-inexact-milliseconds)]
        [results (call-with-values (lambda () (apply f vs)) list)]
        [now (current-inexact-milliseconds)])
    (define delta (inexact->exact (- now then)))
    (values results delta delta 0)))

(define (write v)
  (if (string? v)
      (write-string v)
      (if (number? v)
          (write (number->string v))
          (if (boolean? v)
              (if v (write "#t") (write "#f"))
              (if (symbol? v)
                  (write (symbol->string v))
                  (raise))))))

(define (display v)
  (if (string? v)
      (write v)
      (raise)))

(define (fprintf out format . vs)
  ;; XXX This is the format-string for time in the pycket/wrap language
  (if (equal? format "RESULT-cpu: ~a.0\nRESULT-gc: ~a.0\nRESULT-total: ~a.0\n")
      (begin
        (write "RESULT-cpu: ")
        (write (car vs))
        (write ".0\n")
        (write "RESULT-gc: ")
        (write (car (cdr vs)))
        (write ".0\n")
        (write "RESULT-total: ")
        (write (car (cdr (cdr vs))))
        (write ".0\n"))
      (raise)))
