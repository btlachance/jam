#lang racket
(define-values (odd? even?)
  (values (lambda (n) (if (zero? n) #f (even? (- n 1))))
          (lambda (n) (if (zero? n) #t (odd? (- n 1))))))
(define-values () (values))
(odd? 0)
(even? 0)
(odd? 1)
(even? 2)

values
(apply values 1 2 (cons 3 null))

(let-values ([(y z) (values 2 3)]
             [() (values)]
             [(x) 1])
  (- x (+ y z)))

(letrec-values ([(even? odd?)
                 (values
                  (lambda (n)
                    (if (zero? n)
                        #t
                        (odd? (- n 1))))
                  (lambda (n)
                    (if (zero? n)
                        #f
                        (even? (- n 1)))))])
  (even? 10))

(let ()
  (values 1 2 3)
  (values)
  4)

(let-values ([(vs cpu real gc) (time-apply + (list 1 2))])
  cpu)
