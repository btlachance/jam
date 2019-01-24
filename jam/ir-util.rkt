#lang racket
(require racket/struct-info syntax/transformer (for-template racket/base))
(provide (rename-out [ir-struct-info* ir-struct-info]))

(define (ir-struct-info* constructor-id predicate-id accessor-ids)
  (ir-struct-info
   ;; ugh: make-v-l-t here does produce a set!-transformer but we
   ;; can't directly use that for prop:set!-transformer---it only
   ;; accepts procedures and struct fields containing a procedure
   (set!-transformer-procedure (make-variable-like-transformer constructor-id))
   constructor-id
   predicate-id
   accessor-ids))

(struct ir-struct-info (xform constructor-id predicate-id accessor-ids)
  ;; since we have to produce a procedure anyway (see above) might as
  ;; well use prop:procedure instead of porp:set!-transformer
  #:property prop:procedure (struct-field-index xform)

  #:property prop:struct-info
  (lambda (info)
    (define accessor-ids (ir-struct-info-accessor-ids info))
    (list #f
          (ir-struct-info-constructor-id info)
          (ir-struct-info-predicate-id info)
          (reverse accessor-ids)
          (map (lambda _ #f) accessor-ids)
          #f)))
