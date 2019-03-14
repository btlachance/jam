#lang racket
(provide
 (struct-out nonterminal)
 (struct-out nt:plain)
 (struct-out nt:environment)

 (struct-out metafunction)
 (struct-out mf:plain)
 (struct-out mf:data)
 (struct-out mf:call-evaluator)

 (struct-out transition)
 (struct-out evaluator:rep))

;; a nonterminal is a (nonterminal (listof symbol) nt:rep)
(struct nonterminal (names rep) #:transparent)

;; a nt:rep is one of
;; - (nt:plain (listof pattern))
;; - (nt:environment pattern pattern)
(struct nt:plain (rhss) #:transparent)
(struct nt:environment (pred-py-name key-pattern value-pattern) #:transparent)

;; a metafunction is a (metafunction symbol mf:rep)
;; a mf:rep is one of
;; - (mf:plain symbol ir)
;; - (mf:data symbol pattern)
;; - (mf:call-evaluator symbol)
(struct metafunction (name code) #:transparent)
(struct mf:plain (ir) #:transparent)
(struct mf:data (py-name args) #:transparent)
(struct mf:call-evaluator (name) #:transparent)

;; a transition is a (transition symbol ir)
(struct transition (name ir) #:transparent)

;; an evaluator:rep is a (evaluator:rep symbol symbol clause clause clause)
(struct evaluator:rep (name transition-name load unload control-string)
  #:transparent)