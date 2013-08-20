#lang racket/base
(require racket/match)

(provide (struct-out value)
         (struct-out single-value)
         (struct-out multiple-values)
         value->list
         list->value
         single-value!)

(struct value () #:transparent)
(struct single-value value (v) #:transparent)
(struct multiple-values value (vs) #:transparent)

(define value->list
  (match-lambda
    [(single-value v)
     (list v)]
    [(multiple-values vs)
     vs]))

(define list->value
  (match-lambda
    [(list v)
     (single-value v)]
    [vs
     (multiple-values vs)]))

(define single-value!
  (match-lambda
    [(single-value v)
     v]
    [(multiple-values vs)
     (error 'single-value! "values ~a" vs)]))