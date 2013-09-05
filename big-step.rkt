#lang racket/base
(require racket/function
         racket/list
         racket/match
         racket/set
         "eval-util.rkt"
         "lang.rkt"
         "value.rkt")

(provide eval)

(define (eval e)
  (define (app σ f vs)
    (match f
      [(closure xs r ρ e)
       (let-values ([(σ ρ) (bind σ ρ xs r vs)])
         (inner σ ρ e))]
      [(chaperone L P f′ neg pos)
       (match-let ([(cons σ (app value->list vs*)) (with-continuation-mark 'chaperone f (app σ neg vs))])
         (if (= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (match-let ([(cons σ (app value->list rs)) (app σ f′ vs*)])
                   (match-let ([(cons σ (app value->list rs*)) (with-continuation-mark 'chaperone f (app σ pos rs))])
                     (if (= (length rs)
                            (length rs*))
                         (if (andmap chaperone-of? rs* rs)
                             (cons σ (list->value rs*))
                             (error 'eval "wrapper must at most chaperone arguments (made ~a into ~a)" rs rs*))
                         (error 'eval "wrapper must return same number of results as arguments given"))))
                 (error 'eval "wrapper must at most chaperone arguments (made ~a into ~a)" vs vs*))
             (error 'eval "wrapper must return same number of results as arguments given")))]
      [(impersonator L P f neg pos)
       (match-let ([(cons σ (app value->list vs*)) (app σ neg vs)])
         (if (= (length vs)
                (length vs*))
             (match-let ([(cons σ (app value->list rs)) (app σ f vs*)])
                   (match-let ([(cons σ (app value->list rs*)) (app σ pos rs)])
                     (if (= (length rs)
                            (length rs*))
                         (cons σ (list->value rs*))
                         (error 'eval "wrapper must return same number of results as arguments given"))))
             (error 'eval "wrapper must return same number of results as arguments given")))]
      [(primitive name f arity)
       (if (arity-includes? arity (length vs))
           (cons σ (native-apply f vs))
           (error 'eval "~a cannot accept arity of ~a" name vs))]))
  
  (define (inner* σ ρ es)
    (if (empty? es)
        (cons σ empty)
        (match-let* ([(cons σ v) (inner σ ρ (first es))]
                     [(cons σ vs) (inner* σ ρ (rest es))])
          (cons σ (cons v vs)))))
  
  (define (inner σ ρ e)
    (match e
      [(app-e _ e es)
       (match-let* ([(cons σ (app single-value! v)) (inner σ ρ e)]
                    [(cons σ (app (λ (vs) (map single-value! vs)) vs)) (inner* σ ρ es)])
         (app σ v vs))]
      [(bool-e _ p)
       (cons σ (single-value p))]
      [(ch-op-e L e0 e1 e2)
       (match-let* ([(cons σ (app single-value! v0)) (inner σ ρ e0)]
                    [(cons σ (app single-value! v1)) (inner σ ρ e1)]
                    [(cons σ (app single-value! v2)) (inner σ ρ e2)])
         (cons σ (single-value
                  (chaperone
                   L
                   (continuation-mark-set-first
                    (current-continuation-marks) 'chaperone #f)
                   v0 v1 v2))))]
      [(if-e _ e0 e1 e2)
       (match-let ([(cons σ (app single-value! v)) (inner σ ρ e0)])
         (inner σ ρ (if v e1 e2)))]
      [(int-e _ i)
       (cons σ (single-value i))]
      [(lam-e _ xs r e)
       (cons σ (single-value (closure xs r ρ e)))]
      [(let-e _ xs r e0 e1)
       (match-let ([(cons σ (app value->list vs)) (inner σ ρ e0)])
         (let-values ([(σ ρ) (bind σ ρ xs r vs)])
           (inner σ ρ e1)))]
      [(letrec-e _ xs r e0 e1)
       (let ([ρ (pre-bind ρ xs r)])
         (match-let ([(cons σ (app value->list vs)) (inner σ ρ e0)])
           (let ([σ (rec-bind σ ρ xs r vs)])
             (inner σ ρ e1))))]
      [(handle-e _ x e0 e1)
       (with-handlers ([ERROR? (λ (e)
                                 (match-let ([(ERROR (cons σ (app single-value! v))) e])
                                   (let-values ([(σ ρ) (bind σ ρ (list x) #f (list v))])
                                     (inner σ ρ e0))))])
         (inner σ ρ e1))]
      [(or-e _ e0 e1)
       (match-let ([(cons σ (app single-value! v)) (inner σ ρ e0)])
         (if v
             (cons σ (single-value v))
             (inner σ ρ e1)))]
      [(raise-e _ e)
       (raise (ERROR (inner σ ρ e)))]
      [(prim-e _ id)
       (cons σ (single-value (id->primitive id)))]
      #;[(prim-e 'chaperone-operator)
       (cons σ (single-value
                (primitive 'chaperone-operator
                           (λ (f w)
                             (if (and (operator? f)
                                      (operator? w))
                                 (if (arity=? (operator-arity f)
                                              (operator-arity w))
                                     (chaperone f w)
                                     (error 'eval "operator and wrapper must have same arity"))
                                 (error 'eval "chaperone-operator must be applied to operators")))
                           2)))]
      #;[(prim-e 'impersonate-operator)
       (cons σ (single-value
                (primitive 'impersonate-operator
                           (λ (f w)
                             (if (and (operator? f)
                                      (operator? w))
                                 (if (arity=? (operator-arity f)
                                              (operator-arity w))
                                     (impersonator f w)
                                     (error 'eval "operator and wrapper must have same arity"))
                                 (error 'eval "impersonate-operator must be applied to operators")))
                           2)))]   
      [(ref-e _ x)
       (if (hash-has-key? ρ x)
           (cons σ (single-value (hash-ref σ (hash-ref ρ x))))
           (error 'eval "unbound variable ~a" x))]))
  (inner (hasheqv) (hasheq) e))


