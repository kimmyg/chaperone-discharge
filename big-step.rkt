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
       (match-let ([(cons σ (app value->list vs*)) (with-handlers ([λC:error? (λ (_) (raise (λC:blame- L)))])
                                                     (with-continuation-mark 'chaperone-parent-label (cons '- L)
                                                       (app σ neg vs)))])
         (if (= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (match-let ([(cons σ (app value->list rs)) (app σ f′ vs*)])
                   (if (arity-includes? (operator-arity pos) (length rs))
                       (match-let ([(cons σ (app value->list rs*)) (with-handlers ([λC:error? (λ (_) (raise (λC:blame+ L)))])
                                                                     (with-continuation-mark 'chaperone-parent-label (cons '+ L)
                                                                       (app σ pos rs)))])
                         (if (= (length rs)
                                (length rs*))
                             (if (andmap chaperone-of? rs* rs)
                                 (cons σ (list->value rs*))
                                 (raise (λC:blame+ L))) ; positive guard must at most chaperone arguments
                             (raise (λC:blame+ L)))); positive guard must return same number of results as arguments given
                       (raise (λC:blame L)))) ; positive guard must accept number of results
                 (raise (λC:blame- L))) ; negative guard must at most chaperone arguments
             (raise (λC:blame- L))))] ; negative guard must return same number of results as arguments given
      [(impersonator L P f neg pos)
       (match-let ([(cons σ (app value->list vs*)) (app σ neg vs)])
         (if (= (length vs)
                (length vs*))
             (match-let ([(cons σ (app value->list rs)) (app σ f vs*)])
               (if (arity-includes? (operator-arity pos (length rs)))
                   (match-let ([(cons σ (app value->list rs*)) (app σ pos rs)])
                     (if (= (length rs)
                            (length rs*))
                         (cons σ (list->value rs*))
                         (raise (λC:blame+ L)))) ; positive guard must return same number of results as arguments given
                   (raise (λC:blame L)))) ; positive guard must accept number of results
             (raise (λC:blame- L))))] ; negative guard must return same number of results as arguments given
      [(primitive name f arity)
       (if (arity-includes? arity (length vs))
           (cons σ (native-apply f vs))
           (raise (λC:error)))])) ; wrong arity
  
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
                    (current-continuation-marks) 'chaperone-parent-label #f)
                   v0 v1 v2))))]
      [(if-e _ e0 e1 e2)
       (match-let ([(cons σ (app single-value! v)) (inner σ ρ e0)])
         (inner σ ρ (if v e1 e2)))]
      [(int-e _ i)
       (cons σ (single-value i))]
      [(lam-e _ xs r e0)
       (cons σ (single-value (closure xs r (restrict ρ (free-variables e)) e0)))]
      [(let-e _ xs r e0 e1)
       (match-let ([(cons σ (app value->list vs)) (inner σ ρ e0)])
         (let-values ([(σ ρ) (bind σ ρ xs r vs)])
           (inner σ ρ e1)))]
      [(letrec-e _ xs r e0 e1)
       (let ([ρ (pre-bind ρ xs r)])
         (match-let ([(cons σ (app value->list vs)) (inner σ ρ e0)])
           (let ([σ (rec-bind σ ρ xs r vs)])
             (inner σ ρ e1))))]
      [(handle-e _ e0 e1)
       (with-handlers ([λC:error? (λ (_) (inner σ ρ e1))])
         (inner σ ρ e0))]
      [(or-e _ e0 e1)
       (match-let ([(cons σ (app single-value! v)) (inner σ ρ e0)])
         (if v
             (cons σ (single-value v))
             (inner σ ρ e1)))]
      [(prim-e _ id)
       (cons σ (single-value (id->primitive id)))]
      [(ref-e _ x)
       (if (hash-has-key? ρ x)
           (cons σ (single-value (hash-ref σ (hash-ref ρ x))))
           (raise (λC:error)))])) ; unbound variable
  (with-handlers ([λC:error? values]
                  [λC:blame? values])
    (inner (hasheqv) (hasheq) e)))


