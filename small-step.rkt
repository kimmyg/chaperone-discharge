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
  (define (app f vs σ)
    (match f
      [(closure (lam-e xs r e) ρ)
       (let-values ([(ρ σ) (bind ρ σ xs r vs)])
         (inner e ρ σ))]
      [(chaperone f w)
       (match-let ([(cons σ (app value->list vs*)) (app w vs σ)])
         (cond
           [(= (length vs)
               (length vs*))
            (if (andmap chaperone-of? vs* vs)
                (app f vs* σ)
                (error 'eval "wrapper must at most chaperone arguments (made ~a into ~a)" vs vs*))]
           [(= (add1 (length vs))
               (length vs*))
            (match-let ([(cons w* vs*) vs*])
              (if (operator? w*)
                  (if (andmap chaperone-of? vs* vs)
                      (match-let* ([(cons σ (app value->list rs*)) (app f vs* σ)]
                                   [(cons σ (app value->list rs)) (app w* rs* σ)])
                        (if (= (length rs*)
                               (length rs))
                            (if (andmap chaperone-of? rs rs*)
                                (cons σ (list->value rs))
                                (error 'eval "results wrapper must at most chaperone arguments"))
                            (error 'eval "results wrapper must produce same number of values as it consumed")))
                      (error 'eval "wrapper must at most chaperone arguments"))
                  (error 'eval "extra result must be operator ~a" w*)))]
           [else
            (error 'eval "wrapper must return same number or one additional result")]))]
      [(impersonator f w)
       (match-let ([(cons σ (app value->list vs*)) (app w vs σ)])
         (cond
           [(= (length vs)
               (length vs*))
            (app f vs* σ)]
           [(= (add1 (length vs))
               (length vs*))
            (match-let ([(cons w* vs*) vs*])
              (if (operator? w*)
                  (match-let* ([(cons σ (app value->list rs*)) (app f vs* σ)]
                               [(cons σ (app value->list rs)) (app w* rs* σ)])
                    (if (= (length rs*)
                           (length rs))
                        (cons σ (list->value rs))
                        (error 'eval "results wrapper must produce same number of values as it consumed")))
                  (error 'eval "extra result must be operator ~a" w*)))]
           [else
            (error 'eval "wrapper must return same number or one additional result")]))]      
      [(prim-e 'chaperone-operator)
       (match vs
         [(list (? operator? f) (? operator? w))
          (if (arity-subsumes? w f)
              (cons σ (single-value (chaperone f w)))
              (error 'eval "arity of wrapper must subsume arity of operator"))]
         [_
          (error 'eval "chaperone-operator requires two operators as arguments: ~a" vs)])]
      [(prim-e 'impersonate-operator)
       (match vs
         [(list (? operator? f) (? operator? w))
          (if (arity-subsumes? w f)
              (cons σ (single-value (impersonator f w)))
              (error 'eval "arity of wrapper must subsume arity of operator"))]
         [_
          (error 'eval "impersonate-operator requires two operators as arguments: ~a" vs)])]
      [(primitive name f arity)
       (if (arity-includes? arity (length vs))
           (cons σ (native-apply f vs))
           (error 'eval "~a cannot accept arity of ~a" name vs))]))
  
  (define (inner* es ρ σ)
    (if (empty? es)
        (cons σ empty)
        (match-let* ([(cons σ v) (inner (first es) ρ σ)]
                     [(cons σ vs) (inner* (rest es) ρ σ)])
          (cons σ (cons v vs)))))
  
  (define (inner e ρ σ)
    (match e
      [(app-e e es)
       (match-let* ([(cons σ (app single-value! v)) (inner e ρ σ)]
                    [(cons σ (app (λ (vs) (map single-value! vs)) vs)) (inner* es ρ σ)])
         (app v vs σ))]
      [(if-e e0 e1 e2)
       (match-let ([(cons σ (app single-value! v)) (inner e0 ρ σ)])
         (inner (if v e1 e2) ρ σ))]
      [(int-e i)
       (cons σ (single-value i))]
      [(bool-e p)
       (cons σ (single-value p))]
      [(lam-e xs r e)
       (cons σ (single-value (closure (lam-e xs r e) ρ)))]
      [(let-e xs r e0 e1)
       (match-let ([(cons σ (app value->list vs)) (inner e0 ρ σ)])
         (let-values ([(ρ σ) (bind ρ σ xs r vs)])
           (inner e1 ρ σ)))]
      [(letrec-e xs r e0 e1)
       (let ([ρ (pre-bind ρ xs r)])
         (match-let ([(cons σ (app value->list vs)) (inner e0 ρ σ)])
           (let ([σ (rec-bind ρ σ xs r vs)])
             (inner e1 ρ σ))))]
      [(handle-e x e0 e1)
       (with-handlers ([ERROR? (λ (e)
                                 (match-let ([(ERROR (cons σ (app single-value! v))) e])
                                   (let-values ([(ρ σ) (bind ρ σ (list x) #f (list v))])
                                     (inner e0 ρ σ))))])
         (inner e1 ρ σ))]
      [(or-e e0 e1)
       (match-let ([(cons σ (app single-value! v)) (inner e0 ρ σ)])
         (if v
             (cons σ (single-value v))
             (inner e1 ρ σ)))]
      [(raise-e e)
       (raise (ERROR (inner e ρ σ)))]
      [(prim-e '=)
       (cons σ (single-value (primitive '= = 2)))]
      [(prim-e '<)
       (cons σ (single-value (primitive '< < 2)))]
      [(prim-e '*)
       (cons σ (single-value (primitive '* * 2)))]
      [(prim-e '+)
       (cons σ (single-value (primitive '+ + 2)))]
      [(prim-e '-)
       (cons σ (single-value (primitive '- - 2)))]
      [(prim-e 'chaperone-operator)
       (cons σ (single-value
                (primitive 'chaperone-operator
                           (λ (f w)
                             (if (and (operator? f)
                                      (operator? w))
                                 (if (arity-subsumes? w f)
                                     (chaperone f w)
                                     (error 'eval "arity of wrapper must subsume arity of operator"))
                                 (error 'eval "chaperone-operator must be applied to operators")))
                           2)))]
      [(prim-e 'impersonate-operator)
       (cons σ (single-value
                (primitive 'impersonate-operator
                           (λ (f w)
                             (if (and (operator? f)
                                      (operator? w))
                                 (if (arity-subsumes? w f)
                                     (impersonator f w)
                                     (error 'eval "arity of wrapper must subsume arity of operator"))
                                 (error 'eval "impersonate-operator must be applied to operators")))
                           2)))]
      [(prim-e 'integer?)
       (cons σ (single-value (primitive 'integer? integer? 1)))]
      [(prim-e 'not)
       (cons σ (single-value (primitive 'not not 1)))]
      [(prim-e 'values)
       (cons σ (single-value (primitive 'values values (arity-at-least 0))))]
      [(ref-e x)
       (if (hash-has-key? ρ x)
           (cons σ (single-value (hash-ref σ (hash-ref ρ x))))
           (error 'eval "unbound variable ~a" x))]))
  (inner e (hasheq) (hasheqv)))



