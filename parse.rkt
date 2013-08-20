#lang racket/base
(require racket/list
         racket/match
         racket/set
         "lang.rkt")

(provide parse)

(define primitives (apply seteq '(values not null null? cons pair? car cdr raise + - * < > = integer? boolean? chaperone-operator impersonate-operator)))

(define (pspec? ps)
  (if (list? ps)
      (or (empty? ps)
          (and (symbol? (first ps))
               (pspec? (rest ps))))
      (symbol? ps)))

(define (pspec-posi ps)
  (if (and (list? ps)
           (not (empty? ps)))
      (cons (first ps) (pspec-posi (rest ps)))
      empty))

(define (pspec-rest ps)
  (if (list? ps)
      (and (not (empty? ps))
           (pspec-rest (rest ps)))
      ps))

(define (ρ-extend xs r ρ)
  (let* ([ρ (for/fold ([ρ ρ])
              ([x (in-list xs)])
              (set-add ρ x))]
         [ρ (if r (set-add ρ r) ρ)])
    ρ))

(define (parse e)
  (define (inner e ρ)
    (match e
      [(? symbol? x)
       (if (set-member? primitives x)
           (prim-e x)
           (ref-e x))]
      [(? integer? n)
       (int-e n)]
      [(? boolean? p)
       (bool-e p)]
      [`(λ ,ps ,e)
       (cond
         [(set-member? ρ 'λ)
          (app-e (parse 'λ)
                 (list (inner ps ρ)
                       (inner e ρ)))]
         [(pspec? ps)
          (let ([xs (pspec-posi ps)]
                [r (pspec-rest ps)])
            (lam-e xs r (inner e (ρ-extend xs r ρ))))]
         [else
          (error 'parse "bad parameter specification: ~a" ps)])]
      [`(let ([,ps ,e0]) ,e1)
       (cond
         [(set-member? ρ 'let)
          (app-e (inner 'let ρ)
                 (list (app-e (app-e (inner ps ρ)
                                     (inner e0 ρ))
                              (list))
                       (inner e1 ρ)))]
         [(pspec? ps)
          (let ([xs (pspec-posi ps)]
                [r (pspec-rest ps)])
            (let-e xs r
                   (inner e0 ρ)
                   (inner e1 (ρ-extend xs r ρ))))]
         [else
          (error 'parse "bad parameter specification: ~a" ps)])]
      [`(letrec ([,ps ,e0]) ,e1)
       (cond
         [(set-member? ρ 'letrec)
          (app-e (inner 'letrec ρ)
                 (list (app-e (app-e (inner ps ρ)
                                     (list (inner e0 ρ)))
                              (list))
                       (inner e1 ρ)))]
         [(pspec? ps)
          (let ([xs (pspec-posi ps)]
                [r (pspec-rest ps)])
            (letrec-e xs r
                      (inner e0 (ρ-extend xs r ρ))
                      (inner e1 (ρ-extend xs r ρ))))]
         [else
          (error 'parse "bad parameter specification: ~a" ps)])]
      [`(if ,e0 ,e1 ,e2)
       (cond
         [(set-member? ρ 'if)
          (app-e (inner 'if ρ)
                 (list (inner e0 ρ)
                       (inner e1 ρ)
                       (inner e2 ρ)))]
         [else
          (if-e (inner e0 ρ)
                (inner e1 ρ)
                (inner e2 ρ))])]
      [`(handle ([,(? symbol? x) ,e0])
                ,e1)
       (if (set-member? ρ 'handle)
           (app-e (inner 'handle ρ)
                  (list (app-e (app-e (inner x ρ)
                                      (list (inner e0 ρ)))
                               (list))
                        (inner e1 ρ)))
           (handle-e x (inner e0 (set-add ρ x)) (inner e1 ρ)))]
      [`(raise ,e)
       (if (set-member? ρ 'raise)
           (app-e (inner 'raise ρ)
                  (list (inner e ρ)))
           (raise-e (inner e ρ)))]
      [`(and ,e0 ,e1)
       (cond
         [(set-member? ρ 'and)
          (app-e (inner 'and ρ)
                 (list (inner e0 ρ)
                       (inner e1 ρ)))]
         [else
          (and-e (inner e0 ρ)
                 (inner e1 ρ))])]
      [`(or ,e0 ,e1)
       (cond
         [(set-member? ρ 'or)
          (app-e (inner 'or ρ)
                 (list (inner e0 ρ)
                       (inner e1 ρ)))]
         [else
          (or-e (inner e0 ρ)
                (inner e1 ρ))])]
      [`(apply ,e0 ,e1)
       (cond
         [(set-member? ρ 'apply)
          (app-e (inner 'apply ρ)
                 (list (inner e0 ρ)
                       (inner e1 ρ)))]
         [else
          (app-values-e (inner e0 ρ)
                        (inner e1 ρ))])]
      [`(,e0 . ,es)
       (app-e (inner e0 ρ)
              (map (λ (e) (inner e ρ)) es))]))
  (inner e (seteq)))