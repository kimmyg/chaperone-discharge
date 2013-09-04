#lang racket/base
(require racket/list
         racket/match
         racket/set
         "lang.rkt")

(provide parse
         unparse)

(define primitives (apply seteq '(values not null null? cons pair? car cdr raise + - * < > = integer? boolean?)))

(define fresh-label
  (let ([i 0])
    (λ ()
      (begin0
        (string->symbol (format "l~a" i))
        (set! i (add1 i))))))

(define (pspec? ps)
  (or (null? ps)
      (and (pair? ps)
           (and (symbol? (car ps))
                (pspec? (cdr ps))))
      (symbol? ps)))

(define (pspec-posi ps)
  (if (or (null? ps)
          (symbol? ps))
     null
     (cons (car ps) (pspec-posi (cdr ps)))))

(define (pspec-rest ps)
  (and (not (null? ps))
       (if (pair? ps)
          (pspec-rest (cdr ps))
          ps)))

(define (ρ-extend xs r ρ)
  (let* ([ρ (for/fold ([ρ ρ])
              ([x (in-list xs)])
              (set-add ρ x))]
         [ρ (if r (set-add ρ r) ρ)])
    ρ))

(define (parse e)
  (define (inner e ρ)
    (if (list? e)
        (if (empty? e)
            (error "empty application expression")
            (if (set-member? ρ (first e))
                (app-e (fresh-label)
                       (inner (first e) ρ)
                       (map (λ (e) (inner e ρ)) (rest e)))
                (match e
                  [`(λ ,ps ,e)
                   (if (pspec? ps)
                       (let ([xs (pspec-posi ps)]
                             [r (pspec-rest ps)])
                         (lam-e (fresh-label) xs r (inner e (ρ-extend xs r ρ))))
                       (error 'parse "bad parameter specification: ~a" ps))]
                  [`(let ([,ps ,e0]) ,e1)
                   (if (pspec? ps)
                       (let ([xs (pspec-posi ps)]
                             [r (pspec-rest ps)])
                         (let-e (fresh-label) xs r
                                (inner e0 ρ)
                                (inner e1 (ρ-extend xs r ρ))))
                       (error 'parse "bad parameter specification: ~a" ps))]
                  [`(letrec ([,ps ,e0]) ,e1)
                   (if(pspec? ps)
                      (let ([xs (pspec-posi ps)]
                            [r (pspec-rest ps)])
                        (letrec-e (fresh-label) xs r
                                  (inner e0 (ρ-extend xs r ρ))
                                  (inner e1 (ρ-extend xs r ρ))))
                      (error 'parse "bad parameter specification: ~a" ps))]
                  [`(if ,e0 ,e1 ,e2)
                   (if-e (fresh-label) 
                         (inner e0 ρ)
                         (inner e1 ρ)
                         (inner e2 ρ))]
                  [`(handle ([,(? symbol? x) ,e0]) ,e1)
                   (handle-e (fresh-label) x (inner e0 (set-add ρ x)) (inner e1 ρ))]
                  [`(raise ,e)
                   (raise-e (fresh-label) 
                            (inner e ρ))]
                  [`(and ,e0 ,e1)
                   (and-e (fresh-label) 
                          (inner e0 ρ)
                          (inner e1 ρ))]
                  [`(or ,e0 ,e1)
                   (or-e (fresh-label) 
                         (inner e0 ρ)
                         (inner e1 ρ))]
                  [`(apply ,e0 ,e1)
                   (app-values-e (fresh-label)
                                 (inner e0 ρ)
                                 (inner e1 ρ))]
                  [`(chaperone-operator ,e0 ,e1 ,e2)
                   (ch-op-e (fresh-label)
                            (inner e0 ρ)
                            (inner e1 ρ)
                            (inner e2 ρ))]
                  [`(impersonate-operator ,e0 ,e1 ,e2)
                   (im-op-e (fresh-label)
                            (inner e0 ρ)
                            (inner e1 ρ)
                            (inner e2 ρ))]
                  [`(,e0 . ,es)
                   (app-e (fresh-label)
                          (inner e0 ρ)
                          (map (λ (e) (inner e ρ)) es))])))
        (cond
          [(boolean? e)
           (bool-e (fresh-label) e)]
          [(integer? e)
           (int-e (fresh-label) e)]
          [(symbol? e)
           (if (set-member? primitives e)
               (prim-e (fresh-label) e)
               (ref-e (fresh-label) e))]
          [else
           (error 'parse "unhandled non-list entity: ~a" e)])))
  (inner e (seteq)))

(define unparse
  (match-lambda
    [(app-e L e0 es)
     `(,(unparse e0) . ,(map unparse es))]
    [(bool-e L p)
     p]
    [(ch-op-e L e0 e1 e2)
     `(chaperone-operator ,(unparse e0)
                          ,(unparse e1)
                          ,(unparse e2))]
    [(if-e L e0 e1 e2)
     `(if ,(unparse e0)
          ,(unparse e1)
          ,(unparse e2))]
    [(int-e L i)
     i]
    [(lam-e L xs r e0)
     `(λ ,(foldr cons (or r null) xs) ,(unparse e0))]
    [(let-e L xs r e0 e1)
     `(let ([,(foldr cons (or r null) xs) ,(unparse e0)])
        ,(unparse e1))]
    [(letrec-e L xs r e0 e1)
     `(letrec ([,(foldr cons (or r null) xs) ,(unparse e0)])
        ,(unparse e1))]
    [(or-e L e0 e1)
     `(or ,(unparse e0)
          ,(unparse e1))]
    [(prim-e L id)
     id]
    [(raise-e L e0)
     `(raise ,(unparse e0))]
    [(ref-e L x)
     x]))