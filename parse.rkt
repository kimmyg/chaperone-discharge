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
        (string->symbol (format "L~a" i))
        (set! i (add1 i))))))

(define (ρ-extend xs ρ)
  (for/fold ([ρ ρ])
    ([x (in-list xs)])
    (set-add ρ x)))

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
                  [`(λ ,xs ,e)
                   (if (andmap symbol? xs)
                       (lam-e (fresh-label) xs (inner e (ρ-extend xs ρ)))
                       (error 'parse "bad parameter specification: ~a" xs))]
                  [`(let ([,xs ,e0]) ,e1)
                   (if (andmap symbol? xs)
                       (let-e (fresh-label) xs
                              (inner e0 ρ)
                              (inner e1 (ρ-extend xs ρ)))
                       (error 'parse "bad parameter specification: ~a" xs))]
                  [`(letrec ([,xs ,e0]) ,e1)
                   (if (andmap symbol? xs)
                       (letrec-e (fresh-label) xs
                                 (inner e0 (ρ-extend xs ρ))
                                 (inner e1 (ρ-extend xs ρ)))
                       (error 'parse "bad parameter specification: ~a" xs))]
                  [`(if ,e0 ,e1 ,e2)
                   (if-e (fresh-label) 
                         (inner e0 ρ)
                         (inner e1 ρ)
                         (inner e2 ρ))]
                  [`(chaperone-operator ,e0 ,e1)
                   (ch-op-e (fresh-label)
                            (inner e0 ρ)
                            (inner e1 ρ))]
                  [`(impersonate-operator ,e0 ,e1)
                   (im-op-e (fresh-label)
                            (inner e0 ρ)
                            (inner e1 ρ))]
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
    [(ch-op-e L e0 e1)
     `(chaperone-operator ,(unparse e0)
                          ,(unparse e1))]
    [(if-e L e0 e1 e2)
     `(if ,(unparse e0)
          ,(unparse e1)
          ,(unparse e2))]
    [(int-e L i)
     i]
    [(lam-e L xs e0)
     `(λ ,xs ,(unparse e0))]
    [(let-e L xs e0 e1)
     `(let ([,xs ,(unparse e0)])
        ,(unparse e1))]
    [(letrec-e L xs e0 e1)
     `(letrec ([,xs ,(unparse e0)])
        ,(unparse e1))]
    [(prim-e L id)
     id]
    [(ref-e L x)
     x]))
