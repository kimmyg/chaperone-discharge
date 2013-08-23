#lang racket/base
(require racket/match
         racket/set)

(provide (struct-out exp)
         (struct-out ref-e)
         (struct-out int-e)
         (struct-out bool-e)
         (struct-out lam-e)
         (struct-out let-e)
         (struct-out letrec-e)
         (struct-out app-e)
         (struct-out app-values-e)
         (struct-out if-e)
         (struct-out and-e)
         (struct-out or-e)
         (struct-out handle-e)
         (struct-out raise-e)
         (struct-out prim-e)
         free-variables
         bind-free-with)

(struct exp () #:transparent)
(struct ref-e exp (x) #:transparent)
(struct int-e exp (n) #:transparent)
(struct bool-e exp (p) #:transparent)
(struct lam-e exp (xs r e) #:transparent)
(struct let-e exp (xs r e0 e1) #:transparent)
(struct letrec-e exp (xs r e0 e1) #:transparent)
(struct app-e exp (e es) #:transparent)
(struct app-values-e exp (e0 e1) #:transparent)
(struct if-e exp (e0 e1 e2) #:transparent)
(struct and-e exp (e0 e1) #:transparent)
(struct or-e exp (e0 e1) #:transparent)
(struct handle-e exp (x e0 e1) #:transparent)
(struct raise-e exp (e) #:transparent)
(struct prim-e exp (id) #:transparent)

(define (bind-free-with xs r ys)
  (let ([xs (foldl (λ (x xs) (set-remove xs x)) ys xs)])
    (if r
        (set-remove xs r)
        xs)))

(define free-variables
  (match-lambda
    [(app-e e es)
     (foldl set-union (free-variables e) (map free-variables es))]
    [(if-e e0 e1 e2)
     (set-union (free-variables e0)
                (free-variables e1)
                (free-variables e2))]
    [(or-e e0 e1)
     (set-union (free-variables e0)
                (free-variables e1))]
    [(raise-e e)
     (free-variables e)]
    [(ref-e x)
     (seteq x)]
    [(or (int-e _)
         (bool-e _)
         (prim-e _))
     (seteq)]
    [(lam-e xs r e)
     (bind-free-with xs r (free-variables e))]
    [(let-e xs r e0 e1)
     (set-union (free-variables e0)
                (bind-free-with xs r (free-variables e1)))]
    [(letrec-e xs r e0 e1)
     (bind-free-with xs r (set-union (free-variables e0)
                                     (free-variables e1)))]))

