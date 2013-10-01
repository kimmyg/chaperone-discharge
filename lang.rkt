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
         (struct-out if-e)
         (struct-out prim-e)
         (struct-out ch-op-e)
         (struct-out im-op-e)
         free-variables
         bind-free-with)

(struct exp (label) #:transparent)
(struct ref-e exp (x) #:transparent)
(struct int-e exp (n) #:transparent)
(struct bool-e exp (p) #:transparent)
(struct lam-e exp (xs e) #:transparent)
(struct let-e exp (xs e0 e1) #:transparent)
(struct letrec-e exp (xs e0 e1) #:transparent)
(struct app-e exp (e es) #:transparent)
(struct if-e exp (e0 e1 e2) #:transparent)
(struct prim-e exp (id) #:transparent)
(struct ch-op-e exp (f w) #:transparent)
(struct im-op-e exp (f w) #:transparent)

(define (bind-free-with xs ys)
  (foldl (λ (x xs) (set-remove xs x)) ys xs))

(define free-variables
  (match-lambda
    [(app-e _ e es)
     (foldl set-union (free-variables e) (map free-variables es))]
    [(if-e _ e0 e1 e2)
     (set-union (free-variables e0)
                (free-variables e1)
                (free-variables e2))]
    [(ref-e _ x)
     (seteq x)]
    [(or (int-e _ _)
         (bool-e _ _)
         (prim-e _ _))
     (seteq)]
    [(lam-e _ xs e)
     (bind-free-with xs (free-variables e))]
    [(let-e _ xs e0 e1)
     (set-union (free-variables e0)
                (bind-free-with xs (free-variables e1)))]
    [(letrec-e _ xs e0 e1)
     (bind-free-with xs (set-union (free-variables e0)
                                   (free-variables e1)))]
    [(ch-op-e _ e0 e1)
     (set-union (free-variables e0)
                (free-variables e1))]
    [(im-op-e _ e0 e1)
     (set-union (free-variables e0)
                (free-variables e1))]))

