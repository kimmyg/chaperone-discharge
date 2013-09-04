#lang racket/base
(require racket/function
         racket/list
         racket/match
         racket/set
         "eval-util.rkt"
         "lang.rkt"
         "value.rkt")

(provide eval)

(struct κ () #:transparent)
(struct app-rands-κ κ (op vs ρ es) #:transparent)
(struct app-rator-κ κ (ρ es) #:transparent)
(struct chap-args-κ κ (op vs) #:transparent)
(struct chap-ults-κ κ (w*) #:transparent)
(struct chap-wrap-κ κ (vs*) #:transparent)
(struct handle-κ κ (x ρ e) #:transparent)
(struct if-κ κ (ρ e0 e1) #:transparent)
(struct let-κ κ (xs r ρ e) #:transparent)
(struct letrec-κ κ (xs r ρ e) #:transparent)
(struct or-κ κ (ρ e) #:transparent)
(struct raise-κ κ () #:transparent)

(struct Σ (κs σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)
(struct Σ! Σ (msg) #:transparent)

(define (app κs σ op vs)
  (match op
    [(chaperone f w)
     (app (cons (chap-args-κ f vs) κs) σ w vs)]
    [(closure xs r ρ e)
     (let-values ([(ρ σ) (bind ρ σ xs r vs)])
       (Σe κs σ ρ e))]
    [(primitive id f +)
     (if (arity-includes? + (length vs))
         (with-handlers ([exn:fail:contract? (λ (_) (Σ! κs σ (format "native call error for ~a" id)))])
           (Σv κs σ (native-apply f vs)))
         (Σ! κs σ (format "arity of primitive operator ~a incompatible with operands ~a" id vs)))]))

(define (unpspec xs r)
  (if (empty? xs)
      (or r empty)
      (cons (first xs) (unpspec (rest xs) r))))

(define unparse
  (match-lambda
    [(app-e e es)
     `(,(unparse e) . ,(map unparse es))]
    [(if-e e0 e1 e2)
     `(if ,(unparse e0) ,(unparse e1) ,(unparse e2))]
    [(int-e i)
     i]
    [(lam-e xs r e)
     `(λ ,(unpspec xs r) ,(unparse e))]
    [(let-e xs r e0 e1)
     `(let ([,(unpspec xs r) ,(unparse e0)])
        ,(unparse e1))]
    [(letrec-e xs r e0 e1)
     `(letrec ([,(unpspec xs r) ,(unparse e0)])
        ,(unparse e1))]
    [(or-e e0 e1)
     `(or ,(unparse e0)
          ,(unparse e1))]
    [(prim-e id)
     id]
    [(raise-e e)
     `(raise ,(unparse e))]
    [(ref-e x)
     x]))

(define (subst/shadow σ ρ xs r e)
  (let* ([ρ (for/fold ([ρ ρ])
              ([x (in-list xs)])
              (hash-remove ρ x))]
         [ρ (if r
                (hash-remove ρ r)
                ρ)])
    (subst σ ρ e)))

(define (subst σ ρ e)
  (if (or (int-e? e)
          (prim-e? e))
      e
      (match e
        [(app-e e es)
         (app-e (subst σ ρ e)
                (map (λ (e) (subst σ ρ e)) es))]
        [(if-e e0 e1 e2)
         (if-e (subst σ ρ e0)
               (subst σ ρ e1)
               (subst σ ρ e2))]
        [(lam-e xs r e)
         (lam-e xs r (subst/shadow σ ρ xs r e))]
        [(let-e xs r e0 e1)
         (let-e xs r (subst σ ρ e0) (subst/shadow σ ρ xs r e1))]
        [(or-e e0 e1)
         (or-e (subst σ ρ e0)
               (subst σ ρ e1))]
        [(raise-e e)
         (raise-e (subst σ ρ e))]
        [(ref-e x)
         (if (and (hash-has-key? ρ x)
                  (hash-has-key? σ (hash-ref ρ x)))
             (reify σ (hash-ref σ (hash-ref ρ x)))
             (ref-e x))])))

(define (reify σ v)
  (match v
    [(chaperone f w)
     (app-e (prim-e 'chaperone-operator)
            (list (reify σ f)
                  (reify σ w)))]
    [(closure xs r ρ e)
     (lam-e xs r (subst σ ρ e))]
    [(primitive id f +)
     (prim-e id)]))


(define step
  (match-lambda
    [(Σe κs σ ρ e)
     (match e
       [(app-e e es)
        (Σe (cons (app-rator-κ ρ es) κs) σ ρ e)]
       [(bool-e p)
        (Σv κs σ (single-value p))]
       [(handle-e x e0 e1)
        (Σe (cons (handle-κ x ρ e0) κs) σ ρ e1)]
       [(if-e e0 e1 e2)
        (Σe (cons (if-κ ρ e1 e2) κs) σ ρ e0)]
       [(int-e i)
        (Σv κs σ (single-value i))]
       [(lam-e xs r e)
        (let ([ρ (restrict ρ (bind-free-with xs r (free-variables e)))])
          (Σv κs σ (single-value (closure xs r ρ e))))]
       [(let-e xs r e0 e1)
        (Σe (cons (let-κ xs r ρ e1) κs) σ ρ e0)]
       [(letrec-e xs r e0 e1)
        (let ([ρ (pre-bind ρ xs r)])
          (Σe (cons (letrec-κ xs r ρ e1) κs) σ ρ e0))]
       [(or-e e0 e1)
        (Σe (cons (or-κ ρ e1) κs) σ ρ e0)]
       [(prim-e '=)
        (Σv κs σ (single-value (primitive '= = 2)))]
       [(prim-e '<)
        (Σv κs σ (single-value (primitive '< < 2)))]
       [(prim-e '+)
        (Σv κs σ (single-value (primitive '+ + 2)))]
       [(prim-e '*)
        (Σv κs σ (single-value (primitive '* * 2)))]
       [(prim-e '-)
        (Σv κs σ (single-value (primitive '- - 2)))]
       [(prim-e 'chaperone-operator)
        (Σv κs σ (single-value (primitive 'chaperone-operator
                                          (λ (f w)
                                            (if (and (operator? f)
                                                     (operator? w))
                                                (if (arity=? (operator-arity w)
                                                             (operator-arity f))
                                                    (chaperone f w)
                                                    (ERROR "operator and wrapper must have same arity"))
                                                (ERROR (format "chaperone-operator must be applied to operators ~a ~a" f w))))
                                          2)))]
       [(prim-e 'boolean?)
        (Σv κs σ (single-value (primitive 'boolean? boolean? 1)))]
       [(prim-e 'integer?)
        (Σv κs σ (single-value (primitive 'integer? integer? 1)))]
       [(prim-e 'not)
        (Σv κs σ (single-value (primitive 'not not 1)))]
       [(prim-e 'values)
        (Σv κs σ (single-value (primitive 'values values (arity-at-least 0))))]
       [(raise-e e)
        (Σe (cons (raise-κ) κs) σ ρ e)]
       [(ref-e x)
        #;(displayln ρ)
        (Σv κs σ (single-value (hash-ref σ (hash-ref ρ x))))]
       )]
    [(Σv (cons κ κs) σ v)
     (match κ
       [(app-rands-κ op vs ρ es)
        (let ([v (single-value! v)])
          (match es
            [(list)
             (app κs σ op (reverse (cons v vs)))]
            [(cons e es)
             (Σe (cons (app-rands-κ op (cons v vs) ρ es) κs) σ ρ e)]))]
       [(app-rator-κ ρ es)
        #;(printf "2 ~a\n" v)
        (let ([op (single-value! v)])
          (match es
            [(list)
             (app κs σ op empty)]
            [(cons e es)
             (Σe (cons (app-rands-κ op empty ρ es) κs) σ ρ e)]))]
       [(chap-args-κ op vs)
        (let ([vs* (value->list v)])
          (cond
            [(= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (app κs σ op vs*)
                 (Σ! κs σ (format "chaperone did more than chaperone arguments! ~a ~a" vs vs*)))]
            [(= (add1 (length vs))
                (length vs*))
             (match-let ([(cons w* vs*) vs*])
               (if (operator? w*)
                   (if (andmap chaperone-of? vs* vs)
                       (app (cons (chap-ults-κ w*) κs) σ op vs*)
                       (Σ! κs σ (format "chaperone did more than chaperone arguments! ~a ~a" vs vs*)))
                   (Σ! κs σ "extra argument must be an operator")))]
            [else
             (Σ! κs σ "arguments wrapper must return same number or one additional result")]))]                     
       [(chap-ults-κ w*)
        (let ([vs* (value->list v)])
          (if (arity-includes? (operator-arity w*)
                               (length vs*))
              (app (cons (chap-wrap-κ vs*) κs) σ w* vs*)
              (Σ! κs σ "results wrapper arity incompatible with operator results")))]
       [(chap-wrap-κ vs*)
        (let ([vs (value->list v)])
          (if (= (length vs*)
                 (length vs))
              (if (andmap chaperone-of? vs vs*)
                  (Σv κs σ v)
                  (Σ! κs σ "results wrapper did more than chaperone results"))
              (Σ! κs σ (format "results wrapper didn't give number it was given ~a ~a" vs* vs))))]
       [(handle-κ x ρ e)
        (Σv κs σ v)]
       [(if-κ ρ e0 e1)
        #;(printf "3 ~a\n" v)
        (let ([v (single-value! v)])
          (Σe κs σ ρ (if v e0 e1)))]
       [(let-κ xs r ρ e)
        (let-values ([(ρ σ) (bind ρ σ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(letrec-κ xs r ρ e)
        (let ([σ (rec-bind ρ σ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(or-κ ρ e)
        #;(printf "4 ~a\n" v)
        (let ([v (single-value! v)])
          (if v
              (Σv κs σ (single-value v))
              (Σe κs σ ρ e)))]
       [(raise-κ)
        (match v
          [(single-value v)
           (letrec ([loop (match-lambda
                            [(cons (handle-κ x ρ e) κs)
                             (let-values ([(ρ σ) (bind ρ σ (list x) #f (list v))])
                               (Σe κs σ ρ e))]
                            [(cons κ κs)
                             (loop κs)]
                            [(list)
                             (Σ! κs σ "no handler for error")])])
             (loop κs))]
          [(multiple-values vs)
           (Σ! κs σ "raise must receive one value!")])])]))


(define (eval e)
  (define inner
    (match-lambda
      [(Σv (list) σ v)
       (cons σ v)]
      [(Σ! κs σ msg)
       (Σ! κs σ msg)]
      [ς
       (inner (step ς))]))
  (inner (Σe empty (hasheqv) (hasheq) e)))


