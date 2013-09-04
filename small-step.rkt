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

(struct chap-κ κ (op) #:transparent)
(struct chap-neg-ults-κ chap-κ (f pos vs) #:transparent)
(struct chap-f-ults-κ chap-κ (pos) #:transparent)
(struct chap-pos-ults-κ chap-κ (vs) #:transparent)

(struct app-rands-κ κ (op vs ρ es) #:transparent)
(struct app-rator-κ κ (ρ es) #:transparent)
(struct chap-f-κ κ (L ρ neg pos) #:transparent)
(struct chap-neg-κ κ (L f ρ pos) #:transparent)
(struct chap-pos-κ κ (L f neg) #:transparent)
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
    [(chaperone L P f neg pos)
     (app (cons (chap-neg-ults-κ op f pos vs) κs) σ neg vs)]
    [(closure xs r ρ e)
     (let-values ([(σ ρ) (bind σ ρ xs r vs)])
       (Σe κs σ ρ e))]
    [(primitive id f +)
     (if (arity-includes? + (length vs))
         (with-handlers ([exn:fail:contract? (λ (_) (Σ! κs σ (format "native call error for ~a" id)))])
           (Σv κs σ (native-apply f vs)))
         (Σ! κs σ (format "arity of primitive operator ~a incompatible with operands ~a" id vs)))]))

#;(define (unpspec xs r)
    (if (empty? xs)
        (or r empty)
        (cons (first xs) (unpspec (rest xs) r))))



#;(define (subst/shadow σ ρ xs r e)
    (let* ([ρ (for/fold ([ρ ρ])
                ([x (in-list xs)])
                (hash-remove ρ x))]
           [ρ (if r
                  (hash-remove ρ r)
                  ρ)])
      (subst σ ρ e)))

#;(define (subst σ ρ e)
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

#;(define (reify σ v)
    (match v
      [(chaperone f w)
       (app-e (prim-e 'chaperone-operator)
              (list (reify σ f)
                    (reify σ w)))]
      [(closure xs r ρ e)
       (lam-e xs r (subst σ ρ e))]
      [(primitive id f +)
       (prim-e id)]))

(define (active-chaperone κs)
  (if (empty? κs)
      #f
      (match-let ([(cons κ κs) κs])
        (if (chap-κ? κ)
            (chap-κ-op κ)
            (active-chaperone κs)))))

(define step
  (match-lambda
    [(Σe κs σ ρ e)
     (match e
       [(app-e _ e es)
        (Σe (cons (app-rator-κ ρ es) κs) σ ρ e)]
       [(bool-e _ p)
        (Σv κs σ (single-value p))]
       [(ch-op-e L f neg pos)
        (Σe (cons (chap-f-κ L ρ neg pos) κs) σ ρ f)]
       [(handle-e _ x e0 e1)
        (Σe (cons (handle-κ x ρ e0) κs) σ ρ e1)]
       [(if-e _ e0 e1 e2)
        (Σe (cons (if-κ ρ e1 e2) κs) σ ρ e0)]
       [(int-e _ i)
        (Σv κs σ (single-value i))]
       [(lam-e _ xs r e)
        (let ([ρ (restrict ρ (bind-free-with xs r (free-variables e)))])
          (Σv κs σ (single-value (closure xs r ρ e))))]
       [(let-e _ xs r e0 e1)
        (Σe (cons (let-κ xs r ρ e1) κs) σ ρ e0)]
       [(letrec-e _ xs r e0 e1)
        (let ([ρ (pre-bind ρ xs r)])
          (Σe (cons (letrec-κ xs r ρ e1) κs) σ ρ e0))]
       [(or-e _ e0 e1)
        (Σe (cons (or-κ ρ e1) κs) σ ρ e0)]
       [(prim-e _ id)
        (Σv κs σ (single-value (case id
                                 [(=) (primitive '= = 2)]
                                 [(<) (primitive '< < 2)]
                                 [(*) (primitive '* * 2)]
                                 [(+) (primitive '+ + 2)]
                                 [(-) (primitive '- - 2)]
                                 [(boolean?) (primitive 'boolean? boolean? 1)]
                                 [(integer?) (primitive 'integer? integer? 1)]
                                 [(not) (primitive 'not not 1)]
                                 [(values) (primitive 'values values (arity-at-least 0))]
                                 [else (error 'eval "unknown primitive ~a" id)])))]
       [(raise-e _ e)
        (Σe (cons (raise-κ) κs) σ ρ e)]
       [(ref-e _ x)
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
        (let ([op (single-value! v)])
          (match es
            [(list)
             (app κs σ op empty)]
            [(cons e es)
             (Σe (cons (app-rands-κ op empty ρ es) κs) σ ρ e)]))]
       [(chap-f-κ L ρ neg pos)
        (let ([f (single-value! v)])
          (Σe (cons (chap-neg-κ L f ρ pos) κs) σ ρ neg))]
       [(chap-neg-κ L f ρ pos)
        (let ([neg (single-value! v)])
          (Σe (cons (chap-pos-κ L f neg) κs) σ ρ pos))]
       [(chap-pos-κ L f neg)
        (let ([pos (single-value! v)])
          (Σv κs σ (single-value (chaperone L (active-chaperone κs) f neg pos))))]
       [(chap-neg-ults-κ op f pos vs)
        (let ([vs* (value->list v)])
          (if (= (length vs)
                 (length vs*))
              (if (andmap chaperone-of? vs* vs)
                  (app (cons (chap-f-ults-κ op pos) κs) σ f vs*)
                  (Σ! κs σ (format "chaperone did more than chaperone arguments: ~a ~a" vs vs*)))
              (Σ! κs σ "negative wrapper must return same number of results")))]                     
       [(chap-f-ults-κ op pos)
        (let ([vs (value->list v)])
          (if (arity-includes? (operator-arity pos)
                               (length vs))
              (app (cons (chap-pos-ults-κ op vs) κs) σ pos vs)
              (Σ! κs σ "results wrapper arity incompatible with operator results")))]
       [(chap-pos-ults-κ op vs)
        (let ([vs* (value->list v)])
          (if (= (length vs)
                 (length vs*))
              (if (andmap chaperone-of? vs* vs)
                  (Σv κs σ v)
                  (Σ! κs σ "results wrapper did more than chaperone results"))
              (Σ! κs σ (format "positive wrapper didn't give number it was given ~a ~a" vs vs*))))]
       [(handle-κ x ρ e)
        (Σv κs σ v)]
       [(if-κ ρ e0 e1)
        (let ([v (single-value! v)])
          (Σe κs σ ρ (if v e0 e1)))]
       [(let-κ xs r ρ e)
        (let-values ([(σ ρ) (bind σ ρ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(letrec-κ xs r ρ e)
        (let ([σ (rec-bind σ ρ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(or-κ ρ e)
        (let ([v (single-value! v)])
          (if v
              (Σv κs σ (single-value v))
              (Σe κs σ ρ e)))]
       [(raise-κ)
        (match v
          [(single-value v)
           (letrec ([loop (match-lambda
                            [(cons (handle-κ x ρ e) κs)
                             (let-values ([(σ ρ) (bind σ ρ (list x) #f (list v))])
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


