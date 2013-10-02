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

(struct chap-κ κ (L f) #:transparent)

(struct chap-app-κ κ (L) #:transparent)
(struct chap-neg-ults-κ chap-app-κ (f vs) #:transparent)
(struct chap-f-ults-κ chap-app-κ (pos) #:transparent)
(struct chap-pos-ults-κ chap-app-κ (vs) #:transparent)

(struct if-κ κ (ρ e0 e1) #:transparent)
(struct let-κ κ (xs ρ e) #:transparent)
(struct letrec-κ κ (xs ρ e) #:transparent)

(struct Σ (κs σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)
(struct Σa Σ (v vs) #:transparent)
(struct Σ! Σ (e) #:transparent) ; contains blame

(define (inspect-blame κs)
  (if (empty? κs)
      (λC:error)
      (match-let ([(cons κ κs) κs])
        (cond
          [(chap-κ? κ)
           (λC:blame0 (chap-κ-L κ))]
          [(chap-neg-ults-κ? κ)
           (λC:blame- (chap-app-κ-L κ))]
          [(chap-pos-ults-κ? κ)
           (λC:blame+ (chap-app-κ-L κ))]
          [else
           (inspect-blame κs)]))))

(define (A σ ρ ae)
  (match ae
    [(bool-e _ p)
     p]
    [(int-e _ i)
     i]
    [(lam-e _ xs e)
     (closure xs ρ e)]
    [(prim-e _ id)
     (id->primitive id)]
    [(ref-e _ x)
     (hash-ref σ (hash-ref ρ x))]))

(define step
  (match-lambda
    [(Σe κs σ ρ e)
     (match e
       [(app-e _ ae aes)
        (let ([f (A σ ρ ae)]
              [vs (map (λ (ae) (A σ ρ ae)) aes)])
          (Σa κs σ f vs))]
       [(bool-e _ p)
        (Σv κs σ (single-value p))]
       
       ; a non-operator f will cause an error to occur when it
       ; wouldn't necessarily otherwise (a lone f may never be
       ; applied.)
       
       [(ch-op-e L ae0 e1)
        (Σe (cons (chap-κ L (A σ ρ ae0)) κs) σ ρ e1)]
       [(if-e _ ae0 e1 e2)
        (Σe κs σ ρ (if (A σ ρ ae0) e1 e2))]
       [(int-e _ i)
        (Σv κs σ (single-value i))]
       [(lam-e _ xs e0)
        (Σv κs σ (single-value (closure xs (restrict ρ (free-variables e)) e0)))]
       [(let-e _ xs e0 e1)
        (Σe (cons (let-κ xs ρ e1) κs) σ ρ e0)]
       [(letrec-e _ xs e0 e1)
        (let ([ρ (pre-bind ρ xs)])
          (Σe (cons (letrec-κ xs ρ e1) κs) σ ρ e0))]
       [(prim-e _ id)
        (Σv κs σ (single-value (id->primitive id)))]
       [(ref-e _ x)
        (Σv κs σ (single-value (hash-ref σ (hash-ref ρ x))))])]
    [(Σv (cons κ κs) σ v)
     (match κ
       [(chap-κ L f)
        (match v
          [(single-value w)
           (if (operator? f)
               (if (operator? w)
                   (if (arity=? (operator-arity f)
                                (operator-arity w))
                       (Σv κs σ (single-value (chaperone L f w)))
                       (Σ! κs σ (λC:blame9 L)))
                   (Σ! κs σ (λC:blame8 L)))
               (Σ! κs σ (λC:blame2 L)))]
          [(multiple-values vs)
           (Σ! κs σ (λC:blame10 L))])]
       [(chap-neg-ults-κ L f vs)
        (let ([vs* (value->list v)])
          (cond
            [(= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (Σa κs σ f vs*)
                 (Σ! κs σ (λC:blame1 L)))]
            [(= (add1 (length vs))
                (length vs*))
             (let ([v* (first vs*)]
                   [vs* (rest vs*)])
               (if (operator? v*)
                   (if (andmap chaperone-of? vs* vs)
                       (Σa (cons (chap-f-ults-κ L v*) κs) σ f vs*)
                       (λC:blame1 L))
                   (Σ! κs σ (λC:blame3 L))))]
            [else
             (Σ! κs σ (λC:blame4 L))]))]

       [(chap-f-ults-κ L pos)
        (let ([vs (value->list v)])
          (if (arity-includes? (operator-arity pos)
                               (length vs))
              (Σa (cons (chap-pos-ults-κ L vs) κs) σ pos vs)
              (Σ! κs σ (λC:blame5 L))))]
       [(chap-pos-ults-κ L vs)
        (let ([vs* (value->list v)])
          (if (= (length vs)
                 (length vs*))
              (if (andmap chaperone-of? vs* vs)
                  (Σv κs σ v)
                  (Σ! κs σ (λC:blame7 L)))
              (Σ! κs σ (λC:blame6 L))))]
       [(let-κ xs ρ e)
        (let-values ([(σ ρ) (bind σ ρ xs (value->list v))])
          (Σe κs σ ρ e))]
       [(letrec-κ xs ρ e)
        (let ([σ (rec-bind σ ρ xs (value->list v))])
          (Σe κs σ ρ e))])]
    [(Σa κs σ op vs)
     (if (arity-includes? (operator-arity op) (length vs))
      (match op
        [(chaperone L f -)
         (Σa (cons (chap-neg-ults-κ L f vs) κs) σ - vs)]
        [(closure xs ρ e)
         (let-values ([(σ ρ) (bind σ ρ xs vs)])
           (Σe κs σ ρ e))]
        [(primitive id f +)
         (with-handlers ([λC:error? (λ (e) (Σ! κs σ (inspect-blame κs)))])
           (Σv κs σ (native-apply f vs)))])
      (Σ! κs σ (inspect-blame κs)))]))


(define (eval e)
  (define inner
    (match-lambda
      [(Σv (list) σ v)
       (cons σ v)]
      [(Σ! κs σ e)
       (Σ! κs σ e)]
      [ς
       (inner (step ς))]))
  (inner (Σe empty (hasheqv) (hasheq) e)))


