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

(struct chap-cre-κ κ (L) #:transparent)
(struct chap-f-κ chap-cre-κ (ρ neg pos) #:transparent)
(struct chap-neg-κ chap-cre-κ (f ρ pos) #:transparent)
(struct chap-pos-κ chap-cre-κ (f neg) #:transparent)

(struct chap-app-κ κ (L) #:transparent)
(struct chap-neg-ults-κ chap-app-κ (f pos vs) #:transparent)
(struct chap-f-ults-κ chap-app-κ (pos) #:transparent)
(struct chap-pos-ults-κ chap-app-κ (vs) #:transparent)

(struct app-rands-κ κ (op vs ρ es) #:transparent)
(struct app-rator-κ κ (ρ es) #:transparent)
(struct handle-κ κ (ρ e) #:transparent)
(struct if-κ κ (ρ e0 e1) #:transparent)
(struct let-κ κ (xs r ρ e) #:transparent)
(struct letrec-κ κ (xs r ρ e) #:transparent)
(struct and-κ κ (ρ e) #:transparent)
(struct or-κ κ (ρ e) #:transparent)

(struct Σ (κs σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)
(struct Σ! Σ (e) #:transparent) ; contains blame

(define (app κs σ op vs)
  (if (arity-includes? (operator-arity op) (length vs))
      (match op
        [(chaperone L f neg pos)
         (app (cons (chap-neg-ults-κ L f pos vs) κs) σ neg vs)]
        [(closure xs r ρ e)
         (let-values ([(σ ρ) (bind σ ρ xs r vs)])
           (Σe κs σ ρ e))]
        [(primitive id f +)
         (with-handlers ([λC:error? (λ (e) (Σ! κs σ (inspect-blame κs)))])
           (Σv κs σ (native-apply f vs)))])
      (Σ! κs σ (inspect-blame κs))))

(define (inherit-blame κs)
  (if (empty? κs)
      #f
      (match-let ([(cons κ κs) κs])
        (cond
          [(chap-cre-κ? κ)
           (cons '• (chap-cre-κ-L κ))]
          [(chap-neg-ults-κ? κ)
           (cons '- (chap-app-κ-L κ))]
          [(chap-pos-ults-κ? κ)
           (cons '+ (chap-app-κ-L κ))]
          [else
           (inherit-blame κs)]))))

(define (inspect-blame κs)
  (if (empty? κs)
      (λC:error)
      (match-let ([(cons κ κs) κs])
        (cond
          [(chap-cre-κ? κ)
           (λC:blame (chap-cre-κ-L κ))]
          [(chap-neg-ults-κ? κ)
           (λC:blame- (chap-app-κ-L κ))]
          [(chap-pos-ults-κ? κ)
           (λC:blame+ (chap-app-κ-L κ))]
          [else
           (inspect-blame κs)]))))

(define (call/single-value κs σ v e f)
  (match v
    [(single-value v)
     (f v)]
    [(multiple-values vs)
     (Σ! κs σ e)]))

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
       [(if-e _ e0 e1 e2)
        (Σe (cons (if-κ ρ e1 e2) κs) σ ρ e0)]
       [(int-e _ i)
        (Σv κs σ (single-value i))]
       [(lam-e _ xs r e0)
        (Σv κs σ (single-value (closure xs r (restrict ρ (free-variables e)) e0)))]
       [(let-e _ xs r e0 e1)
        (Σe (cons (let-κ xs r ρ e1) κs) σ ρ e0)]
       [(letrec-e _ xs r e0 e1)
        (let ([ρ (pre-bind ρ xs r)])
          (Σe (cons (letrec-κ xs r ρ e1) κs) σ ρ e0))]
       [(and-e _ e0 e1)
        (Σe (cons (and-κ ρ e1) κs) σ ρ e0)]
       [(or-e _ e0 e1)
        (Σe (cons (or-κ ρ e1) κs) σ ρ e0)]
       [(prim-e _ id)
        (Σv κs σ (single-value (id->primitive id)))]
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
        (call/single-value
         κs σ v (λC:blame L)
         (λ (f) (Σe (cons (chap-neg-κ L f ρ pos) κs) σ ρ neg)))]
       [(chap-neg-κ L f ρ pos)
        (call/single-value
         κs σ v (λC:blame L)
         (λ (neg) (Σe (cons (chap-pos-κ L f neg) κs) σ ρ pos)))]
       [(chap-pos-κ L f neg)
        (call/single-value
         κs σ v (λC:blame L)
         (λ (pos) (Σv κs σ (single-value (chaperone L f neg pos)))))]
       [(chap-neg-ults-κ L f pos vs)
        (let ([vs* (value->list v)])
          (if (= (length vs)
                 (length vs*))
              (if (andmap chaperone-of? vs* vs)
                  (app (cons (chap-f-ults-κ L pos) κs) σ f vs*)
                  (Σ! κs σ (λC:blame- L)))
              (Σ! κs σ (λC:blame- L))))]                     
       [(chap-f-ults-κ L pos)
        (let ([vs (value->list v)])
          (if (arity-includes? (operator-arity pos)
                               (length vs))
              (app (cons (chap-pos-ults-κ L vs) κs) σ pos vs)
              (Σ! κs σ (λC:blame L))))]
       [(chap-pos-ults-κ L vs)
        (let ([vs* (value->list v)])
          (if (= (length vs)
                 (length vs*))
              (if (andmap chaperone-of? vs* vs)
                  (Σv κs σ v)
                  (Σ! κs σ (λC:blame+ L)))
              (Σ! κs σ (λC:blame+ L))))]
       [(handle-κ ρ e)
        (Σv κs σ v)]
       [(if-κ ρ e0 e1)
        (call/single-value
         κs σ v (λC:error)
         (λ (v) (Σe κs σ ρ (if v e0 e1))))]
       [(let-κ xs r ρ e)
        (let-values ([(σ ρ) (bind σ ρ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(letrec-κ xs r ρ e)
        (let ([σ (rec-bind σ ρ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(and-κ ρ e)
        (call/single-value
         κs σ v (λC:error)
         (λ (v)
           (if v
               (Σe κs σ ρ e)
               (Σv κs σ (single-value v)))))]
       [(or-κ ρ e)
        (call/single-value
         κs σ v (λC:error)
         (λ (v)
           (if v
               (Σv κs σ (single-value v))
               (Σe κs σ ρ e))))])]))


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


