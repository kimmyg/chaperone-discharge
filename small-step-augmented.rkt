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
(struct chap-ults-κ κ (c w*) #:transparent)
(struct chap-wrap-κ κ (vs*) #:transparent)
(struct handle-κ κ (x ρ e) #:transparent)
(struct if-κ κ (ρ e0 e1) #:transparent)
(struct let-κ κ (xs r ρ e) #:transparent)
(struct letrec-κ κ (xs r ρ e) #:transparent)
(struct or-κ κ (ρ e) #:transparent)
(struct raise-κ κ () #:transparent)

(struct Σ (κs σ) #:transparent)
#;(struct Σ (τ κs σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)
(struct Σ! Σ (msg) #:transparent)

(define chap-stack empty)
(define chap-source (make-hasheq))
(define runtime-error-chaps (seteq))
(define funtime-error-chaps (seteq))

(define (app κs σ op vs)
  (match op
    [(chaperone f w)
     (set! chap-stack (cons op chap-stack))
     (app (cons (chap-args-κ f vs) κs) σ w vs)]
    [(closure xs r ρ e)
     (let-values ([(ρ σ) (bind ρ σ xs r vs)])
       (Σe κs σ ρ e))]
    [(primitive id f +)
     (if (arity-includes? + (length vs))
         (with-handlers ([exn:fail:contract? (λ (_) (Σ! κs σ (format "native call error for ~a" id)))])
           (Σv κs σ (native-apply f vs)))
         (Σ! κs σ (format "arity of primitive operator ~a incompatible with operands ~a" id vs)))]))

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
        (Σv κs σ (single-value (closure xs r ρ e)))]
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
       [(prim-e '*)
        (Σv κs σ (single-value (primitive '* * 2)))]
       [(prim-e '-)
        (Σv κs σ (single-value (primitive '- - 2)))]
       #;[(chaperone-operator-e e0 e1)
          (Σe (cons (chap-op-κ ρ e1) κs) σ ρ e0)]
       [(prim-e 'chaperone-operator)
        (Σv κs σ (single-value (primitive 'chaperone-operator
                                          (λ (f w)
                                            (if (and (operator? f)
                                                     (operator? w))
                                                (if (arity=? (operator-arity w)
                                                             (operator-arity f))
                                                    (let ([c (chaperone f w)])
                                                      (hash-set! chap-source c (and (not (empty? chap-stack))
                                                                                    (first chap-stack)))
                                                      c)
                                                    (ERROR "operator and wrapper must have same arity"))
                                                (ERROR "chaperone-operator must be applied to operators")))
                                          2)))]
       [(prim-e 'integer?)
        (Σv κs σ (single-value (primitive 'integer? integer? 1)))]
       [(prim-e 'not)
        (Σv κs σ (single-value (primitive 'not not 1)))]
       [(prim-e 'values)
        (Σv κs σ (single-value (primitive 'values values (arity-at-least 0))))]
       [(raise-e e)
        (Σe (cons (raise-κ) κs) σ ρ e)]
       [(ref-e x)
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
       [(chap-args-κ op vs)
        (define c (first chap-stack))
        (set! chap-stack (rest chap-stack))
        (let ([vs* (value->list v)])
          (cond
            [(= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (app κs σ op vs*)
                 (Σ! κs σ (format "chaperone did more than chaperone arguments!")))]
            [(= (add1 (length vs))
                (length vs*))
             (match-let ([(cons w* vs*) vs*])
               (if (operator? w*)
                   (app (cons (chap-ults-κ c w*) κs) σ op vs*)
                   (Σ! κs σ "extra argument must be an operator")))]
            [else
             (Σ! κs σ "arguments wrapper must return same number or one additional result")]))]                     
       [(chap-ults-κ c w*)
        (set! chap-stack (cons c chap-stack))
        (let ([vs* (value->list v)])
          (if (arity-includes? (operator-arity w*)
                               (length vs*))
              (app (cons (chap-wrap-κ vs*) κs) σ w* vs*)
              (Σ! κs σ "results wrapper arity incompatible with operator results")))]
       [(chap-wrap-κ vs*)
        (set! chap-stack (rest chap-stack))
        (let ([vs (value->list v)])
          (if (= (length vs*)
                 (length vs))
              (if (andmap chaperone-of? vs vs*)
                  (Σv κs σ v)
                  (Σ! κs σ "results wrapper did more than chaperone results"))
              (Σ! κs σ "results wrapper didn't give number it was given")))]
       [(handle-κ x ρ e)
        (Σv κs σ v)]
       [(if-κ ρ e0 e1)
        (let ([v (single-value! v)])
          (Σe κs σ ρ (if v e0 e1)))]
       [(let-κ xs r ρ e)
        (let-values ([(ρ σ) (bind ρ σ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(letrec-κ xs r ρ e)
        (let ([σ (rec-bind ρ σ xs r (value->list v))])
          (Σe κs σ ρ e))]
       [(or-κ ρ e)
        (let ([v (single-value! v)])
          (if v
              (Σv κs σ (single-value v))
              (Σe κs σ ρ e)))]
       [(raise-κ)
        (unless (empty? chap-stack)
          (set! funtime-error-chaps (set-add funtime-error-chaps (first chap-stack))))
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
       (values chap-source
               funtime-error-chaps)
       #;(cons σ v)]
      [(Σ! κs σ msg)
       (Σ! κs σ msg)]
      [ς
       (inner (step ς))]))
  (inner (Σe empty (hasheqv) (hasheq) e)))


