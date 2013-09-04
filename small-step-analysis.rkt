#lang racket/base
(require racket/function
         racket/list
         racket/match
         racket/set
         "eval-util.rkt"
         "lang.rkt"
         "value.rkt")

(provide eval
         (struct-out Σ)
         (struct-out Σe)
         (struct-out Σv)
         (struct-out Σ!))

(struct κ () #:transparent)
(struct app-rands-κ κ (op vs ρ es) #:transparent)
(struct app-rator-κ κ (ρ es) #:transparent)
(struct chap-1-κ κ (info op vs) #:transparent)
(struct chap-2-κ κ (info w*) #:transparent)
(struct chap-3-κ κ (info vs*) #:transparent)
(struct handle-κ κ (x ρ e) #:transparent)
(struct if-κ κ (ρ e0 e1) #:transparent)
(struct let-κ κ (xs r ρ e) #:transparent)
(struct letrec-κ κ (xs r ρ e) #:transparent)
(struct or-κ κ (ρ e) #:transparent)
(struct raise-κ κ () #:transparent)


(struct Σ (cs κs σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)
(struct Σ! Σ (msg) #:transparent)

(define (app cs κs σ op vs)
  (match op
    [(chaperone f w)
     (app cs (cons (chap-1-κ op f vs) κs) σ w vs)]
    [(closure xs r ρ e)
     (let-values ([(ρ σ) (bind ρ σ xs r vs)])
       (Σe cs κs σ ρ e))]
    [(primitive id f +)
     (if (arity-includes? + (length vs))
         (with-handlers ([exn:fail:contract? (λ (_) (Σ! cs κs σ (format "native call error for ~a" id)))])
           (Σv cs κs σ (native-apply f vs)))
         (Σ! cs κs σ (format "arity of primitive operator ~a incompatible with operands ~a" id vs)))]))

(define step
  (match-lambda
    [(Σe cs κs σ ρ e)
     (match e
       [(app-e _ e es)
        (Σe cs (cons (app-rator-κ ρ es) κs) σ ρ e)]
       [(bool-e _ p)
        (Σv cs κs σ (single-value p))]
       [(ch-op-e L f w)
        (Σe cs κs σ ρ (app-e #f
                             (prim-e L 'chaperone-operator)
                             (list f w)))]
       [(handle-e _ x e0 e1)
        (Σe cs (cons (handle-κ x ρ e0) κs) σ ρ e1)]
       [(if-e _ e0 e1 e2)
        (Σe cs (cons (if-κ ρ e1 e2) κs) σ ρ e0)]
       [(int-e _ i)
        (Σv cs κs σ (single-value i))]
       [(lam-e _ xs r e)
        (let ([ρ (restrict ρ (bind-free-with xs r (free-variables e)))])
          (Σv cs κs σ (single-value (closure xs r ρ e))))]
       [(let-e _ xs r e0 e1)
        (Σe cs (cons (let-κ xs r ρ e1) κs) σ ρ e0)]
       [(letrec-e _ xs r e0 e1)
        (let ([ρ (pre-bind ρ xs r)])
          (Σe cs (cons (letrec-κ xs r ρ e1) κs) σ ρ e0))]
       [(or-e _ e0 e1)
        (Σe cs (cons (or-κ ρ e1) κs) σ ρ e0)]
       [(prim-e _ '=)
        (Σv cs κs σ (single-value (primitive '= = 2)))]
       [(prim-e _ '<)
        (Σv cs κs σ (single-value (primitive '< < 2)))]
       [(prim-e _ '+)
        (Σv cs κs σ (single-value (primitive '+ + 2)))]
       [(prim-e _ '*)
        (Σv cs κs σ (single-value (primitive '* * 2)))]
       [(prim-e _ '-)
        (Σv cs κs σ (single-value (primitive '- - 2)))]
       [(prim-e L 'chaperone-operator)
        (Σv cs κs σ (single-value (primitive 'chaperone-operator
                                          (λ (f w)
                                            (if (and (operator? f)
                                                     (operator? w))
                                                (if (arity=? (operator-arity w)
                                                             (operator-arity f))
                                                    (chaperone L f w)
                                                    (ERROR L "operator and wrapper must have same arity"))
                                                (ERROR L (format "chaperone-operator must be applied to operators ~a ~a" f w))))
                                          2)))]
       [(prim-e _ 'boolean?)
        (Σv cs κs σ (single-value (primitive 'boolean? boolean? 1)))]
       [(prim-e _ 'integer?)
        (Σv cs κs σ (single-value (primitive 'integer? integer? 1)))]
       [(prim-e _ 'not)
        (Σv cs κs σ (single-value (primitive 'not not 1)))]
       [(prim-e _ 'values)
        (Σv cs κs σ (single-value (primitive 'values values (arity-at-least 0))))]
       [(raise-e _ e)
        (Σe cs (cons (raise-κ) κs) σ ρ e)]
       [(ref-e _ x)
        (Σv cs κs σ (single-value (hash-ref σ (hash-ref ρ x))))]
       )]
    [(Σv cs (cons κ κs) σ v)
     (match κ
       [(app-rands-κ op vs ρ es)
        (let ([v (single-value! v)])
          (match es
            [(list)
             (app cs κs σ op (reverse (cons v vs)))]
            [(cons e es)
             (Σe cs (cons (app-rands-κ op (cons v vs) ρ es) κs) σ ρ e)]))]
       [(app-rator-κ ρ es)
        #;(printf "2 ~a\n" v)
        (let ([op (single-value! v)])
          (match es
            [(list)
             (app cs κs σ op empty)]
            [(cons e es)
             (Σe cs (cons (app-rands-κ op empty ρ es) κs) σ ρ e)]))]
       [(chap-1-κ info op vs)
        (let ([vs* (value->list v)])
          (cond
            [(= (length vs)
                (length vs*))
             (if (andmap chaperone-of? vs* vs)
                 (app cs κs σ op vs*)
                 (Σ! cs κs σ (format "chaperone did more than chaperone arguments! ~a ~a" vs vs*)))]
            [(= (add1 (length vs))
                (length vs*))
             (match-let ([(cons w* vs*) vs*])
               (if (operator? w*)
                   (if (andmap chaperone-of? vs* vs)
                       (app cs (cons (chap-2-κ info w*) κs) σ op vs*)
                       (Σ! cs κs σ (format "chaperone did more than chaperone arguments! ~a ~a" vs vs*)))
                   (Σ! cs κs σ "extra argument must be an operator")))]
            [else
             (Σ! cs κs σ "arguments wrapper must return same number or one additional result")]))]                     
       [(chap-2-κ info w*)
        (let ([vs* (value->list v)])
          (if (arity-includes? (operator-arity w*)
                               (length vs*))
              (app cs (cons (chap-3-κ info vs*) κs) σ w* vs*)
              (Σ! cs κs σ "results wrapper arity incompatible with operator results")))]
       [(chap-3-κ info vs*)
        (let ([vs (value->list v)])
          (if (= (length vs*)
                 (length vs))
              (if (andmap chaperone-of? vs vs*)
                  (Σv cs κs σ v)
                  (Σ! cs κs σ "results wrapper did more than chaperone results"))
              (Σ! cs κs σ (format "results wrapper didn't give number it was given ~a ~a" vs* vs))))]
       [(handle-κ x ρ e)
        (Σv cs κs σ v)]
       [(if-κ ρ e0 e1)
        #;(printf "3 ~a\n" v)
        (let ([v (single-value! v)])
          (Σe cs κs σ ρ (if v e0 e1)))]
       [(let-κ xs r ρ e)
        (let-values ([(ρ σ) (bind ρ σ xs r (value->list v))])
          (Σe cs κs σ ρ e))]
       [(letrec-κ xs r ρ e)
        (let ([σ (rec-bind ρ σ xs r (value->list v))])
          (Σe cs κs σ ρ e))]
       [(or-κ ρ e)
        #;(printf "4 ~a\n" v)
        (let ([v (single-value! v)])
          (if v
              (Σv cs κs σ (single-value v))
              (Σe cs κs σ ρ e)))]
       [(raise-κ)
        (match v
          [(single-value v)
           (letrec ([loop (match-lambda**
                            [(cs (cons (handle-κ x ρ e) κs))
                             (let-values ([(ρ σ) (bind ρ σ (list x) #f (list v))])
                               (Σe cs κs σ ρ e))]
                            [(cs (cons (chap-1-κ info op vs) κs))
                             (loop (set-add cs info) κs)]
                            [(cs (cons (chap-3-κ info vs*) κs))
                             (loop (set-add cs info) κs)]
                            [(cs (cons κ κs))
                             (loop cs κs)]
                            [(cs (list))
                             (Σ! cs κs σ "no handler for error")])])
             (loop cs κs))]
          [(multiple-values vs)
           (Σ! cs κs σ "raise must receive one value!")])])]))


(define (eval e)
  (define inner
    (match-lambda
      [(Σv cs (list) σ v)
       (Σv cs (list) σ v)]
      [(Σ! cs κs σ msg)
       (Σ! cs κs σ msg)]
      [ς
       (inner (step ς))]))
  (inner (Σe (seteq) empty (hasheqv) (hasheq) e)))


