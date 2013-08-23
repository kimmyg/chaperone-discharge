#lang racket/base
(require racket/function
         racket/list
         racket/match
         racket/set
         "value.rkt")

(provide (struct-out closure)
         (struct-out chaperone)
         (struct-out impersonator)
         (struct-out primitive)
         (struct-out ERROR)
         chaperone-of?
         bind
         pre-bind
         rec-bind
         operator-arity
         arity=?
         arity-includes?
         arity-compatible?
         native-apply
         operator?
         restrict)

(define alloc
  (let ([i 0])
    (λ (x)
      (begin0
        i
        (set! i (add1 i))))))

(struct ERROR (state) #:transparent)

(struct closure (xs r ρ e) #:transparent)
(struct chaperone (f w) #:transparent)
(struct impersonator (f w) #:transparent)
(struct primitive (id f +) #:transparent)

(define (chaperone-of? v0 v1)
  (cond
    [(and (chaperone? v0)
          (chaperone? v1))
     (or (equal? v0 v1)
         (and (chaperone-of? (chaperone-w v0)
                             (chaperone-w v1))
              (chaperone-of? (chaperone-f v0)
                             (chaperone-f v1)))
         (chaperone-of? (chaperone-f v0) v1))]
    [(chaperone? v0)
     (chaperone-of? (chaperone-f v0) v1)]
    [(chaperone? v1)
     #f]
    [else
     (equal? v0 v1)]))

(define operator-arity
  (match-lambda
    [(closure xs r ρ e)
     (if r (arity-at-least (length xs)) (length xs))]
    [(chaperone f w)
     (operator-arity w)]
    [(impersonator f w)
     (operator-arity w)]
    [(primitive id f +)
     +]))

(define (operator? f)
  ; this doesn't need to be recursive, does it?
  (or (closure? f)
      (and (chaperone? f)
           (operator? (chaperone-f f)))
      (and (impersonator? f)
           (operator? (impersonator-f f)))
      (and (primitive? f)
           (primitive-+ f))))

(define (native-apply f vs)
  (list->value (call-with-values (λ () (apply f vs)) list)))

(define (arity-compatible? xs r vs)
  (let ([m (length xs)])
    (arity-includes? (if r (arity-at-least m)  m)
                     (length vs))))

(define (bind ρ σ xs r vs)
  (if (arity-compatible? xs r vs)
      (let ([n (length xs)])
        (let*-values ([(ρ σ) (for/fold ([ρ ρ]
                                        [σ σ])
                               ([x xs]
                                [v (take vs n)])
                               (let ([α (alloc x)])
                                 (values (hash-set ρ x α)
                                         (hash-set σ α v))))]
                      [(ρ σ) (if r
                                 (let ([α (alloc r)])
                                   (values (hash-set ρ r α)
                                           (hash-set σ α (drop vs n))))
                                 (values ρ σ))])
          (values ρ σ)))
      (error 'bind "~a ~a ~a" xs r vs)))

(define (pre-bind ρ xs r)
  (let* ([ρ (for/fold ([ρ ρ])
              ([x xs])
              (let ([α (alloc x)])
                (hash-set ρ x α)))]
         [ρ (if r
                (let ([α (alloc r)])
                  (hash-set ρ r α))
                ρ)])
    ρ))

(define (rec-bind ρ σ xs r vs)
  (if (arity-compatible? xs r vs)
      (let ([n (length xs)])
        (let* ([σ (for/fold ([σ σ])
                    ([x xs]
                     [v (take vs n)])
                    (hash-set σ (hash-ref ρ x) v))]
               [σ (if r
                      (hash-set σ (hash-ref ρ r) (drop vs n))
                      σ)])
          σ))
      (error 'rec-bind "~a ~a ~a" xs r vs)))

(define (restrict ρ xs)
  (for/hasheq ([x (in-set xs)])
    (values x (hash-ref ρ x))))

