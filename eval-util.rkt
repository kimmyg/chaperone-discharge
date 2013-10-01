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
         (struct-out λC:error)
         (struct-out λC:blame)
         (struct-out λC:blame+)
         (struct-out λC:blame-)
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
         restrict
         id->primitive)

(define alloc
  (let ([i 0])
    ;(λ (x) x)))
    (λ (x)
      (begin0
        i
        (set! i (add1 i))))))


(struct λC:error () #:transparent)
(struct λC:blame (L) #:transparent)
(struct λC:blame+ λC:blame () #:transparent)
(struct λC:blame- λC:blame () #:transparent)

(struct closure (xs r ρ e) #:transparent)
(struct chaperone (L f neg pos) #:transparent)
(struct impersonator (L f neg pos) #:transparent)
(struct primitive (id f +) #:transparent)

(define (chaperone-of? v0 v1)
  (cond
    [(and (chaperone? v0)
          (chaperone? v1))
     (or (equal? v0 v1)
         (and (chaperone-of? (chaperone-neg v0)
                             (chaperone-neg v1))
              (chaperone-of? (chaperone-pos v0)
                             (chaperone-pos v1))
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
     (signature-arity xs r)]
    [(chaperone L f neg pos)
     (operator-arity f)]
    [(impersonator L f neg pos)
     (operator-arity f)]
    [(primitive id f +)
     +]))

(define (signature-arity xs r)
  (if r
      (arity-at-least (length xs))
      (length xs)))

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
  (with-handlers ([exn:fail? (λ (_) (raise (λC:error)))])
    (list->value (call-with-values (λ () (apply f vs)) list))))

(define (arity-compatible? xs r vs)
  (let ([m (length xs)])
    (arity-includes? (if r (arity-at-least m)  m)
                     (length vs))))

(define (bind σ ρ xs r vs)
  (if (arity-compatible? xs r vs)
      (let ([n (length xs)])
        (let*-values ([(σ ρ) (for/fold ([σ σ]
                                        [ρ ρ])
                               ([x xs]
                                [v (take vs n)])
                               (let ([α (alloc x)])
                                 (values (hash-set σ α v)
                                         (hash-set ρ x α))
                                 #;(values (hash-update σ α (λ (s) (set-add s v)) (set))
                                           (hash-set ρ x α))))]
                      [(σ ρ) (if r
                                 (let ([α (alloc r)])
                                   (values (hash-set σ α (drop vs n))
                                           (hash-set ρ r α))
                                   #;(values (hash-update σ α (λ (s) (set-add s (drop vs n))) (set))
                                             (hash-set ρ r α)))
                                 (values σ ρ))])
          (values σ ρ)))
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

(define (rec-bind σ ρ xs r vs)
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

(define (id->primitive id)
  (case id
    [(=) (primitive '= = 2)]
    [(<) (primitive '< < 2)]
    [(>) (primitive '> > 2)]
    [(*) (primitive '* * 2)]
    [(+) (primitive '+ + 2)]
    [(-) (primitive '- - 2)]
    [(raise) (primitive 'raise (λ () (raise (λC:error))) (arity-at-least 0))]
    [(null) (primitive 'null null #f)]
    [(null?) (primitive 'null? null? 1)]
    [(cons) (primitive 'cons cons 2)]
    [(pair?) (primitive 'pair? pair? 2)]
    [(car) (primitive 'car car 1)]
    [(cdr) (primitive 'cdr cdr 1)]
    [(boolean?) (primitive 'boolean? boolean? 1)]
    [(integer?) (primitive 'integer? integer? 1)]
    [(not) (primitive 'not not 1)]
    [(values) (primitive 'values values (arity-at-least 0))]
    [else (error 'id->primitive "unknown primitive ~a" id)]))

