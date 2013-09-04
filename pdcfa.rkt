#lang racket/base
(require racket/list
         racket/match
         racket/port
         racket/set
         (rename-in "A.rkt" [A T-A])
         "eval-util.rkt"
         "graph.rkt"
         "lang.rkt"
         "parse.rkt"
         "value.rkt")

(struct αΓ () #:transparent)
(struct ε αΓ () #:transparent)
(struct +Γ αΓ (Γ) #:transparent)
(struct -Γ αΓ (Γ) #:transparent)

(struct Σ () #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σv Σ (v) #:transparent)

(struct Γ () #:transparent)
(struct let-Γ Γ (xs r ρ e) #:transparent)

(define (inject e)
  (Σe (hasheq) e))

(define (A? e)
  (or (bool-e? e)
      (int-e? e)
      (lam-e? e)
      (prim-e? e)
      (ref-e? e)))

(define (A σ ρ e)
  (match e
    [(bool-e L p)
     (set p)]
    [(int-e L i)
     (set i)]
    [(lam-e L xs r e)
     (set (closure xs r ρ e))]
    [(prim-e L 'values)
     (set (primitive 'values values (arity-at-least 0)))]
    [(ref-e L x)
     (hash-ref σ (hash-ref ρ x))]))

(define (A* σ ρ es)
  (if (empty? es)
      (set empty)
      (let ([e (first es)]
            [es (rest es)])
        (let ([vs (A σ ρ e)]
              [vs* (A* σ ρ es)])
          (for*/set ([v (in-set vs)]
                     [vs (in-set vs*)])
            (cons v vs))))))

(define (B vs)
  (for/set ([v (in-set vs)])
    (single-value v)))

(define (i0 σ ς γ)
  (displayln "another step")
  (let ([line (read-line)])
    (if (zero? (string-length line))
        (void)
        (begin
          (match (with-input-from-string line read)
            ['(store-keys)
             (displayln (hash-keys σ))]
            [`(store ,x)
             (displayln (hash-ref σ x #f))]
            ['(s-name)
             (cond
               [(Σe? ς)
                (displayln 'Σe)]
               [else
                ς])])
          (i0 σ ς γ)))))

(define (deliver σ γ vs)
  (match γ
    [(let-Γ xs r ρ e)
     (let-values ([(σ L->s)
                   (for/fold ([σ σ]
                              [L->s (set)])
                     ([v (in-set vs)])
                     (let-values ([(σ ρ) (bind σ ρ xs r (value->list v))])
                       (values σ (set-add L->s (L-> (-Γ γ) (Σe ρ e))))))])
       (cons σ L->s))]))
  
(define (step σ ς γ)
  #;(i0 σ ς γ)
  (match ς
    [(Σe ρ e)
     (if (A? e)
         (deliver σ γ (B (A σ ρ e)))
         (match e
           [(app-e L e es)
            (printf "app ~a ~a\n" e es)
            (let ([vs* (A* σ ρ es)])
              (let-values ([(σ L->s)
                            (for/fold ([σ σ]
                                       [L->s (set)])
                              ([v (in-set (A σ ρ e))])
                              (match v
                                [(closure xs r ρ e)
                                 (let-values ([(σ ςs)
                                               (for/fold ([σ σ]
                                                          [ςs (set)])
                                                 ([vs (in-set vs*)])
                                                 (let-values ([(σ ρ) (bind σ ρ xs r vs)])
                                                   (values σ (set-add ςs (Σe ρ e)))))])
                                   (values σ (set-union L->s (for/set ([ς (in-set ςs)])
                                                               (L-> (ε) ς)))))]))])
                (cons σ L->s)))]
           [(let-e L xs r e0 e1)
            (printf "let ~a ~a\n" xs r)
            (cons σ (set (L-> (+Γ (let-Γ xs r ρ e1)) (Σe ρ e0))))]))]))


#;(define (run e)
    (define frontier (set))
    (define visited (set))
    (define σ (make-hasheqv))
    (define graph (set))
    (define ε-graph (set))
    (define (inner)
      (unless (set-empty? frontier)
        (let ([ς (set-first frontier)])
          (set! frontier (set-rest frontier))
          (for ([ς- (in-set (select ε-graph -->-> ς -->-+))])
            ς- 
            (->s σ ς
                 3))))))

(define (a σ graph ε-graph visited frontier)
  #;(when (> (set-count graph) 250)
      (displayln (set-count graph)))
  (if (set-empty? frontier)
      (values σ graph ε-graph visited frontier)
      (let ([ς (set-first frontier)])
        (let-values ([(σ graph ε-graph visited frontier)
                      (b σ
                         ς
                         graph
                         ε-graph
                         (set-add visited ς)
                         (set-rest frontier))])
          (a σ graph ε-graph visited frontier)))))

(define (top-frames ς graph ε-graph)
  (let* ([γαss (set-map
                (select ε-graph -->-> ς -->-+)
                (λ (ς′) (select graph -L->-> ς′ -L->-L)))]
         [γs (map +Γ-Γ (filter +Γ? (set->list (apply set-union (set) γαss))))]
         [γs (if (ormap set-empty? γαss) (cons #f γs) γs)])
    γs))

(define (b σ ς graph ε-graph visited frontier)
  (let ([γs (top-frames ς graph ε-graph)])
    (for/fold ([σ σ]
               [graph graph]
               [ε-graph ε-graph]
               [visited visited]
               [frontier frontier])
      ([γ (in-list γs)])
      (match-let ([(cons σ es) (step σ ς γ)])
        #;(display-step ς γ es)
        (c σ ς es graph ε-graph visited frontier)))))

(define (c σ ς es graph ε-graph visited frontier)
  (if (set-empty? es)
      (values σ graph ε-graph visited frontier)
      (let-values ([(σ graph ε-graph visited frontier)
                    (d σ ς (set-first es) graph ε-graph visited frontier)])
        (c σ ς (set-rest es) graph ε-graph visited frontier))))

#;(define subby
    (match-lambda
      [(Σe σ ρ e)
       (letrec ([f (λ (e)
                     (cond
                       [(procedure? e)
                        e]
                       [(native-value? e)
                        e]
                       [(dynamic-closure? e)
                        '<closure>]
                       [(set? e)
                        `(set . ,(set-map e f))]
                       [else
                        (match e
                          [(app-expr e es)
                           `(,(f e) . ,(map f es))]
                          [(app-values-expr e0 e1)
                           `(,(f e0) ,(f e1))]
                          [(if-expr e0 e1 e2)
                           `(if ,(f e0) ,(f e1) ,(f e2))]
                          [(lam-expr xs r e)
                           `(λ ,(plist xs r) ,(f e))]
                          [(let-expr xs r e0 e1)
                           `(let ([,(plist xs r) ,(f e0)]) ,(f e1))]
                          [(letrec-expr xs r e0 e1)
                           `(letrec ([,(plist xs r) ,(f e0)]) ,(f e1))]
                          [(primval-expr id)
                           `(primval ,id)]
                          [(ref-expr x)
                           (if (and (hash-has-key? ρ x)
                                    (hash-has-key? σ (hash-ref ρ x)))
                               (f (hash-ref σ (hash-ref ρ x)))
                               x)])]))])
         (f e))]))


(define (d σ ς e- graph ε-graph visited frontier)
  (let ([γα (L->-L e-)]
        [ς′ (L->-> e-)])
    #;((current-print) (subby ς′))
    (let ([e (-L-> ς γα ς′)])
      (let-values ([(visited frontier)
                    (if (set-member? visited ς′)
                        (begin
                          (printf "already visited ~a\n" ς′)
                          (values visited frontier))
                        (values visited (set-add frontier ς′)))]
                   [(graph ε-graph)
                    (values (set-add graph e)
                            (match γα
                              [(+Γ γ′)
                               (set-add ε-graph (--> ς′ ς′))]
                              [(ε)
                               (for/fold ([ε-graph ε-graph])
                                 ([ς* (in-set (select ε-graph -->-> ς -->-+))])
                                 (set-add ε-graph (--> ς* ς′)))]
                              [(-Γ γ′)
                               (let ([γα′ (+Γ γ′)])
                                 (for/fold ([ε-graph ε-graph])
                                   ([ς* (in-set (select ε-graph -->-> ς -->-+))])
                                   (for/fold ([ε-graph ε-graph])
                                     ([ς+ (in-set (select graph -L->-> ς* -L->-L γα′ -L->-+))])
                                     (for/fold ([ε-graph ε-graph])
                                       ([ς^ (in-set (select ε-graph -->-> ς+ -->-+))])
                                       (set-add ε-graph (--> ς^ ς′))))))]))])
        (values σ graph ε-graph visited frontier)))))

(define (pdcfa ς)
  (let-values ([(σ graph ε-graph visited frontier)
                (a (hasheqv) (set) (set (--> ς ς)) (set) (set ς))])
    (cons σ graph)))

(define p
  '(let ([(->) (λ (c0 c1)
                 (λ (f)
                   (chaperone-operator
                    f
                    (λ (v) (values c1 (c0 v))))))])
     (let ([(any/c) (λ (x) x)])
       (let ([(any) values])
         (let ([(boolean/c) (λ (p)
                              (if (not (boolean? p))
                                  (raise 59)
                                  p))])
           (let ([(church/c) (-> (-> any/c any)
                                 (-> any/c any))])
             (let ([(c:*) ((-> church/c (-> church/c church/c))
                           (λ (n1)
                             (λ (n2)
                               (λ (f)
                                 (n1 (n2 f))))))])
               (let ([(c:zero?) ((-> church/c boolean/c)
                                 (λ (c) ((c (λ (x) #f)) #t)))])
                 (let ([(c:sub1) ((-> church/c church/c)
                                  (λ (n)
                                    (λ (f)
                                      (let ([(X) (λ (g) (λ (h) (h (g f))))])
                                        (λ (x)
                                          (((n X)
                                            (λ (u) x))
                                           (λ (u) u)))))))])
                   (letrec ([(c:!) ((-> church/c church/c)
                                    (λ (n)
                                      (if (c:zero? n)
                                          (λ (f) f)
                                          ((c:* n) (c:! (c:sub1 n))))))])
                     (c:! (λ (f) (λ (x) (f (f (f x)) x))))))))))))))

(unparse (T-A (parse p)))

(match-let ([(cons σ g) (pdcfa (inject (T-A (parse p))))])
  (displayln (set-count g)))

