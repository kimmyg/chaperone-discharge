#lang racket/base
(require racket/function
         racket/list
         racket/match
         racket/set
         "../graph.rkt"
         "../lang.rkt"
         "../parse.rkt")

(define (alloc x) x)
#|  (let ([i 0])
    ;(λ (x) x)))
    (λ (x)
      (begin0
        i
        (set! i (add1 i))))))
|#

(define (arity-compatible? xs vs)
  (= (length xs)
     (length vs)))

(define (bind σ ρ xs vs)
  (if (arity-compatible? xs vs)
      (for/fold ([σ σ]
                 [ρ ρ])
        ([x (in-list xs)]
         [v (in-list vs)])
        (let ([α (alloc x)])
          (values (hash-update σ α (λ (s) (set-add s v)) (set))
                  (hash-set ρ x α))))
      (error 'bind "~a ~a" xs vs)))

(define (pre-bind ρ xs)
  (for/fold ([ρ ρ])
    ([x xs])
    (let ([α (alloc x)])
      (hash-set ρ x α))))

(define (rec-bind σ ρ xs vs)
  (if (arity-compatible? xs vs)
      (for/fold ([σ σ])
        ([x (in-list xs)]
         [v (in-list vs)])
        (hash-update σ (hash-ref ρ x) (λ (s) (set-add s v)) (set)))
      (error 'rec-bind "~a ~a" xs vs)))


(struct Σ (σ) #:transparent)
(struct Σe Σ (ρ e) #:transparent)
(struct Σ! Σ () #:transparent)

(struct Γ () #:transparent)
(struct let-Γ Γ (ρ xs r e) #:transparent)
(struct letrec-Γ Γ (ρ xs r e) #:transparent)

(struct αΓ () #:transparent)
(struct +Γ (Γ) #:transparent)
(struct -Γ (Γ) #:transparent)
(struct ε () #:transparent)

(struct integer () #:transparent)

(define (inject p)
  (Σe (hasheqv) (hasheq) p))

(define render-node
  (match-lambda
    [(Σe σ ρ e)
     (unparse e)]))

(define render-frame
  (match-lambda
    [(let-Γ ρ xs r e)
     (unparse e)]
    [(letrec-Γ ρ xs r e)
     (unparse e)]))

(define render-edge
  (match-lambda
    [(+Γ γ)
     (format "+Γ ~a" (render-frame γ))]
    [(-Γ γ)
     (format "-Γ ~a" (render-frame γ))]
    [(ε)
     "ε"]))

(struct closure (xs r ρ e) #:transparent)
(struct primitive (id f +) #:transparent)
(struct chaperone (label f w) #:transparent)

;; program -> graph
(define (pdcfa p)
  (define gr (set))
  (define eps-gr (set))
  (define (top-frames ς)
    (let ([eps-preds (select eps-gr +->-> ς +->-+)])
      (for/fold ([a (set)])
        ([ς′ (in-set eps-preds)])
        (let* ([fs (select gr +-L->-> ς′)]
               [fs (set->list fs)]
               [fs (filter (compose +Γ? +-L->-L) fs)]
               [fs (map (λ (e) (cons (+-L->-+ e)
                                     (+Γ-Γ (+-L->-L e)))) fs)])
          (if (empty? fs)
              (error 'empty "here0")
              (set-union a (apply set fs)))))))
  
  (define (A σ ρ e)
    (match e
      [(bool-e L p)
       (set p)]
      [(int-e L i)
       (set (integer))]
      [(prim-e L id)
       (set (case id
              [(=)
               (primitive '=
                          (λ (n0 n1)
                            (if (and (integer? n0)
                                     (integer? n1))
                                (set (list #t) (list #f))
                                (raise (void))))
                          2)]
              [else (error 'A "unhandled primitive id \"~a\"" id)]))]
      [(ref-e L x)
       (hash-ref σ (hash-ref ρ x))]))
  
  (define (A* σ ρ es)
    (if (empty? es)
        (set empty)
        (for*/set ([v (in-set (A σ ρ (first es)))]
                   [vs (in-set (A* σ ρ (rest es)))])
          (cons v vs))))
  
  (define (inner ς)
    (match ς
      [(Σe σ ρ (app-e L e es))
       (for ([v (in-set (A σ ρ e))]
             [vs (in-set (A* σ ρ es))])
         (match v
           [(closure xs r ρ e)
            (let-values ([(σ′ ρ′) (bind σ ρ xs r vs)])
              (let ([ς′ (Σe σ′ ρ′ e)])
                (set! gr (set-add gr (+-L-> ς (ε) ς′)))
                (for ([ς* (in-set (select eps-gr +->-> ς +->-+))])
                  (set! eps-gr (set-add eps-gr (+-> ς* ς′))))
                (inner ς′)))]
           [(primitive id f +)
            (if (arity-includes? + (length vs))
                (for ([rs (in-set (apply f vs))])
                  (for ([x (top-frames ς)])
                    (match (cdr x)
                      [(let-Γ ρ xs r e)
                       (let-values ([(σ′ ρ′) (bind σ ρ xs r rs)])
                         (let ([ς′ (Σe σ′ ρ′ e)])
                           (set! gr (set-add gr (+-L-> ς (-Γ (cdr x)) ς′)))
                           (set! eps-gr (set-add eps-gr (+-> (car x) ς′)))
                           (inner ς′)))]
                      [(letrec-Γ ρ xs r e)
                       (let ([σ′ (rec-bind σ ρ xs r rs)])
                         (let ([ς′ (Σe σ′ ρ e)])
                           (set! gr (set-add gr (+-L-> ς (-Γ (cdr x)) ς′)))
                           (set! eps-gr (set-add eps-gr (+-> (car x) ς′)))
                           (inner ς′)))])))
                (let ([ς′ (Σ! σ)])
                  (set! gr (set-add gr (+-L-> ς (ε) ς′)))
                  (for ([ς* (in-set (select eps-gr +->-> ς +->-+))])
                    (set! eps-gr (set-add eps-gr (+-> ς* ς′))))))]))]
      [(Σe σ ρ (if-e L ae0 e1 e2))
       (for ([p (in-set (A σ ρ ae0))])
         (let ([ς′ (Σe σ ρ (if p e1 e2))])
           (set! gr (set-add gr (+-L-> ς (ε) ς′)))
           (for ([ς* (in-set (select eps-gr +->-> ς +->-+))])
             (set! eps-gr (set-add eps-gr (+-> ς* ς′))))))]
      [(Σe σ ρ (lam-e L xs e))
       (for ([x (top-frames ς)])
         (match (cdr x)
           [(letrec-Γ ρ xs′ r′ e′)
            (let ([σ′ (rec-bind σ ρ xs′ r′ (list (closure xs ρ e)))])
              (let ([ς′ (Σe σ′ ρ e′)])
                (set! gr (set-add gr (+-L-> ς (-Γ (cdr x)) ς′)))
                (set! eps-gr (set-add eps-gr (+-> (car x) ς′)))
                (inner ς′)))]))]
      [(Σe σ ρ (let-e L xs r e0 e1))
       (let ([ς′ (Σe σ ρ e0)]
             [αγ (+Γ (let-Γ ρ xs r e1))])
         (set! gr (set-add gr (+-L-> ς αγ ς′)))
         (set! eps-gr (set-add eps-gr (+-> ς′ ς′)))
         (inner ς′))]
      
      [(Σe σ ρ (letrec-e L xs r e0 e1))
       (let ([ρ′ (pre-bind ρ xs r)])
         (let ([ς′ (Σe σ ρ′ e0)]
               [αγ (+Γ (letrec-Γ ρ′ xs r e1))])
           (set! gr (set-add gr (+-L-> ς αγ ς′)))
           (set! eps-gr (set-add eps-gr (+-> ς′ ς′)))
           (inner ς′)))]
      [(Σe σ ρ e)
       (error 'inner "not ~a ~a" σ (unparse e))]))
  (let ([ς (inject p)])
    (set! eps-gr (set-add eps-gr (+-> ς ς)))
    (inner ς))
  (vizualize gr render-node render-edge))

(module+ main
  (require "../parse.rkt"
           "../A.rkt")
  
  (define p0
    '(letrec ([(fac) (λ (n)
                       (if (= n 0)
                           1
                           (* n (fac (- n 1)))))])
       (fac 5)))
  
  (with-output-to-file "p0.gv"
    (λ () (pdcfa (A (parse p0))))
    #:exists 'replace))
