#lang racket/base
(require racket/match
         racket/set)

(provide (struct-out +-L->)
         (struct-out +-L)
         (struct-out L->)
         (struct-out +->)
         select
         vizualize)

(struct +-L-> (+ L >) #:transparent)
(struct +-L (+ L) #:transparent)
(struct L-> (L >) #:transparent)
(struct +-> (+ >) #:transparent)

(define (select g . a+vs)
  (match a+vs
    [(list* a v a+vs)
     (apply select
            (for/fold ([g (set)])
              ([e (in-set g)])
              (if (equal? (a e) v)
                  (set-add g e)
                  g))
            a+vs)]
    [(list a)
     (for/set ([e (in-set g)])
       (a e))]
    [(list)
     g]))

(define (vizualize g node-render edge-render)
  (displayln "digraph BST {\nsize=\"6,4\"")
  (set-for-each
   g
   (match-lambda
     [(+-L-> ς αγ ς′)
      (printf "\"~a\" -> \"~a\" [label=\"~a\"];\n"
              (node-render ς)
              (node-render ς′)
              (edge-render αγ))]))
  (displayln "}"))

(module+ main
  (define g (set))
  
  (define (make-x)
    (let ([xs (make-hasheqv)]
          [i 0])
      (λ (x)
        (cond
          [(eq? x 'present)
           (hash-keys xs)]
          [(exact-nonnegative-integer? x)
           (hash-ref xs x #f)]
          [else
           (begin
              (hash-set! xs i x)
              (set! i (add1 i)))]))))
  
  (define ςs (make-x))
  (define Γs (make-x))
  
  (struct ς (e ρ))
  
  (define display-ς
    (match-lambda
      [(ς e ρ)
       (format "~a ~a" e ρ)]))
  
  (struct Γ (x e ρ))
  
  (define display-Γ
    (match-lambda
      [(Γ x e ρ)
       (format "~a ~a ~a" x e ρ)]))
  
  (struct ΔΓ ())
  (struct ε ΔΓ ())
  (struct +Γ ΔΓ (Γ))
  (struct -Γ ΔΓ (Γ))
  
  (define display-ΔΓ
    (match-lambda
      [(ε)
       "ε"]
      [(+Γ Γ)
       (format "+ ~a" (display-Γ Γ))]
      [(-Γ Γ)
       (format "- ~a" (display-Γ Γ))]))
  
  (define (read/prompt prompt)
    (printf "~a: " prompt)
    (read))
  
  (define (read-ς)
    (displayln "read ς")
    (ς (read/prompt "e")
       (read/prompt "ρ")))
  
  (define (read-Γ)
    (displayln "read Γ")
    (Γ (read/prompt "x")
       (read/prompt "e")
       (read/prompt "ρ")))
  
  (define (read-ΔΓ)
    (match (read/prompt "(+ - e)")
      ['+
       (+Γ (read-Γ))]
      ['-
       (-Γ (read-Γ))]
      ['e
       (ε)]))
       
  
  (define (ς/ref)
    (printf "read ς reference from ~a\n" (ςs 'present))
    (or (ςs (read/prompt "ς reference"))
        (ς/ref)))
  
  (ςs (read-ς))
  
  (let loop ([i 0])
    (match (read/prompt "command")
      ['done
       (exit 0)]
      ['new
       (let* ([s (ς/ref)]
              [e (read-ΔΓ)]
              [t (read-ς)])
         (set! g (set-add g (+-L-> s e t)))
         (ςs t))]
      ['add
       (let* ([s (ς/ref)]
              [e (read-ΔΓ)]
              [t (ς/ref)])
         (set! g (set-add g (+-L-> s e t))))])
    (with-output-to-file (format "s~a.gv" i)
      (λ () (vizualize g display-ς display-ΔΓ))
      #:exists 'replace)
    (loop (add1 i))))
