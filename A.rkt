#lang racket/base
(require racket/list
         racket/match
         "lang.rkt")

(provide A)

(define (atom? e)
  (or (bool-e? e)
      (int-e? e)
      (prim-e? e)
      (ref-e? e)))

(define (<=A0? e)
  (or (atom? e)
      (lam-e? e)))

(define (<=A1? e)
  (or (<=A0? e)
      (app-e? e)
      (ch-op-e? e)
      (im-op-e? e)))

(define (A e)
  (define fresh
    (let ([counts (make-hasheq)])
      (λ (prefix)
        (begin0
          (string->symbol (format "~a~a" prefix (hash-ref counts prefix 0)))
          (hash-update! counts prefix add1 0)))))
  
  (define (A* es k)
    (if (empty? es)
        (k empty (λ (e0) e0))
        (let ([e (first es)]
              [es (rest es)])
          (A0 'arg e (λ (a0 k0)
                       (A* es (λ (a* k*)
                                (k (cons a0 a*) (λ (e0) (k0 (k* e0)))))))))))
  
  (define (A0 type e k)
    (if (atom? e)
        (k e (λ (x0) x0))
        (match e
          [(lam-e L xs r e0)
           (k (lam-e L xs r (A2 e0 (λ (c0 k0) (k0 c0)))) (λ (e0) e0))]
          [e
           (A1 e (λ (b0 k0)
                   (let ([x (fresh type)])
                     (k (ref-e (fresh 'A) x) (λ (e0) (k0 (let-e (fresh 'A) (list x) #f b0 e0)))))))])))
  
  (define (A1 e k)
    (if (<=A0? e)
        (A0 #f e k)
        (match e
          [(app-e L e es)
           (A0 'fun e (λ (a0 k0)
                        (A* es (λ (a* k*)
                                 (k (app-e L a0 a*) (λ (e0) (k0 (k* e0))))))))]
          [(ch-op-e L e0 e1 e2)
           (A0 'oned e0 (λ (a0 k0)
                          (A0 'oner e1 (λ (a1 k1)
                                         (k (ch-op-e L a0 a1) (λ (e0) (k0 (k1 e0))))))))]
          [(im-op-e L e0 e1 e2)
           (A0 'ated e0 (λ (a0 k0)
                          (A0 'ator e1 (λ (a1 k1)
                                         (k (im-op-e a0 a1) (λ (e0) (k0 (k1 e0))))))))]
          [(or-e L e0 e1)
           (A0 'temp e0 (λ (a0 k0)
                          (A2 e1 (λ (a1 k1)
                                   (k (if-e L
                                            a0
                                            a0
                                            (k1 a1))
                                      k0)))))])))
  
  (define (A2 e k)
    (if (<=A1? e)
        (A1 e k)
        (match e
          [(if-e L e0 e1 e2)
           (A0 'test e0 (λ (a0 k0)
                          (k (if-e L
                                   a0
                                   (A2 e1 (λ (c1 k1) (k1 c1)))
                                   (A2 e2 (λ (c2 k2) (k2 c2))))
                             k0)))]
          [(let-e L xs r e0 e1)
           (A1 e0 (λ (b0 k0)
                    (A2 e1 (λ (c1 k1)
                             (k (let-e L xs r b0 (k1 c1)) (λ (e0) (k0 e0)))))))]
          [(letrec-e L xs r e0 e1)
           (A1 e0 (λ (b0 k0)
                    (A2 e1 (λ (c1 k1)
                             (k (letrec-e L xs r b0 (k1 c1)) (λ (e0) (k0 e0)))))))]
          
          
          [(raise-e L e0)
           (A0 'error e0 (λ (a0 k0)
                           (k (raise-e L a0) k0)))])))
  
  (A2 e (λ (c0 k0) (k0 c0))))

(module+ main
  (require "parse.rkt")
  
  (define p2
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
             (let ([(nat/c) (λ (n)
                              (if (or (not (integer? n))
                                      (< n 0))
                                  (raise 43)
                                  n))])
               (let ([(church/c) (-> (-> any/c any)
                                     (-> any/c any))])
                 (letrec ([(n->f) ((-> nat/c church/c)
                                   (λ (n)
                                     (if (= n 0)
                                         (λ (f) (λ (x) x))
                                         (let ([(n-1) (n->f (- n 1))])
                                           (λ (f)
                                             (let ([(fn-1) (n-1 f)])
                                               (λ (x) (f (fn-1 x)))))))))])
                   (let ([(f->n) ((-> church/c nat/c)
                                  (λ (c)
                                    ((c (λ (x) (+ x 1))) 0)))])
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
                             (f->n (c:! (n->f 6))))))))))))))))
  
  (unparse
   (A
    (parse p2))))

