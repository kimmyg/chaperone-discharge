#lang racket/base
(require "parse.rkt"
         "small-step.rkt")

#;(eval (parse '(letrec ([(fac) (λ (n)
                                  (if (= n 0)
                                      1
                                      (* (- 0 n) (fac (- n 1)))))])
                  (let ([(fac-rec) (chaperone-operator fac (λ (n)
                                                             (if (or (not (integer? n))
                                                                     (< n 0))
                                                                 (raise 42)
                                                                 (values (λ (n)
                                                                           (if (or (not (integer? n))
                                                                                   (< n 1))
                                                                               (raise 43)
                                                                               n))
                                                                         n))))])
                    (handle ([x x])
                            (fac-rec 7))))))

#;(eval (parse '(letrec ([(fac) (chaperone-operator
                                 (λ (n)
                                   (if (= n 0)
                                       -1
                                       (* n (fac (- n 1)))))
                                 (λ (n)
                                   (if (or (not (integer? n))
                                           (< n 0))
                                       (raise 42)
                                       (values (λ (n)
                                                 (if (or (not (integer? n))
                                                         (< n 1))
                                                     (raise 43)
                                                     n))
                                               n))))])
                  (handle ([x x])
                          (fac 5)))))

; identify the chaperone with the value that it's wrapping!?

(define factp
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

(define testp
  '(let ([(->) (λ (a b)
                 (λ (f)
                   (chaperone-operator
                    f
                    (λ (v)
                      (values b (a v))))))])
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
                 (n->f 0)))))))))

(define testp2
  '(let ([(->) (λ (a b)
                 (λ (f)
                   (chaperone-operator
                    f
                    (λ (v)
                      (values b (a v))))))])
     (let ([(any/c) (λ (x) x)])
       (let ([(any) values])
         (let ([(f) ((-> (-> any/c any) (any/c any))
                     (λ (x) x))])
           (f f))))))

#;(require "eval-util.rkt"
           "lang.rkt")

#;(chaperone-of?
   (chaperone (chaperone (closure '(x) #f #hasheq() (ref-e 'x))
                         (closure '(f) #f #hasheq((any/c . 0))
                                  (app-e (prim-e 'chaperone-operator)
                                         (list (ref-e 'f)
                                               (lam-e '(v) #f (app-e (ref-e 'any/c)
                                                                     (list (ref-e 'v))))))))
              (closure '(v) #f #hasheq((any/c . 0)) 
                       (app-e (ref-e 'any/c)
                              (list (ref-e 'v)))))
   (chaperone (closure '(x) #f #hasheq() (ref-e 'x))
              (closure '(f) #f #hasheq((any/c . 0))
                       (app-e (prim-e 'chaperone-operator)
                              (list (ref-e 'f)
                                    (lam-e '(v) #f (app-e (ref-e 'any/c)
                                                          (list (ref-e 'v)))))))))


#;'(chaperone-operator
  (λ (x) x)
  (λ (f)
    (values (-> any/c any)
            (chaperone-operator
             f
             (λ (v)
               (values any
                       (any/c v)))))))

#;'(λ (a (-> any/c any))
   (λ (f)
     (chaperone-operator
      f
      (λ (v)
        (values (-> any/c any) (a v))))))

(require racket/match)
(time
 (match (eval (parse factp))
  [(cons σ v)
   v]))
