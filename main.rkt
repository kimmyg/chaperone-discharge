#lang racket/base
(require "parse.rkt"
         "big-step.rkt")

(eval (parse '(letrec ([(fac) (λ (n)
                                (if (= n 0)
                                    1
                                    (* n (fac (- n 1)))))])
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
                          (fac-rec 3))))))
