#lang racket

(define (fac n)
  (if (zero? n)
      1
      (* n (fac (sub1 n)))))

(define fac-chap
  (chaperone-procedure
   fac
   (λ (n)
     #;(printf "checking argument ~a\n" n)
     (unless (exact-nonnegative-integer? n)
       (raise-argument-error 'fac "exact-nonnegative-integer?" n))
     (values (λ (n)
               (unless (exact-nonnegative-integer? n)
                 (raise-result-error 'fac "exact-nonnegative-integer?" n))
               n)
             n))))

(define fac-chap-deep
  (chaperone-procedure
   (λ (n)
     (if (zero? n)
         1
         (* n (fac-chap-deep (sub1 n)))))
   (λ (n)
     #;(printf "checking argument ~a\n" n)
     (unless (exact-nonnegative-integer? n)
       (raise-argument-error 'fac "exact-nonnegative-integer?" n))
     (values (λ (n)
               (unless (exact-nonnegative-integer? n)
                 (raise-result-error 'fac "exact-nonnegative-integer?" n))
               n)
             n))))

(time
 (for ([i (in-range 1000000)])
   (fac 5)))

(time
 (for ([i (in-range 1000000)])
   (fac-chap 5)))

(time
 (for ([i (in-range 1000000)])
   (fac-chap-deep 5)))
