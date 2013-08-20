#lang racket
#|
x
(λ (x ...) e)
(f e ...)
(let ([p-list e0] ...) e1)
set! (vector-set! maybe?)
(impersonate f w)
; takes
; - a function of arity m to n 
; - a wrapping function of arity m to m+1 where the first result
    is a function from n to n
; returns
; - a function of arity m to n
(impersonator-of? f0 f1)
; true if f0 is an impersonator of f1 (at least as impersonated as)
(chaperone f w)
; identical to impersonate but performs check to make sure all arguments 
; and results are chaperone-of?s the original
(doesn't make sense unless some mutable values are allowed)
; numbers (can't impersonate nor chaperone)
; lists (can't impersonate nor chaperone)

(impersonate (λ (x) x) (λ (x) (values sub1 (add1 x))))
|#
(struct impersonator (f ->))

(define (impersonator-of? f0 f1)
  (if (impersonator? f0)
      (if (impersonator? f1)
          (and (eq? (impersonator--> f0)
                    (impersonator--> f1))
               (impersonator-of? (impersonator-f f0)
                                 (impersonator-f f1)))
          (impersonator-of? (impersonator-f f0) f1))
      (and (not (impersonator? f1))
           (eq? f0 f1))))

(struct chaperone (f ->))

(define (chaperone-of? f0 f1)
  (if (chaperone? f0)
      (if (chaperone? f1)
          (and (eq? (chaperone--> f0)
                    (chaperone--> f1))
               (chaperone-of? (chaperone-f f0)
                              (chaperone-f f1)))
          (chaperone-of? (chaperone-f f0) f1))
      (and (not (chaperone? f1))
           (eq? f0 f1))))

; in an implementation that we control, we would be able to tell if 
; the procedures had the same code pointer and environment closure.
; suppose closure A is created from λ0 with e0 and impersonated with 
; W to make A'. suppose closure B is created from λ0 with e0 (identical
; to A). we know that (impersonator-of? A' A) is true. is 
; (impersonator-of? A' B) true? the racket implementation doesn't 
; consider closure A from λ0 with empty environment to be impersonator-of?
; closure B from λ0 with empty environment.
; we need to decide the how we want to expose equality.

(define (procedure-arity* f)
  (cond
    [(procedure? f)
     (procedure-arity f)]
    [(chaperone? f)
     (procedure-arity* (chaperone--> f))]
    [(impersonator? f)
     (procedure-arity* (impersonator--> f))]
    ; the * here means that wrappers can be impersonators!
    [else
     (error 'procedure-arity* "not a procedure")]))

(define (procedure-arity-includes?* f a)
  (arity-includes? (procedure-arity* f) a))

(define (app f . args)
  (cond
    [(procedure? f)
     (apply f args)]
    [(chaperone? f)
     (let ([f (chaperone-f f)]
           [-> (chaperone--> f)])
       (let ([args* (call-with-values (λ () (apply app -> args)) list)])
         (cond
           [(= (length args)
               (length args*))
            (if (andmap chaperone-of? args* args)
                (apply app f args)
                (error 'app "chaperone must only chaperone arguments"))]
           [(= (add1 (length args))
               (length args*))
            (let ([<- (first args*)]
                  [args* (rest args*)])
              (if (andmap chaperone-of? args* args)
                  (let ([results* (call-with-values (λ () (apply app f args*)) list)])
                    (if (procedure-arity-includes?* <- (length results*))
                        (let ([results (call-with-values (λ () (apply app <- results*)) list)])
                          (if (= (length results*)
                                 (length results))
                              (if (andmap chaperone-of? results results*)
                                  (apply values results)
                                  (error 'app "chaperone must only chaperone results"))
                              (error 'app "chaperone return wrapper must produce as many arguments as it consumes")))
                        (error 'app "chaperone return wrapper arity does not include number of values returned by wrapped function")))
                  (error 'app "chaperone must only chaperone arguments")))]
           [else
            (error 'app "impersonator wrapper must return the same number or one additional value")])))]
    [(impersonator? f)
     (let ([f (impersonator-f f)]
           [-> (impersonator--> f)])
       (let ([args* (call-with-values (λ () (apply app -> args)) list)])
         (cond
           [(= (length args)
               (length args*))
            (apply app f args*)]
           [(= (add1 (length args))
               (length args*))
            (let ([<- (first args*)]
                  [args* (rest args*)])
              (let ([results* (call-with-values (λ () (apply app f args*)) list)])
                (if (procedure-arity-includes?* <- (length results*))
                    (let ([results (call-with-values (λ () (apply app <- results*)) list)])
                      (if (= (length results*)
                             (length results))
                          (apply values results)
                          (error 'app "impersonator return wrapper must produce as many arguments as it consumes")))
                    (error 'app "impersonator return wrapper arity does not include number of values returned by wrapped function"))))]
           [else
            (error 'app "impersonator wrapper must return the same number or one additional value")])))]
    [else
     (error 'app "not a procedure ~a" f)]))
         

(define (impersonate-fun f w)
  (if (procedure-arity-includes?* w (procedure-arity* f))
      ; the stars here recognize that impersonators can be wrapped multiple times and impersonators can be used to wrap!
      (impersonator f w)
      (error 'impersonate "arity of wrapper must include arity of function")))

(define (chaperone-fun f w)
  (if (procedure-arity-includes?* w (procedure-arity* f))
      (chaperone f w)
      (error 'chaperone "arity of wrapper must include arity of function")))

(define f (impersonate-fun (λ (x) x) (λ (x) (values (λ (x) x) x))))
(define g (chaperone-fun (λ (x) x) (λ (x) (values (λ (x) x) x))))

(define (ratio f . xs)
  (let ([g (impersonate-fun f (λ xs (apply values values xs)))]
        [h (chaperone-fun f (λ xs (apply values values xs)))])
    (let-values ([(g-res g-cpu g-real g-gc)
                  (begin
                    (collect-garbage)
                    (time-apply 
                     (λ ()
                       (for ([i (in-range 1000000)])
                         (apply app g xs)))
                     empty))]
                 [(h-res h-cpu h-real h-gc)
                  (begin
                    (collect-garbage)
                    (time-apply
                     (λ ()
                       (for ([i (in-range 1000000)])
                         (apply app h xs)))
                     empty))])
      (exact->inexact (/ h-cpu g-cpu)))))
                           
(ratio (λ (a) (values a)) 0)
(ratio (λ (a b) (values a b)) 0 1)
(ratio (λ (a b c) (values a b c)) 0 1 2)
(ratio (λ (a b c d) (values a b c)) 0 1 2 3)
(ratio (λ (a b c d e) (values a b c)) 0 1 2 3 4)
(ratio (λ (a b c d e f) (values a b c)) 0 1 2 3 4 5)
(ratio (λ (a b c d e f g h) (values a b c)) 0 1 2 3 4 5 6 7)
(ratio (λ (a b c d e f g h i) (values a b c)) 0 1 2 3 4 5 6 7 8)

;(app (impersonate-fun (λ (x) x) (λ (x) (values add1 4))) 2)
;(app (chaperone-fun (λ (x) x) (λ (x) (values (λ (x) x) 4))) 4)
;(app (chaperone-fun (λ (x) x) (λ (x) (values add1 4))) 4)
;(app (chaperone-fun (λ (x) x) (λ (x) (values add1 4))) 2)

#|
blame for "chaperone errors"
1. wrapper function does not have the correct arity - chaperone creator
2. wrapper function modifies its arguments - chaperone creator
3. returned wrapper function does not have the required arity - chaperone creator
4. returned wrapper function modifies its arguments
5. returned wrapper function doesn't preserve the number of values - chaperone creator

of course all the blame lies with the creator--the feature wouldn't be fully-
baked otherwise. we have instead enumerated (negatively) the conditions that
must be satisfied for the chaperone to be discarded. (modulo chaperone 
installment)

but there are two classes of violation that can occur.
the first is that a side-effect is thrown within a wrapper function.
call this type A.
the second is an occurrence of one of the five enumerated errors above.
call this type B.

type A depends on the wrapped function and the places it is used.
the arguments not evoking a side-effect corresponds to the client of a 
contract meeting its obligation.
the results not evoking a side-effect corresponds to the provider of a 
contract meeting its obligation.

a particular invocation of a chaperoned procedure is transparent if
- there are no type A errors
- there are no type B errors
- chaperones are recursively discharged (see below)

let's make a chaperone-generating higher-order chaperone:

(define (f g)
  (values (λ (g) (chaperone-procedure g f)) g))

(define h (chaperone-procedure (λ (x) x) f))

(chaperone? (h (λ (x) x)))
(chaperone? ((h (λ (x) x)) (λ (x) x)))

a chaperone is transparent if it has no errors of type A or B and
its results are transparent. (this means that the arguments to the 
original function are transparent within the function (and always, 
in the case of mutation) and the results are transparent in the program.)

example: chaperoned factorial

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

let's try this definition again:

a transparent chaperone is a chaperone that never throws type A errors,
never throws type B errors, and only wraps transparent chaperones.

there is recursion in the definition.

random facts:

type B errors have to do with a misbehaving chaperone. the runtime 
system oversees these.

if the chaperone doesn't misbehave for a particular program, and 
wraps only chaperones that don't misbehave, it can be replaced 
with an impersonator.

type A errors have to do with a misbehaving chaperoned function. the 
chaperone oversees these.

if the chaperone doesn't raise an error for a particular program, 
and wraps only chaperones that don't raise an error, it can be
removed entirely!

with this in mind, what is the precise flow analysis that will allow us
to make these judgements?

first, we need a calculus:

e :=
x
λ <plist> . e
(e e ...)
(chaperone e e)
0 | 1 | ...
#t | #f
(if e e e)
(let ([<plist> e]) e)
(letrec ([<plist> e]) e)
(apply e e)
(values e ...)
+ | - | *
integer?
boolean?
(> e e)
(< e e)
(= e e)
and
or
not
null
null?
cons
pair?
car
cdr

handle [?]
raise (arity-at-least 0)

chaperone? [?]
chaperone-of? [?]


plist :=
empty
x
(cons x plist)

in this language, there are only a few different types of values.
there are procedures, chaperones (a refinement of procedures), integers, 
and booleans.

(letrec ([(fact) (λ (n)
                   (if (= n 0)
                       1
                       (* n (fact (- n 1)))))])
  (chaperone fact (λ (n)
                    (if (or (not (integer? n))
                            (< n 0))
                        (raise)
                        (values (λ (n)
                                  (if (or (not (integer? n))
                                          (< n 0))
                                      (raise)
                                      n))
                                 n)))))

|#

  