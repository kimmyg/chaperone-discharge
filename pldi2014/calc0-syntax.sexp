(grammar
 [e ((e e ...)
     (app-values e e)
     (chaperone-procedure e e e)
     (impersonate-procedure e e e)
     (let ([s e]) e)
     (letrec ([s e]) e)
     (λ s e)
     (if e e e)
     (or e e)
     (and e e)
     (raise)
     v
     x)]
 [v (p n b)]
 [p (= < > + - * values integer? boolean? null null? cons pair? car cdr)]
 [n (0 1 -1 2 -2 ...)]
 [b (#t #f)]
 [s (x () (x . s))])
