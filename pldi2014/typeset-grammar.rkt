#lang racket/base
(require racket/file
         racket/set
         racket/string)

(define (go a)
  (if (eq? (car a) 'grammar)
      (go2 (cdr a))
      (error 'go "not a grammar")))

(define (go2 a)
  (let ([cs (apply seteq (map car a))])
    (string-join (map (go3 cs) a) "\n")))

(define ((go3 cs) a)
  (string-append
   "$"
   (symbol->string (car a))
   "::="
   (string-join
    (map (go4 cs) (cadr a))
    "\\,|\\,")
   "$\n"))

(define ((go4 cs) a)
  (cond
    [(symbol? a)
     (let ([b (symbol->string a)])
       (cond
         [(string=? (substring b 0 1) "\\")
          b]
         [(set-member? cs a)
          b]
         [else
          (go5 a)]))]
    [(boolean? a)
     (if a "\\mathrm{\\#t}" "\\mathrm{\\#f}")]
    [(integer? a)
     (number->string a)]
    [(pair? a)
     (if (eq? (car a) 'LaTeX)
         (string-append
          "{"
          ((go4 cs) (caddr a))
          "}"
          (symbol->string (cadr a))
          "{"
          ((go4 cs) (cadddr a))
          "}")
         (string-append
          "("
          (string-join ((go4* cs) a) "\\,")
          ")"))]
    [(null? a)
     "()"]
    [else
     (error 'go4 "not in it ~a" a)]))

(define ((go4* cs) a)
  (cond
    [(pair? a)
     (cons ((go4 cs) (car a)) ((go4* cs) (cdr a)))]
    [(null? a)
     null]
    [else
     (cons "." (cons ((go4 cs) a) null))]))

(define (go5 a)
  (let ([b (symbol->string a)])
    (if (= (string-length b) 1)
        b
        (string-append
         "\\mathbf{"
         (string-join
          (string-split b "-")
          "\\mhyphen ")
         "}"))))

(current-command-line-arguments (vector "calc0.sexp"))

(for ([filepath (in-vector (current-command-line-arguments))])
  (with-output-to-file (path-replace-suffix filepath ".tex")
    (λ () (display (go (with-input-from-file filepath read))))
    #:exists 'replace))

