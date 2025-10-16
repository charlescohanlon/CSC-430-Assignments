; Full project implemented.
#lang typed/racket
(require typed/rackunit)

;; ====================
;; SHEQ3 language AST structs, types, and utilites
;; ====================

(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct Binop ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)
(struct Ifleq0 ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(define-type ExprC (U NumC IdC FundefC Binop AppC Ifleq0))

; binop-eval: maps a binary operator 
(define (binop-eval [op : Symbol] [l : ExprC] [r : ExprC] [funs : (Listof FundefC)]) : Real
  (match (list (interp l funs) (interp r funs))
    [(list l r)
     (match op
       ['+ (+ l r)]
       ['* (* l r)]
       ['- (- l r)]
       ['/ (cond 
             [(equal? r 0) (error 'binop-eval "SHEQ - division by zero ~a/~a" l r)]
             [else (/ l r)])])]))

(define binop-set '(+ - * /))
(define keyword-set '(def : ifleq0?))

; is-binop?: determines whether the given symbol is a binop symbol or not
(define (is-binop? [s : Symbol]) : Boolean
  (if (member s binop-set)
      #t
      #f))

; is-reserved?: determines whether the given symbol is a reserved keyword or not
(define (is-reserved? [s : Symbol]) : Boolean
  (if (or (is-binop? s) (member s keyword-set))
      #t
      #f))

;; ====================
;; Interpreter
;; ====================

; top-interp: parses a s-expression list of functions and interprets it as a program
(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

; interp-fns: interprets the main function in the list of FundefC funs
(define (interp-fns [funs : (Listof FundefC)]) : Real
  (interp (FundefC-body (fn-lookup 'main funs)) funs))

; interp: interprets an expression given a list of defined functions
(define (interp [expr : ExprC] [funs : (Listof FundefC)]) : Real
  (match expr
    [(NumC n) n]
    [(Binop op l r) (binop-eval op l r funs)]
    [(Ifleq0 test then otherwise)
     (cond 
       [(<= (interp test funs) 0) (interp then funs)]
       [else (interp otherwise funs)])]
    [(AppC fun arg-exprs)
     (match (fn-lookup fun funs)
       [(FundefC _ arg-names body) 
        (cond 
          [(equal? (length arg-names) (length arg-exprs))
           (interp 
            (foldl 
             (lambda ([arg-val : Real] [arg-name : Symbol] [expr : ExprC]) : ExprC
               (subst (NumC arg-val) arg-name expr))
             body
             (map (lambda ([e : ExprC]) (interp e funs)) arg-exprs)
             arg-names) funs)]
          [else (error 'interp "SHEQ - found wrong arity for function call ~a" fun)])])]
    [(IdC s) (error 'interp "SHEQ - undefined identifier ~a" s)]))

; subst: substitute symbols in expressions for other expressions
(define (subst [what : ExprC] [to-replace : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(IdC s)
     (cond 
       [(equal? s to-replace) what]
       [else in])]
    [(Ifleq0 test then otherwise) (Ifleq0 (subst what to-replace test) 
                                          (subst what to-replace then) 
                                          (subst what to-replace otherwise))]
    [(AppC fun args) (AppC fun (map (lambda ([x : ExprC]) (subst what to-replace x)) args))]
    [(Binop o l r) (Binop o (subst what to-replace l) (subst what to-replace r))]))

; fn-lookup: finds a given function in a list of functions
(define (fn-lookup [fun : Symbol] [funs : (Listof FundefC)]) : FundefC
  (match funs
    ['() (error 'fn-lookup "SHEQ - could not find function ~a in function definitions" fun)]
    [(cons (FundefC name args body) rest)
     (cond
       [(equal? name fun) (FundefC name args body)]
       [else (fn-lookup fun rest)])]))

;; ====================
;; Parser
;; ====================

; parse-prog: parses program syntax into list of FundefC structs for ASTs
(define (parse-prog [sexp : Sexp]) : (Listof FundefC)
  (match sexp
    [(? list? fun-sexps) 
     (match (map parse-fundef fun-sexps)
       [(list fundefs ...) (cond
                             [(check-duplicates (map FundefC-name fundefs))
                              (error 'parse-prog "SHEQ - found duplicate function names in program ~a" sexp)]
                             [else fundefs])])]))

; parse-fundef: parses function definition syntax expressions into FundefC structs in the SHEQ3 AST
(define (parse-fundef [sexp : Sexp]) : FundefC
  (match sexp
    [(list 'def (? symbol? name) (list (? symbol? args) ...) ': body)
     (cond 
       [(is-reserved? name)
        (error 'parse-fundef "SHEQ - tried using reserved keyword ~a as a function name" name)]
       [(check-duplicates args)
        (error 'parse-fundef "SHEQ - bad syntax, function ~a has duplicate args" sexp)]
       [else (FundefC name (cast args (Listof Symbol)) (parse body))])]
    [else (error 'parse-fundef "SHEQ - function definition ill-formed: ~a" sexp)]))

; parse: parses a syntax expression into an ExprC
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    [(? symbol? s)
     (cond 
       [(is-reserved? s)
        (error 'parse "SHEQ - tried using a reserved keyword as an identifier, ~a" s)]
       [else (IdC s)])]
    [(list 'ifleq0? other-sexps ...)
     (match other-sexps
       [(list test then otherwise)
        (Ifleq0 (parse test) (parse then) (parse otherwise))]
       [else (error 'parse "SHEQ - ill-formed ifleq0? expression, ~a" sexp)])]
    [(list (? symbol? s) args ...)
     (cond
       [(is-binop? s)
        (match args
          [(list l r) (Binop s (parse l) (parse r))]
          [else (error 'parse "SHEQ - wrong arity for binary operator, got operands ~a" args)])]
       [else (AppC s (map parse args))])]
    [else (error 'parse "SHEQ - expression ill-formed: ~a" sexp)]))

;; ====================
;; Parser and Utility Function Tests
;; ====================

;; is-binop function tests
(check-equal? (is-binop? '/) #t)
(check-equal? (is-binop? 'f) #f)

;; is-reserved function tests
(check-equal? (is-reserved? ':) #t)
(check-equal? (is-reserved? 'f) #f)

;; subst function tests
(check-equal? (subst (NumC 5) 'x (parse '{f x 1})) (parse '{f 5 1}))
(check-equal? (subst (parse '{f x y}) 'x (parse '{f x y})) (parse '{f {f x y} y}))
(check-equal? (subst (parse '{f x y}) 'y (parse '{f {f x y} y})) (parse '{f {f x {f x y}} {f x y}}))

;; fn-lookup function tests
(check-equal? (fn-lookup 'f2 (parse-prog '{{def f (x) : 5}{def f2 (y) : 2}})) 
              (FundefC 'f2 (list 'y) (NumC 2)))
(check-equal? (fn-lookup 'f (parse-prog '{{def f (x) : 5}{def f2 (y) : 2}}))
              (FundefC 'f (list 'x) (NumC 5)))

; ;; parse function tests
(check-equal? (parse '5) (NumC 5))
(check-equal? (parse 'x) (IdC 'x))
(check-equal? (parse '{+ 5 x}) (Binop '+ (NumC 5) (IdC 'x)))
(check-equal? (parse '{f 1 2}) (AppC 'f (list (NumC 1) (NumC 2))))
(check-equal? (parse '{ifleq0? x x {- x 1}}) (Ifleq0 (IdC 'x) (IdC 'x) (Binop '- (IdC 'x) (NumC 1))))
(check-exn #px"SHEQ.*wrong arity" (lambda () (parse '{/ 3 2 1})))
(check-exn #px"SHEQ" (lambda () (parse '{ifleq0? (x 4) then 3 else {+ 2 9} 3})))

;; parse-fundef function tests
(check-equal? (parse-fundef '{def f (x y) : {+ x y}}) (FundefC 'f (list 'x 'y) (parse '{+ x y})))
(check-equal? (parse-fundef '{def five () : 5}) (FundefC 'five '() (parse 5)))
(check-equal? (parse-fundef '{def my-func (x y z) : {+ x {+ y z}}}) 
              (FundefC 'my-func (list 'x 'y 'z) (parse '{+ x {+ y z}})))

;; parse-prog function tests
(check-equal? (parse-prog '{{def f (x y) : {+ x y}}
                            {def five () : 5}})
              (list (parse-fundef '{def f (x y) : {+ x y}}) (parse-fundef '{def five () : 5})))
(check-equal? (parse-prog '{{def name (x) : {* 2 x}}})
              (list (parse-fundef '{def name (x) : {* 2 x}})))

;; ====================
;; Basic Arithmetic Tests
;; ====================

;; Test simple numbers
(check-= (top-interp '{{def main () : 5}})
         5 0.0)

(check-= (top-interp '{{def main () : -10}})
         -10 0.0)

(check-= (top-interp '{{def main () : 0}})
         0 0.0)

;; Test binary operators
(check-= (top-interp '{{def main () : {+ 2 3}}})
         5 0.0)

(check-= (top-interp '{{def main () : {- 5 3}}})
         2 0.0)

(check-= (top-interp '{{def main () : {* 4 5}}})
         20 0.0)

(check-= (top-interp '{{def main () : {/ 10 2}}})
         5 0.0)

;; Test nested arithmetic
(check-= (top-interp '{{def main () : {+ {* 2 3} {- 8 4}}}})
         10 0.0)

(check-= (top-interp '{{def main () : {* {+ 1 2} {/ 12 4}}}})
         9 0.0)

;; Test division by non-integers
(check-= (top-interp '{{def main () : {/ 7 2}}})
         3.5 0)

;; ====================
;; Function Tests - Zero Arguments
;; ====================

(check-= (top-interp '{{def five () : 5}
                       {def main () : {five}}})
         5 0.0)

(check-= (top-interp '{{def zero () : 0}
                       {def main () : {+ {zero} 10}}})
         10 0.0)

;; ====================
;; Function Tests - Single Argument
;; ====================

(check-= (top-interp '{{def double (x) : {* x 2}}
                       {def main () : {double 5}}})
         10 0.0)

(check-= (top-interp '{{def negate (x) : {- 0 x}}
                       {def main () : {negate 7}}})
         -7 0.0)

;; ====================
;; Function Tests - Multiple Arguments
;; ====================

(check-= (top-interp '{{def add (x y) : {+ x y}}
                       {def main () : {add 3 4}}})
         7 0.0)

(check-= (top-interp '{{def area (w h) : {* w h}}
                       {def main () : {area 5 6}}})
         30 0.0)

(check-= (top-interp '{{def sum3 (a b c) : {+ a {+ b c}}}
                       {def main () : {sum3 1 2 3}}})
         6 0.0)

(check-= (top-interp '{{def sum4 (a b c d) : {+ {+ a b} {+ c d}}}
                       {def main () : {sum4 1 2 3 4}}})
         10 0.0)

;; ====================
;; Function Calls with Nested Expressions
;; ====================

(check-= (top-interp '{{def add (x y) : {+ x y}}
                       {def main () : {add {+ 1 2} {* 3 4}}}})
         15 0.0)

(check-= (top-interp '{{def compute (x y z) : {+ {* x y} z}}
                       {def main () : {compute 2 3 4}}})
         10 0.0)

;; ====================
;; Recursive Function Tests
;; ====================

(check-= (top-interp '{{def fact (n) : 
                         {ifleq0? n 
                                  1 
                                  {* n {fact {- n 1}}}}}
                       {def main () : {fact 5}}})
         120 0.0)

(check-= (top-interp '{{def fact (n) : 
                         {ifleq0? n 
                                  1 
                                  {* n {fact {- n 1}}}}}
                       {def main () : {fact 0}}})
         1 0.0)

;; ====================
;; Conditional Tests
;; ====================

(check-= (top-interp '{{def main () : {ifleq0? 0 1 2}}})
         1 0.0)

(check-= (top-interp '{{def main () : {ifleq0? -5 1 2}}})
         1 0.0)

(check-= (top-interp '{{def main () : {ifleq0? 5 1 2}}})
         2 0.0)

(check-= (top-interp '{{def abs (x) : {ifleq0? x {- 0 x} x}}
                       {def main () : {abs -7}}})
         7 0.0)

(check-= (top-interp '{{def abs (x) : {ifleq0? x {- 0 x} x}}
                       {def main () : {abs 7}}})
         7 0.0)

(check-= (top-interp '{{def max (x y) : 
                         {ifleq0? {- x y} y x}}
                       {def main () : {max 3 5}}})
         5 0.0)

; ; Nested conditionals
(check-= (top-interp '{{def sign (x) : 
                         {ifleq0? x 
                                  {ifleq0? {+ x 1} 0 -1} 
                                  1}}
                       {def main () : {sign -5}}})
         0 0.0)

(check-= (top-interp '{{def sign (x) : 
                         {ifleq0? x 
                                  {ifleq0? {+ x 1} 0 -1} 
                                  1}}
                       {def main () : {sign 0}}})
         -1 0.0)

(check-= (top-interp '{{def sign (x) : 
                         {ifleq0? x 
                                  {ifleq0? {+ x 1} 0 -1} 
                                  1}}
                       {def main () : {sign 5}}})
         1 0.0)

;; ====================
;; Mutual Recursion Tests
;; ====================

(check-= (top-interp '{{def even? (n) : 
                         {ifleq0? n 
                                  1 
                                  {odd? {- n 1}}}}
                       {def odd? (n) : 
                         {ifleq0? n 
                                  0 
                                  {even? {- n 1}}}}
                       {def main () : {even? 4}}})
         1 0.0)

(check-= (top-interp '{{def even? (n) : 
                         {ifleq0? n 
                                  1 
                                  {odd? {- n 1}}}}
                       {def odd? (n) : 
                         {ifleq0? n 
                                  0 
                                  {even? {- n 1}}}}
                       {def main () : {odd? 5}}})
         1 0.0)

;; ====================
;; Variable Substitution Tests
;; ====================

(check-= (top-interp '{{def f (x) : {+ x x}}
                       {def g (x y) : {+ {f x} {f y}}}
                       {def main () : {g 3 4}}})
         14 0.0)

;; Shadow parameter names (should work with substitution)
(check-= (top-interp '{{def f (x y) : {+ x y}}
                       {def g (y x) : {f x y}}
                       {def main () : {g 1 2}}})
         3 0.0)

;; ====================
;; Edge Cases
;; ====================

;; Function returning another function call result
(check-= (top-interp '{{def f () : 5}
                       {def g () : {f}}
                       {def main () : {g}}})
         5 0.0)

;; Deeply nested expressions
(check-= (top-interp '{{def main () : 
                         {+ 1 {+ 2 {+ 3 {+ 4 5}}}}}})
         15 0.0)

;; ====================
;; Error Tests - These should raise exceptions
;; ====================

;; Wrong arity - too few arguments
(check-exn #px"SHEQ.*wrong arity"
           (λ () (top-interp '{{def f (x y) : {+ x y}}
                               {def main () : {f 1}}})))

;; Wrong arity - too many arguments  
(check-exn #px"SHEQ.*wrong arity"
           (λ () (top-interp '{{def f (x) : x}
                               {def main () : {f 1 2}}})))

;; Wrong arity - arguments to zero-arg function
(check-exn #px"SHEQ.*wrong arity"
           (λ () (top-interp '{{def f () : 5}
                               {def main () : {f 1}}})))

;; No main function
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f () : 5}})))

;; Duplicate function names
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f () : 5}
                               {def f () : 6}
                               {def main () : {f}}})))

;; Function with reserved keyword name
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def : () : 5}
                               {def main () : {:}}})))

;; Duplicate parameter names  
(check-exn #px"SHEQ.*bad syntax"
           (λ () (top-interp '{{def f (x x) : x}
                               {def main () : {f 1 2}}})))

;; Undefined function
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {undefined-func 5}}})))

;; Undefined variable
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f (x) : y}
                               {def main () : {f 5}}})))

;; Unknown binop
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f (x) : {% 4 x}}
                               {def main () : {f 5}}})))

;; Division by zero
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {/ 5 0}}})))

;; Invalid syntax - missing colon (function ill-formed)
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () 5}})))

;; ill-formed expression
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f () : {{}}}
                              {def main () : {f}}})))
;; Invalid binop syntax - not enough arguments
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {+ 5}}})))

;; Invalid binop syntax - too many arguments  
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {+ 1 2 3}}})))

;; Invalid ifleq0? syntax - missing branches
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {ifleq0? 0 1}}})))

;; Invalid ifleq0? syntax - too many branches
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {ifleq0? 0 1 2 3}}})))

;; Non-numeric operations
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main () : {+ main 5}}})))

;; Reserved word as identifier
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def f (x :) : {+ x :}}
                               {def main () : {f 1 2}}})))

(check-exn #px"SHEQ"
           (λ () (top-interp '{{def def () : 5}
                               {def main () : {def}}})))

;; main with parameters (should error)
(check-exn #px"SHEQ"
           (λ () (top-interp '{{def main (x) : x}})))

;; ====================
;; Complex Integration Tests
;; ====================

;; Fibonacci
(check-= (top-interp '{{def fib (n) : 
                         {ifleq0? n 
                                  1 
                                  {ifleq0? {- n 1} 
                                           1 
                                           {+ {fib {- n 1}} {fib {- n 2}}}}}}
                       {def main () : {fib 6}}})
         13 0.0)

;; Power function
(check-= (top-interp '{{def pow (base exp) : 
                         {ifleq0? exp 
                                  1 
                                  {* base {pow base {- exp 1}}}}}
                       {def main () : {pow 2 5}}})
         32 0.0)

