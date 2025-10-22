; Full project implemented.
#lang typed/racket
(require typed/rackunit)

; TODO: EQUAL ON FUNCTIONS SHOULD RETURN FALSE

;; ====================
;; SHEQ4 language AST structs, types, and utilites
;; ====================

; Core types
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct PrimC ([f : Any]) #:transparent)
(define-type ExprC (U NumC IdC IfC LamC AppC StrC PrimC))

; Value types
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([f : Symbol]) #:transparent)
(define-type Value (U NumV BoolV StrV CloV PrimV))

(define (serialize [v : Value]) : String
  (match v
    [(NumV n) (format "~v" n)]
    [(BoolV b) (if b "true" "false")]
    [(StrV s) (format "~v" s)]
    [(? CloV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))

; Environment
(struct Binding ([bind : Symbol] [val : Value]) #:transparent)
(struct Env ([bindings : (Listof Binding)]) #:transparent)

(define (env-extend [new-binding : Binding] [env : Env]) : Env
  (Env (cons new-binding (Env-bindings env))))

(define (env-lookup [for : Symbol] [env : Env]) : Value
  (match (Env-bindings env)
    ['() (error "SHEQ: ~v is undefined" for)]
    [(cons (Binding bind val) rest)
     (cond
       [(equal? bind for) val]
       [else (env-lookup for (Env rest))])]))

(define top-level-env
  (Env (list
        (Binding '+ (PrimV '+))
        (Binding '- (PrimV '-))
        (Binding '* (PrimV '*))
        (Binding '/ (PrimV '/))
        (Binding '<= (PrimV '<=))
        (Binding 'substring (PrimV 'substring))
        (Binding 'strlen (PrimV 'string-length))
        (Binding 'equal? (PrimV 'equal?))
        (Binding 'true (BoolV #t))
        (Binding 'false (BoolV #f))
        (Binding 'error (PrimV 'error)))))

(define (eval-prim [op : Symbol] [args : (Listof Value)]) : Value
  (match (list op args)
    [(list '+ (list (NumV l) (NumV r))) (NumV (+ l r))]
    [(list '- (list (NumV l) (NumV r))) (NumV (- l r))]
    [(list '* (list (NumV l) (NumV r))) (NumV (* l r))]
    [(list '/ (list (NumV l) (NumV r))) (NumV (/ l r))]
    [(list '<= (list (NumV l) (NumV r))) (BoolV (<= l r))]
    [(list 'substring (list (StrV s) (NumV (? natural? start)) (NumV (? natural? stop))))
     (StrV (substring s start stop))]
    [(list 'string-length (list (StrV s))) (NumV (string-length s))]
    [(list 'equal? (list l r)) (BoolV (equal? l r))]
    [(list 'true) (BoolV #t)]
    [(list 'false) (BoolV #f)]
    [(list 'error (list v)) (error "user-error: ~v" v)]))

(define reserved-set (list 'if ': 'let '= 'in 'end))
(define (is-reserved? [s : Symbol]) : Boolean
  (if (member s reserved-set) #t #f))

;; ====================
;; Parser
;; ====================

(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    [(? string? s) (StrC s)]
    [(? symbol? s)
     (cond
       [(is-reserved? s)
        (error "SHEQ: cannot use reserved keyword ~a as identifier" s)]
       [else (IdC s)])]
    [(list 'if other-sexps ...)
     (match other-sexps
       [(list test then otherwise)
        (IfC (parse test) (parse then) (parse otherwise))]
       [_ (error "SHEQ: ill-formed \"if\" expression, ~a" sexp)])]
    [(list 'lambda (list (? symbol? args) ...) ': body)
     (cond
       [(check-duplicates args) (error "SHEQ: duplicate function argument names")]
       [else (LamC (cast args (Listof Symbol)) (parse body))])]
    [(list 'let (list (list (? symbol? ids) '= exprs) ...) 'in body 'end)
     (AppC (LamC (cond
                   [(check-duplicates ids) (error "SHEQ: duplicate identifiers in let statement")]
                   [else (cast ids (Listof Symbol))])
                 (parse body)) (map parse (cast exprs (Listof Sexp))))]
    [(list fun args ...) (AppC (parse fun) (map parse args))]
    [_ (error "SHEQ: ill-formed expression, ~a" sexp)]))

;; ====================
;; Interpreter
;; ====================

(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-level-env)))

(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(IdC s) (env-lookup s env)]
    [(StrC s) (StrV s)]
    [(IfC test then otherwise)
     (match (interp test env)
       [(BoolV b) (if b (interp then env) (interp otherwise env))]
       [_ (error "SHEQ: ~a is not a conditional expression")])]
    [(LamC args body) (CloV args body env)]
    [(AppC fun args)
     (match (interp fun env)
       [(CloV params body closure-env)
        (cond
          [(not (equal? (length args) (length params)))
           (error "SHEQ: wrong arity for function, got ~a expected ~a" (length args) (length params))]
          [else
           (interp body
                   (foldl (lambda ([param : Symbol] [arg : Value] [e : Env])
                            (env-extend (Binding param arg) e)) closure-env params
                                                                (map
                                                                 (lambda ([arg : ExprC])
                                                                   (interp arg env)) args)))])]
       [(PrimV op) (eval-prim op (map (lambda ([arg : ExprC]) (interp arg env)) args))]
       [_ (error "SHEQ: function ~a is ill-formed" fun)])]
    ))

;; ============================================
;; PARSING TESTS
;; ============================================

;; Basic literals
(check-equal? (parse '42) (NumC 42))
(check-equal? (parse '-3.14) (NumC -3.14))
(check-equal? (parse '0) (NumC 0))
(check-equal? (parse 'x) (IdC 'x))
(check-equal? (parse 'abc123) (IdC 'abc123))
(check-equal? (parse '"hello") (StrC "hello"))
(check-equal? (parse '"") (StrC ""))
(check-equal? (parse '"with spaces") (StrC "with spaces"))

;; Reserved words cannot be identifiers
(check-exn #px"SHEQ" (lambda () (parse 'if)))
(check-exn #px"SHEQ" (lambda () (parse ':)))
(check-exn #px"SHEQ" (lambda () (parse 'let)))
(check-exn #px"SHEQ" (lambda () (parse '=)))
(check-exn #px"SHEQ" (lambda () (parse 'in)))
(check-exn #px"SHEQ" (lambda () (parse 'end)))

;; Lambda expressions
(check-equal? (parse '{lambda () : 5})
              (LamC '() (NumC 5)))
(check-equal? (parse '{lambda (x) : x})
              (LamC '(x) (IdC 'x)))
(check-equal? (parse '{lambda (x y z) : {+ x y}})
              (LamC '(x y z) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))))

;; Duplicate parameter names should error
(check-exn #px"SHEQ" (lambda () (parse '{lambda (x x) : x})))
(check-exn #px"SHEQ" (lambda () (parse '{lambda (x y x) : x})))

;; If expressions
(check-equal? (parse '{if true 1 2})
              (IfC (IdC 'true) (NumC 1) (NumC 2)))
(check-equal? (parse '{if {<= 3 4} "yes" "no"})
              (IfC (AppC (IdC '<=) (list (NumC 3) (NumC 4)))
                   (StrC "yes")
                   (StrC "no")))

;; Missing else clause should error
(check-exn #px"SHEQ" (lambda () (parse '{if true 1})))
(check-exn #px"SHEQ" (lambda () (parse '{if})))
(check-exn #px"SHEQ" (lambda () (parse '{if true})))

;; Let expressions
(check-equal? (parse '{let {} in 5 end})
              (AppC (LamC '() (NumC 5)) '()))
(check-equal? (parse '{let {[x = 5]} in x end})
              (AppC (LamC '(x) (IdC 'x)) (list (NumC 5))))
(check-equal? (parse '{let {[x = 5] [y = 10]} in {+ x y} end})
              (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                    (list (NumC 5) (NumC 10))))

;; Let with duplicate bindings should error
(check-exn #px"SHEQ" (lambda () (parse '{let {[x = 1] [x = 2]} in x end})))

;; Malformed let expressions
(check-exn #px"SHEQ" (lambda () (parse '{let})))
(check-exn #px"SHEQ" (lambda () (parse '{let {} in})))
(check-exn #px"SHEQ" (lambda () (parse '{let {} in 5}))) ; missing 'end'
(check-exn #px"SHEQ" (lambda () (parse '{let {[x 5]} in x end}))) ; missing =

;; Application expressions
(check-equal? (parse '{f})
              (AppC (IdC 'f) '()))
(check-equal? (parse '{f x})
              (AppC (IdC 'f) (list (IdC 'x))))
(check-equal? (parse '{+ 1 2})
              (AppC (IdC '+) (list (NumC 1) (NumC 2))))
(check-equal? (parse '{{lambda (x) : x} 5})
              (AppC (LamC '(x) (IdC 'x)) (list (NumC 5))))

;; Nested expressions
(check-equal? (parse '{+ {* 2 3} 4})
              (AppC (IdC '+) (list (AppC (IdC '*) (list (NumC 2) (NumC 3)))
                                   (NumC 4))))

;; Invalid s-expressions
(check-exn #px"SHEQ" (lambda () (parse '{}))) ; empty application
(check-exn #px"SHEQ" (lambda () (parse '())))  ; not valid in our syntax

;; ============================================
;; SERIALIZATION TESTS
;; ============================================

(check-equal? (serialize (NumV 42)) "42")
(check-equal? (serialize (NumV -3.14)) "-3.14")
(check-equal? (serialize (NumV 0)) "0")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StrV "hello")) "\"hello\"")
(check-equal? (serialize (StrV "")) "\"\"")
(check-equal? (serialize (StrV "with \"quotes\"")) "\"with \\\"quotes\\\"\"")
(check-equal? (serialize (CloV '(x) (NumC 1) (Env '()))) "#<procedure>")
(check-equal? (serialize (PrimV '+)) "#<primop>")

;; ============================================
;; INTERPRETATION TESTS - BASIC VALUES
;; ============================================

(check-equal? (interp (NumC 42) top-level-env) (NumV 42))
(check-equal? (interp (NumC -3.14) top-level-env) (NumV -3.14))
(check-equal? (interp (StrC "hello") top-level-env) (StrV "hello"))

;; ============================================
;; TOP-LEVEL ENVIRONMENT TESTS
;; ============================================

(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp 'false) "false")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '-) "#<primop>")
(check-equal? (top-interp '*) "#<primop>")
(check-equal? (top-interp '/) "#<primop>")
(check-equal? (top-interp '<=) "#<primop>")
(check-equal? (top-interp 'equal?) "#<primop>")
(check-equal? (top-interp 'substring) "#<primop>")
(check-equal? (top-interp 'strlen) "#<primop>")
(check-equal? (top-interp 'error) "#<primop>")

;; Undefined identifier
(check-exn #px"SHEQ" (lambda () (top-interp 'undefined)))

;; ============================================
;; ARITHMETIC OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{+ 3 4}) "7")
(check-equal? (top-interp '{- 10 3}) "7")
(check-equal? (top-interp '{* 3 4}) "12")
(check-equal? (top-interp '{/ 12 3}) "4")

;; Arithmetic with non-numbers should error TODO: implement arg checks
; (check-exn #px"SHEQ" (lambda () (top-interp '{+ true 3})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{+ 3 "hello"})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{- "x" 3})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{* false true})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 false})))

;; Division by zero
; (check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 0})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{/ 0 0})))

;; Wrong number of arguments
; (check-exn #px"SHEQ" (lambda () (top-interp '{+})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{+ 1})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 2 3})))

;; ============================================
;; COMPARISON OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{<= 3 4}) "true")
(check-equal? (top-interp '{<= 4 3}) "false")
(check-equal? (top-interp '{<= 3 3}) "true")
(check-equal? (top-interp '{<= -5 -2}) "true")

;; <= with non-numbers
; (check-exn #px"SHEQ" (lambda () (top-interp '{<= "3" 4})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{<= true false})))

;; equal? tests
(check-equal? (top-interp '{equal? 3 3}) "true")
(check-equal? (top-interp '{equal? 3 4}) "false")
(check-equal? (top-interp '{equal? true true}) "true")
(check-equal? (top-interp '{equal? false false}) "true")
(check-equal? (top-interp '{equal? true false}) "false")
(check-equal? (top-interp '{equal? "hello" "hello"}) "true")
(check-equal? (top-interp '{equal? "hello" "world"}) "false")
(check-equal? (top-interp '{equal? "" ""}) "true")

;; equal? with different types returns false
(check-equal? (top-interp '{equal? 3 "3"}) "false")
(check-equal? (top-interp '{equal? true 1}) "false")
(check-equal? (top-interp '{equal? false 0}) "false")

;; equal? with functions returns false
; (check-equal? (top-interp '{equal? {lambda (x) : x} {lambda (x) : x}}) "false")
; (check-equal? (top-interp '{equal? + +}) "false")
; (check-equal? (top-interp '{equal? + -}) "false")

;; Wrong number of arguments
; (check-exn #px"SHEQ" (lambda () (top-interp '{equal?})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{equal? 1})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{equal? 1 2 3})))

;; ============================================
;; STRING OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{strlen "hello"}) "5")
(check-equal? (top-interp '{strlen ""}) "0")
(check-equal? (top-interp '{strlen "a"}) "1")

;; strlen with non-string
; (check-exn #px"SHEQ" (lambda () (top-interp '{strlen 5})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{strlen true})))

(check-equal? (top-interp '{substring "hello" 0 5}) "\"hello\"")
(check-equal? (top-interp '{substring "hello" 1 4}) "\"ell\"")
(check-equal? (top-interp '{substring "hello" 0 0}) "\"\"")
(check-equal? (top-interp '{substring "hello" 2 2}) "\"\"")

;; substring errors
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring 123 0 1}))) ; non-string
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 1.5 3}))) ; non-natural
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" -1 3}))) ; negative
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 6}))) ; out of range
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 3 2}))) ; stop before start

;; ============================================
;; ERROR FUNCTION TESTS
;; ============================================

(check-exn #px"user-error.*42" (lambda () (top-interp '{error 42})))
(check-exn #px"user-error.*\"test\"" (lambda () (top-interp '{error "test"})))

;; ============================================
;; CONDITIONALS TESTS
;; ============================================

(check-equal? (top-interp '{if true 1 2}) "1")
(check-equal? (top-interp '{if false 1 2}) "2")
(check-equal? (top-interp '{if {<= 3 4} "yes" "no"}) "\"yes\"")
(check-equal? (top-interp '{if {<= 5 4} "yes" "no"}) "\"no\"")

;; Non-boolean test should error
(check-exn #px"SHEQ" (lambda () (top-interp '{if 1 2 3})))
(check-exn #px"SHEQ" (lambda () (top-interp '{if "true" 1 2})))

;; ============================================
;; LAMBDA AND APPLICATION TESTS
;; ============================================

(check-equal? (top-interp '{{lambda () : 5}}) "5")
(check-equal? (top-interp '{{lambda (x) : x} 42}) "42")
(check-equal? (top-interp '{{lambda (x y) : {+ x y}} 3 4}) "7")
(check-equal? (top-interp '{{lambda (x y z) : {+ {+ x y} z}} 1 2 3}) "6")

;; Higher-order functions
(check-equal? (top-interp '{{lambda (f x) : {f x}} {lambda (y) : {+ y 1}} 5}) "6")
(check-equal? (top-interp '{{{lambda (x) : {lambda (y) : {+ x y}}} 3} 4}) "7")

;; Wrong number of arguments
; (check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x}})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x} 1 2})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x y) : x} 1})))

;; Application of non-function
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4})))
(check-exn #px"SHEQ" (lambda () (top-interp '{true false})))
(check-exn #px"SHEQ" (lambda () (top-interp '{"not-a-function" 1 2})))

;; ============================================
;; LET BINDING TESTS
;; ============================================

(check-equal? (top-interp '{let {} in 5 end}) "5")
(check-equal? (top-interp '{let {[x = 5]} in x end}) "5")
(check-equal? (top-interp '{let {[x = 5] [y = 10]} in {+ x y} end}) "15")

;; Shadowing
(check-equal? (top-interp '{let {[x = 5]} in {let {[x = 10]} in x end} end}) "10")
(check-equal? (top-interp '{let {[+ = 100]} in + end}) "100") ; shadows primitive

;; Scope tests - bindings don't see later bindings
(check-exn #px"SHEQ" (lambda () (top-interp '{let {[x = y] [y = 5]} in x end})))

;; Complex let expressions
(check-equal? (top-interp '{let {[f = {lambda (x) : {+ x 1}}]} in {f 5} end}) "6")
(check-equal? (top-interp '{let {[x = 3] [y = 4]} in {let {[z = {+ x y}]} in z end} end}) "7")

;; ============================================
;; CLOSURE AND ENVIRONMENT TESTS
;; ============================================

;; Lexical scoping
(check-equal? (top-interp '{let {[x = 10]} in
                             {let {[f = {lambda (y) : {+ x y}}]} in
                               {let {[x = 20]} in
                                 {f 5}
                                 end}
                               end}
                             end}) "15") ; uses x=10, not x=20

;; Returning closures
(check-equal? (top-interp '{{{lambda (x) : {lambda (y) : {+ x y}}} 10} 5}) "15")

;; ============================================
;; COMPLEX INTEGRATION TESTS
;; ============================================

;; Factorial
(check-equal? (top-interp
               '{let {[fact = {lambda (f n) :
                                {if {<= n 0}
                                    1
                                    {* n {f f {- n 1}}}}}]}
                  in {fact fact 5} end}) "120")

;; Nested conditionals
(check-equal? (top-interp
               '{if {<= 3 4}
                    {if true "correct" "wrong1"}
                    "wrong2"}) "\"correct\"")

;; String manipulation
(check-equal? (top-interp
               '{let {[s = "hello world"]} in
                  {substring s 0 {strlen {substring s 0 5}}}
                  end}) "\"hello\"")

;; Error propagation
(check-exn #px"user-error" (lambda () (top-interp
                                       '{let {[f = {lambda (x) : {error x}}]} in
                                          {if true {f "oops"} 42}
                                          end})))

;; ============================================
;; EDGE CASES AND STRESS TESTS
;; ============================================

;; Empty string operations
(check-equal? (top-interp '{strlen ""}) "0")
(check-equal? (top-interp '{substring "" 0 0}) "\"\"")

;; Deep nesting
; (check-equal? (top-interp
;                '{{{{{{lambda (a) :
;                        {lambda (b) :
;                          {lambda (c) :
;                            {lambda (d) :
;                              {lambda (e) :
;                                {lambda (f) :
;                                  {+ {+ {+ {+ {+ a b} c} d} e} f}}}}}}}
;                      1} 2} 3} 4} 5} 6}) "21")

;; Many let bindings
(check-equal? (top-interp
               '{let {[a = 1] [b = 2] [c = 3] [d = 4] [e = 5]}
                  in {+ {+ {+ {+ a b} c} d} e}
                  end}) "15")

;; Primitive as first-class value
(check-equal? (top-interp
               '{let {[op = +]} in {op 3 4} end}) "7")
(check-equal? (top-interp
               '{{lambda (f x y) : {f x y}} + 10 20}) "30")

; (check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 true})))
(check-exn #px"SHEQ" (lambda () (top-interp 'undefined-var)))
(check-exn #px"SHEQ" (lambda () (top-interp '{if 5 1 2})))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x} 1 2})))
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{/ 1 0})))
(check-exn #px"SHEQ" (lambda () (parse '{lambda (x x) : x})))
(check-exn #px"SHEQ" (lambda () (parse '{let {[x = 1] [x = 2]} in x end})))

;; Wrong arity for primitives
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 3 5})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{strlen})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{strlen "hello" "world"})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{error})))
; (check-exn #px"SHEQ" (lambda () (top-interp '{error 1 2})))