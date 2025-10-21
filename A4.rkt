; Full project implemented.
#lang typed/racket
(require typed/rackunit)

; TODO:
;   1. Do we type check the arguments to PrimVs or just check arity?
;   2. Are the top-level-env names keywords?
;   3. StrC and BoolC for string and boolean literals?
;   4. Need BoolC StrC and PrimC? How would get to them in interp? How would evaluate Prims in inter?

;; ====================
;; SHEQ4 language AST structs, types, and utilites
;; ====================

; Core types
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct BoolC ([b : Boolean]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct PrimC ([f : Any]) #:transparent)
(define-type ExprC (U NumC IdC IfC LamC AppC BoolC StrC PrimC))

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
    [(StrV s) (format "\"~v\"" s)]
    [(? CloV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))

; Environment
(struct Binding ([bind : Symbol] [val : Value]) #:transparent)
(struct Env ([bindings : (Listof Binding)]) #:transparent)

(define (env-extend [new-binding : Binding] [env : Env]) : Env
  (Env (cons new-binding (Env-bindings env))))

(define (env-lookup [for : Symbol] [env : Env]) : Value
  (match env
    ['() (error "SHEQ: ~a is undefined" for)]
    [(cons (Binding bind val) rest)
     (cond
       [(equal? bind for) val]
       [else (env-lookup for rest)])]))

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
    [(list 'substring (list (StrV s) (NumV start) (NumV stop)))
     (StrV (substring s (cast start Integer) (cast stop Integer)))] ; Cast to integers?
    [(list 'strlen (list (StrV s))) (NumV (string-length s))]
    [(list 'equal? (list l r)) (BoolV (equal? l r))]
    [(list 'true) (BoolV #t)]
    [(list 'false) (BoolV #f)]
    [(list 'error (list v)) (error "~v" v)]))
; TODO: need to check arity and argument types here


(define reserved-set (list 'if ': 'let '= 'in 'end))
(define (is-reserved? [s : Symbol]) : Boolean
  (if (member s reserved-set) #t #f))

;; ====================
;; Parser
;; ====================

(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
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
    [(list fun args ...) (AppC (parse fun) (map parse args))]
    [_ (error "SHEQ: ill-formed expression, ~a" sexp)]))

;; ====================
;; Interpreter
;; ====================

(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(IdC s) (env-lookup s env)]
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


; (AppC
;  (LamC '(f) (AppC (IdC 'f) (list (NumC 1) (NumC 2))))
;  (list (LamC '(x y) (IdC 'x))))

; {{lambda (x y) : x} 1}
(AppC (LamC '(x y) (IdC 'x)) (list (NumC 1)))

; TODO: write a SHEQ3 program in SHEQ4 and ask Brian about it



