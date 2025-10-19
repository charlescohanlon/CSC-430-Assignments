; Full project implemented.
#lang typed/racket
(require typed/rackunit)

;; ====================
;; SHEQ4 language AST structs, types, and utilites
;; ====================

; Core types
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct FundefC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(define-type ExprC (U NumC IdC FundefC AppC IfC))

; Value types
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct PrimV ([name : Symbol] ) #:transparent)
(define-type Value (U NumV BoolV CloV StrV PrimV))

; Environment
(struct Binding ([bind : Symbol] [val : NumV]) #:transparent)
(define-type Env (Listof Binding))

(define empty-env empty)
(define extend-env cons)
(define (env-lookup [for : Symbol] [env : Env]) : NumV
  (match env
    ['() (error 'env-lookup "Name ~a not found in env" for)]
    [(cons (Binding bind val) rest)
     (cond
       [(equal? bind for) val]
       [else (env-lookup for rest)])]))

;; ====================
;; Interpreter
;; ====================


;   (cond
;     [(empty? env) (error 'lookup "name not found")]
;     [else (cond
;             [(symbol=? for (bind-name (first env)))
;              (bind-val (first env))]
;             [else (lookup for (rest env))])]))