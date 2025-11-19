; Full project implemented.
#lang typed/racket
(require typed/rackunit)

; TODO: VoidT, no Null?
; Top-level lambda doesn't have a return type annotation?

;; ====================
;; SHEQ7 language AST structs, types, and utilites
;; ====================

; Core AS
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [arg-types : (Listof Type)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct AssignC ([var : Symbol] [val : ExprC]) #:transparent)
(struct SeqC ([exprs : (Listof ExprC)]) #:transparent)
(define-type ExprC (U NumC IdC IfC LamC AppC StrC AssignC SeqC))

; Value AS
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([f : Symbol]) #:transparent)
(struct NullV () #:transparent)
(struct ArrayV ([sto-pos : Natural] [len : Natural]) #:transparent)
(define-type Value (U NumV BoolV StrV CloV PrimV NullV ArrayV))

; Type AS
(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct StrT () #:transparent)
(struct NumarrayT () #:transparent)
(struct VoidT () #:transparent)
(struct ->T ([args : (Listof Type)] [return-val : Type]) #:transparent)
(define-type Type (U NumT BoolT StrT NumarrayT VoidT ->T))

; Environment
(struct Binding ([bind : Symbol] [idx : Natural]) #:transparent)
(struct Env ([bindings : (Listof Binding)]) #:transparent)

; env-extend: adds a new binding to a given environment
(define (env-extend [new-binding : Binding] [env : Env]) : Env
  (Env (cons new-binding (Env-bindings env))))

; env-lookup: looks for a given symbol bound in an environment
(define (env-lookup [for : Symbol] [env : Env]) : Natural
  (match (Env-bindings env)
    ['() (error (format "SHEQ: ~v is undefined" for))]
    [(cons (Binding bind pos) rest)
     (cond
       [(equal? bind for) pos]
       [else (env-lookup for (Env rest))])]))

(define base-env
  (Env (list
        ; 0 reserved for free location indicator
        (Binding '+ 1)
        (Binding '- 2)
        (Binding '* 3)
        (Binding '/ 4)
        (Binding '<= 5)
        (Binding 'num-eq? 6)
        (Binding 'str-eq? 7)
        (Binding 'substring 8)
        (Binding 'strlen 9)
        (Binding 'true 10)
        (Binding 'false 11)
        (Binding 'make-array 12)
        (Binding 'aref 13)
        (Binding 'aset! 14)
        (Binding 'alen 15))))

(struct Store ([vals : (Vectorof Value)] [memsize : Natural]) #:transparent)

; make-init-sto: creates the initial store with a specific size memsize
(define (make-init-sto [memsize : Natural]) : Store
  (define init-sto
    ; First position is used to indicated index of next free location.
    (Store (vector (NullV)
                   (PrimV '+)
                   (PrimV '-)
                   (PrimV '*)
                   (PrimV '/)
                   (PrimV '<=)
                   (PrimV 'num-eq?)
                   (PrimV 'str-eq?)
                   (PrimV 'substring)
                   (PrimV 'string-length)
                   (BoolV #t)
                   (BoolV #f)
                   (PrimV 'make-array)
                   (PrimV 'aref)
                   (PrimV 'aset!)
                   (PrimV 'alen)) memsize))
  (cond
    [(< memsize (vector-length (Store-vals init-sto)))
     ; Error if size is less than the number of initial bindings
     (error (format "SHEQ: initial storage size ~a is too small" memsize))]
    [else
     (begin
       ; Set first position to current length so it indicates next free location
       (vector-set! (Store-vals init-sto) 0 (NumV (vector-length (Store-vals init-sto))))
       ; Extend storage to requested size
       (Store (vector-append
               (Store-vals init-sto)
               (ann (make-vector
                     (- memsize (vector-length (Store-vals init-sto))) (NullV)) (Vectorof Value))) memsize))]))

; read-store: retrieves the value at a given position from a given store
(define (read-store [pos : Natural] [sto : Store]) : Value
  (vector-ref (Store-vals sto) pos))

; allocate: allocates a new location in sto for a value provided there's enough memory remaining
(define (allocate [val : Value] [sto : Store]) : Natural
  (match (vector-ref (Store-vals sto) 0)
    [(NumV free-pos)
     (match free-pos
       [(? natural? free-pos)
        (cond
          [(< free-pos (Store-memsize sto))
           (begin
             (vector-set! (Store-vals sto) free-pos val)
             (vector-set! (Store-vals sto) 0 (NumV (+ free-pos 1)))
             free-pos)]
          [else
           (error (format "SHEQ: cannot allocate ~a, exceeded memory of size ~a"
                          (serialize val) (Store-memsize sto)))])])]))

; Type Env
(struct TBinding ([bind : Symbol] [type : Type]) #:transparent)
(struct TEnv ([bindings : (Listof TBinding)]) #:transparent)

; tenv-extend: adds a new type binding to a given type environment
(define (tenv-extend [new-binding : TBinding] [tenv : TEnv]) : TEnv
  (TEnv (cons new-binding (TEnv-bindings tenv))))

; tenv-lookup: looks for a given symbol bound in a type environment
(define (tenv-lookup [for : Symbol] [tenv : TEnv]) : Type
  (match (TEnv-bindings tenv)
    ['() (error (format "SHEQ: ~v is undefined" for))]
    [(cons (TBinding bind type) rest)
     (cond
       [(equal? bind for) type]
       [else (tenv-lookup for (TEnv rest))])]))

(define base-tenv
  (TEnv (list
         ; 0 reserved for free location indicator
         (TBinding '+ (->T (list (NumT) (NumT)) (NumT)))
         (TBinding '- (->T (list (NumT) (NumT)) (NumT)))
         (TBinding '* (->T (list (NumT) (NumT)) (NumT)))
         (TBinding '/ (->T (list (NumT) (NumT)) (NumT)))
         (TBinding '<= (->T (list (NumT) (NumT)) (BoolT)))
         (TBinding 'num-eq? (->T (list (NumT) (NumT)) (BoolT)))
         (TBinding 'str-eq? (->T (list (StrT) (StrT)) (BoolT)))
         (TBinding 'substring (->T (list (StrT) (NumT) (NumT)) (StrT)))
         (TBinding 'strlen (->T (list (StrT)) (NumT)))
         (TBinding 'true (BoolT))
         (TBinding 'false (BoolT))
         (TBinding 'make-array (->T (list (NumT) (NumT)) (NumarrayT)))
         (TBinding 'aref (->T (list (NumarrayT) (NumT)) (NumT)))
         (TBinding 'aset! (->T (list (NumarrayT) (NumT) (NumT)) (VoidT)))
         (TBinding 'alen (->T (list (NumarrayT)) (NumT))))))

; serialize: produces a string representation of a given value
(define (serialize [v : Value]) : String
  (match v
    [(NumV n) (format "~v" n)]
    [(BoolV b) (if b "true" "false")]
    [(StrV s) (format "~v" s)]
    [(? CloV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]
    [(? ArrayV?) "#<array>"]
    [(? NullV?) "null"]))

; eval-prim: evaluates primative operations
(define (eval-prim [op : Symbol] [args : (Listof Value)] [env : Env] [sto : Store]) : Value
  (match (list op args)
    ;; Binary ops
    [(list '+ (list (NumV l) (NumV r))) (NumV (+ l r))]
    [(list '- (list (NumV l) (NumV r))) (NumV (- l r))]
    [(list '* (list (NumV l) (NumV r))) (NumV (* l r))]
    [(list '/ (list (NumV l) (NumV r)))
     (cond
       [(zero? r) (error (format "SHEQ: division by zero ~a/~a" l r))]
       [else (NumV (/ l r))])]
    [(list '<= (list (NumV l) (NumV r))) (BoolV (<= l r))]

    ;; String ops
    [(list 'substring (list (StrV s) (NumV start) (NumV stop)))
     (cond
       [(or (not (exact-integer? start))
            (not (exact-integer? stop))
            (< start 0)
            (< stop start)
            (> stop (string-length s)))
        (error (format "SHEQ: invalid substring range ~a ~a ~a" s start stop))]
       [else (StrV (substring s (exact-round start) (exact-round stop)))])]
    [(list 'string-length (list (StrV s))) (NumV (string-length s))]

    ;; Equality
    [(list 'num-eq? (list l r))
     (cond
       [(and (NumV? l) (NumV? r)) (BoolV (equal? (NumV-n l) (NumV-n r)))]
       [else (error (format "SHEQ: num-eq? expects numbers, got ~a and ~a" (serialize l) (serialize r)))])]

    [(list 'str-eq? (list l r))
     (cond
       [(and (StrV? l) (StrV? r)) (BoolV (equal? (StrV-s l) (StrV-s r)))]
       [else (error (format "SHEQ: str-eq? expects strings, got ~a and ~a" (serialize l) (serialize r)))])]

    [(list 'make-array (list (NumV len) elm))
     (cond
       [(and (natural? len) (>= len 1)) (make-array len elm sto)]
       [else (error (format "SHEQ: cannot create array of length ~a" len))])]

    [(list 'aref (list (? ArrayV? arr) (NumV i)))
     (cond
       [(not (natural? i)) (error (format "SHEQ: index ~a must be a non-negative integer" i))]
       [(>= i (ArrayV-len arr))
        (error (format "SHEQ: index ~a out of bounds for array length ~a" i (ArrayV-len arr)))]
       [else (aref arr i sto)])]

    [(list 'aset! (list (? ArrayV? arr) (NumV i) val))
     (cond
       [(not (natural? i)) (error (format "SHEQ: index ~a must be a non-negative integer" i))]
       [(>= i (ArrayV-len arr))
        (error (format "SHEQ: index ~a out of bounds for array length ~a" i (ArrayV-len arr)))]
       [else (aset! arr i val sto)])]

    [(list 'alen (list (? ArrayV? arr)))
     (NumV (ArrayV-len arr))]

    ;; Catch-all for any other wrong arity/type
    [_ (error (format "SHEQ: bad primitive application ~a with args ~a" op args))]))

(define reserved-set (list 'if 'let 'rlet '= 'lambda ': '-> 'in 'end 'seq))
; is-reserved: determines if the given symbols is in the set of reserved keywords
(define (is-reserved? [s : Symbol]) : Boolean
  (if (member s reserved-set) #t #f))

; make-array: creates arrays of given length filled with given element
(define (make-array [len : Natural] [elm : Value] [sto : Store]) : ArrayV
  (match (vector-ref (Store-vals sto) 0)
    [(NumV (? natural? free-pos))
     (define new-array (ArrayV free-pos len))
     (define (repeat-alloc [i : Integer]) : Void
       (cond
         [(> i 0) (begin (allocate elm sto) (repeat-alloc (- i 1)))]))
     (begin
       (repeat-alloc len)
       new-array)]))

; aref: returns an element of an array
(define (aref [arr : ArrayV] [pos : Natural] [sto : Store]) : Value
  (define idx (+ (ArrayV-sto-pos arr) pos))
  (vector-ref (Store-vals sto) idx))

; aref: returns an element of a given array
(define (aset! [arr : ArrayV] [pos : Natural] [val : Value] [sto : Store]) : NullV
  (define idx (+ (ArrayV-sto-pos arr) pos))
  (begin
    (vector-set! (Store-vals sto) idx val)
    (NullV)))

;; ====================
;; Type Checking
;; ====================

(define (parse-type [sexp : Sexp]) : Type
  (match sexp
    ['num (NumT)]
    ['bool (BoolT)]
    ['str (StrT)]
    ['numarray (NumarrayT)]
    ['void (VoidT)]
    [(list args ... '-> return)
     (->T (map parse-type (cast args (Listof Sexp))) (parse-type return))]
    [_ (error (format "SHEQ: unrecognized type ~a" sexp))]))

(define (type-check [expr : ExprC] [tenv : TEnv]) : Type
  (match expr
    [(NumC _) (NumT)]
    [(StrC _) (StrT)]
    [(IdC s) (tenv-lookup s tenv)]
    [(IfC test then otherwise)
     (define test-type (type-check test tenv))
     (define then-type (type-check then tenv))
     (define else-type (type-check otherwise tenv))
     (if (and (BoolT? test-type) (equal? then-type else-type))
         then-type
         (error "SHEQ: type error in if expression"))]
    [(LamC args arg-types body)
     (define extended-tenv (foldl
                            (lambda ([arg : Symbol] [arg-type : Type] [tenv-to-extend : TEnv])
                              (tenv-extend (TBinding arg arg-type) tenv-to-extend))
                            tenv args arg-types))
     (define body-type (type-check body extended-tenv))
     (->T arg-types body-type)]
    [(AppC fun args)
     (define fun-type (type-check fun tenv))
     (define arg-types (map (lambda ([arg : ExprC]) (type-check arg tenv)) args))
     (match fun-type
       [(->T param-types ret-type)
        (if (equal? param-types arg-types)
            ret-type
            (error "SHEQ: function argument types do not match"))]
       [_ (error "SHEQ: application of non-function")])]
    [(AssignC var val)
     (define var-type (tenv-lookup var tenv))
     (define val-type (type-check val tenv))
     (if (equal? var-type val-type)
         (VoidT)
         (error "SHEQ: type mismatch in assignment"))]
    [(SeqC exprs)
     ; Type check all expressions, return type of last one
     (define types (map (lambda ([e : ExprC]) (type-check e tenv)) exprs))
     (last types)]))

;; ====================
;; Parser
;; ====================

; parse: parses given s-expression into an AST
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    [(? string? s) (StrC s)]
    [(? symbol? s)
     (cond
       [(is-reserved? s)
        (error (format "SHEQ: cannot use reserved keyword ~a as identifier" s))]
       [else (IdC s)])]
    [(list 'if other-sexps ...)
     (match other-sexps
       [(list test then otherwise)
        (IfC (parse test) (parse then) (parse otherwise))]
       [_ (error (format "SHEQ: ill-formed \"if\" expression, ~a" sexp))])]
    [(list 'lambda (list (list type-annots args) ...) ': body)
     (cond
       [(ormap is-reserved? (cast args (Listof Symbol)))
        (error "SHEQ: cannot use reserved keyword as function argument name")]
       [(check-duplicates args) (error "SHEQ: duplicate function argument names")]
       [else (LamC (cast args (Listof Symbol))
                   (map parse-type (cast type-annots (Listof Sexp)))
                   (parse body))])]
    [(list 'let other-sexps ...)
     (match other-sexps
       [(list (list (list type-annots ids '= exprs) ...) 'in body 'end)
        (AppC (LamC (cond
                      [(ormap is-reserved? (cast ids (Listof Symbol)))
                       (error "SHEQ: cannot use reserved keyword as identifier in let statement")]
                      [(check-duplicates (cast ids (Listof Symbol))) (error "SHEQ: duplicate identifiers in let statement")]
                      [else (cast ids (Listof Symbol))])
                    (map parse-type (cast type-annots (Listof Sexp)))
                    (parse body)) (map parse (cast exprs (Listof Sexp))))]
       [_ (error (format "SHEQ: ill-formed \"let\" expression, ~a" sexp))])]
    [(list (? symbol? s) ':= val-sexp) (AssignC s (parse val-sexp))]
    [(list 'seq exprs ...)
     (cond
       [(empty? exprs) (error (format "SHEQ: seq requires at least one expression"))]
       [else (SeqC (map parse exprs))])]
    [(list fun args ...) (AppC (parse fun) (map parse args))]
    [_ (error (format "SHEQ: ill-formed expression, ~a" sexp))]))

;; ====================
;; Interpreter
;; ====================

; top-interp: intializes program parsing and interpreting, given an s-expression
(define (top-interp [s : Sexp]) : String
  (define ast (parse s))
  (begin
    (type-check ast base-tenv)
    (serialize (interp ast base-env (make-init-sto 2000)))))

; interp: interpretes an AST given an environment and store
(define (interp [expr : ExprC] [env : Env] [sto : Store]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(IdC s) (read-store (env-lookup s env) sto)]
    [(StrC s) (StrV s)]
    [(IfC test then otherwise)
     (match (interp test env sto)
       [(BoolV b) (if b (interp then env sto) (interp otherwise env sto))]
       [_ (error (format "SHEQ: ~a is not a conditional expression" test))])]
    [(LamC args _ body) (CloV args body env)]
    [(AssignC var val)
     (define loc (env-lookup var env))
     (define new-val (interp val env sto))
     (begin
       (vector-set! (Store-vals sto) loc new-val)
       (NullV))]
    [(SeqC exprs)
     ; Evaluate all expressions in order, return last value
     (define values (map (lambda ([e : ExprC]) (interp e env sto)) exprs))
     (last values)]
    [(AppC fun args)
     (match (interp fun env sto)
       [(CloV params body closure-env)
        (cond
          [(not (equal? (length args) (length params)))
           (error (format "SHEQ: wrong arity for function, got ~a expected ~a"
                          (length args) (length params)))]
          [else
           (interp body
                   (foldl (lambda ([param : Symbol] [arg : Value] [e : Env])
                            (env-extend
                             (Binding param (allocate arg sto)) e))
                          closure-env params
                          (map
                           (lambda ([arg : ExprC])
                             (interp arg env sto)) args)) sto)])]
       [(PrimV op) (eval-prim op (map (lambda ([arg : ExprC]) (interp arg env sto)) args) env sto)]
       [_ (error (format "SHEQ: function ~a is ill-formed" fun))])]))

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
(check-exn #px"SHEQ" (lambda () (parse 'in)))
(check-exn #px"SHEQ" (lambda () (parse 'end)))
(check-exn #px"SHEQ" (lambda ()
                       (top-interp
                        '{let {[str let = ""]} in "World" end})))
(check-exn #px"SHEQ" (lambda ()
                       (top-interp
                        '{lambda ([str let]) : let})))

;; Duplicate parameter names should error
(check-exn #px"SHEQ" (lambda () (parse '{lambda ([num x] [num x]) : x})))
(check-exn #px"SHEQ" (lambda () (parse '{lambda ([num x] [str y] [num x]) : x})))

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

;; Let with duplicate bindings should error
(check-exn #px"SHEQ" (lambda () (parse '{let {[num x = 1] [num x = 2]} in x end})))

;; Malformed let expressions
(check-exn #px"SHEQ" (lambda () (parse '{let})))
(check-exn #px"SHEQ" (lambda () (parse '{let {} in})))
(check-exn #px"SHEQ" (lambda () (parse '{let {} in 5}))) ; missing 'end'
(check-exn #px"SHEQ" (lambda () (parse '{let {[num x 5]} in x end}))) ; missing =

;; Application expressions
(check-equal? (parse '{f})
              (AppC (IdC 'f) '()))
(check-equal? (parse '{f x})
              (AppC (IdC 'f) (list (IdC 'x))))
(check-equal? (parse '{+ 1 2})
              (AppC (IdC '+) (list (NumC 1) (NumC 2))))

;; Nested expressions
(check-equal? (parse '{+ {* 2 3} 4})
              (AppC (IdC '+) (list (AppC (IdC '*) (list (NumC 2) (NumC 3)))
                                   (NumC 4))))

; ============================================
; SERIALIZATION TESTS
; ============================================

(check-equal? (serialize (NumV 42)) "42")
(check-equal? (serialize (NumV -3.14)) "-3.14")
(check-equal? (serialize (NumV 0)) "0")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StrV "hello")) "\"hello\"")
(check-equal? (serialize (StrV "")) "\"\"")
(check-equal? (serialize (StrV "with \"quotes\"")) "\"with \\\"quotes\\\"\"")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (NullV)) "null")

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
(check-equal? (top-interp 'num-eq?) "#<primop>")
(check-equal? (top-interp 'str-eq?) "#<primop>")
(check-equal? (top-interp 'substring) "#<primop>")
(check-equal? (top-interp 'strlen) "#<primop>")
(check-equal? (top-interp '{- 10 3}) "7")
(check-equal? (top-interp '{* 3 4}) "12")
(check-equal? (top-interp '{/ 12 3}) "4")

;; Arithmetic with non-numbers should error
(check-exn #px"SHEQ" (lambda () (top-interp '{+ true 3})))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 3 "hello"})))
(check-exn #px"SHEQ" (lambda () (top-interp '{- "x" 3})))
(check-exn #px"SHEQ" (lambda () (top-interp '{* false true})))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 false})))

;; Division by zero
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 0})))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 0 0})))

;; Wrong number of arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{+})))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1})))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 2 3})))

;; Invalid substring range (stop < start)
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "test" 3 1})))

;; Invalid substring start index (negative)
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "test" -1 2})))

;; Non-integer substring index
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0.5 3})))

; ============================================
; COMPARISON OPERATIONS TESTS
; ============================================

(check-equal? (top-interp '{<= 3 4}) "true")
(check-equal? (top-interp '{<= 4 3}) "false")
(check-equal? (top-interp '{<= 3 3}) "true")
(check-equal? (top-interp '{<= -5 -2}) "true")

;; <= with non-numbers
(check-exn #px"SHEQ" (lambda () (top-interp '{<= "3" 4})))
(check-exn #px"SHEQ" (lambda () (top-interp '{<= true false})))

;; equality tests (num-eq? / str-eq?)
(check-equal? (top-interp '{num-eq? 3 3}) "true")
(check-equal? (top-interp '{num-eq? 3 4}) "false")
(check-equal? (top-interp '{str-eq? "hello" "hello"}) "true")
(check-equal? (top-interp '{str-eq? "hello" "world"}) "false")
(check-equal? (top-interp '{str-eq? "" ""}) "true")

;; Wrong number of arguments for num-eq?
(check-exn #px"SHEQ" (lambda () (top-interp '{num-eq?})))
(check-exn #px"SHEQ" (lambda () (top-interp '{num-eq? 1})))
(check-exn #px"SHEQ" (lambda () (top-interp '{num-eq? 1 2 3})))

;; ============================================
;; STRING OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{strlen "hello"}) "5")
(check-equal? (top-interp '{strlen ""}) "0")
(check-equal? (top-interp '{strlen "a"}) "1")

;; strlen with non-string
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen 5})))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen true})))

(check-equal? (top-interp '{substring "hello" 0 5}) "\"hello\"")
(check-equal? (top-interp '{substring "hello" 1 4}) "\"ell\"")
(check-equal? (top-interp '{substring "hello" 0 0}) "\"\"")
(check-equal? (top-interp '{substring "hello" 2 2}) "\"\"")

;; substring errors
(check-exn #px"SHEQ" (lambda () (top-interp '{substring 123 0 1}))) ; non-string
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 1.5 3}))) ; non-natural
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" -1 3}))) ; negative
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 6}))) ; out of range
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 3 2}))) ; stop before start

; ============================================
; CONDITIONALS TESTS
; ============================================

(check-equal? (top-interp '{if true 1 2}) "1")
(check-equal? (top-interp '{if false 1 2}) "2")
(check-equal? (top-interp '{if {<= 3 4} "yes" "no"}) "\"yes\"")
(check-equal? (top-interp '{if {<= 5 4} "yes" "no"}) "\"no\"")

;; Non-boolean test should error
(check-exn #px"SHEQ" (lambda () (top-interp '{if 1 2 3})))
(check-exn #px"SHEQ" (lambda () (top-interp '{if "true" 1 2})))

;; ============================================
;; LAMBDA AND APPLICATION TESTS WITH TYPES
;; ============================================

(check-equal? (top-interp '{{lambda () : 5}}) "5")
(check-equal? (top-interp '{{lambda ([num x]) : x} 42}) "42")
(check-equal? (top-interp '{{lambda ([num x] [num y]) : {+ x y}} 3 4}) "7")
(check-equal? (top-interp '{{lambda ([num x] [num y] [num z]) : {+ {+ x y} z}} 1 2 3}) "6")

;; Higher-order functions with types
(check-equal? (top-interp '{{lambda ([{num -> num} f] [num x]) : {f x}} {lambda ([num y]) : {+ y 1}} 5}) "6")
(check-equal? (top-interp '{{{lambda ([num x]) : {lambda ([num y]) : {+ x y}}} 3} 4}) "7")

;; Wrong number of arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda ([num x]) : x}})))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda ([num x]) : x} 1 2})))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda ([num x] [num y]) : x} 1})))

;; Application of non-function
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4})))
(check-exn #px"SHEQ" (lambda () (top-interp '{true false})))
(check-exn #px"SHEQ" (lambda () (top-interp '{"not-a-function" 1 2})))

;; ============================================
;; LET BINDING TESTS WITH TYPES
;; ============================================

(check-equal? (top-interp '{let {} in 5 end}) "5")
(check-equal? (top-interp '{let {[num x = 5]} in x end}) "5")
(check-equal? (top-interp '{let {[num x = 5] [num y = 10]} in {+ x y} end}) "15")

;; Shadowing
(check-equal? (top-interp '{let {[num x = 5]} in {let {[num x = 10]} in x end} end}) "10")
(check-equal? (top-interp '{let {[num + = 100]} in + end}) "100") ; shadows primitive

;; Scope tests - bindings don't see later bindings
(check-exn #px"SHEQ" (lambda () (top-interp '{let {[num x = y] [num y = 5]} in x end})))

;; Complex let expressions with types
(check-equal? (top-interp '{let {[{num -> num} f = {lambda ([num x]) : {+ x 1}}]} in {f 5} end}) "6")
(check-equal? (top-interp '{let {[num x = 3] [num y = 4]} in {let {[num z = {+ x y}]} in z end} end}) "7")

;; ============================================
;; CLOSURE AND ENVIRONMENT TESTS
;; ============================================

;; Lexical scoping with types
(check-equal? (top-interp '{let {[num x = 10]} in
                             {let {[{num -> num} f = {lambda ([num y]) : {+ x y}}]} in
                               {let {[num x = 20]} in
                                 {f 5}
                                 end}
                               end}
                             end}) "15") ; uses x=10, not x=20

;; Returning closures with types
(check-equal? (top-interp '{{{lambda ([num x]) : {lambda ([num y]) : {+ x y}}} 10} 5}) "15")

; ============================================
; MISC. TESTS
; ============================================

;; seq function with no arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{seq})))

;; assignment operator with reserved keyword
(check-exn #px"SHEQ" (lambda () (top-interp '{lambda := 5})))

;; ============================================
;; COMPLEX INTEGRATION TESTS
;; ============================================

;; Nested conditionals
(check-equal? (top-interp
               '{if {<= 3 4}
                    {if true "correct" "wrong1"}
                    "wrong2"}) "\"correct\"")

;; String manipulation
(check-equal? (top-interp
               '{let {[str s = "hello world"]} in
                  {substring s 0 {strlen {substring s 0 5}}}
                  end}) "\"hello\"")

;; ============================================
;; EDGE CASES AND STRESS TESTS
;; ============================================

(check-equal? (top-interp '{strlen ""}) "0")
(check-equal? (top-interp '{substring "" 0 0}) "\"\"")

(check-equal? (top-interp
               '{let {[num a = 1] [num b = 2] [num c = 3] [num d = 4] [num e = 5]}
                  in {+ {+ {+ {+ a b} c} d} e}
                  end}) "15")

(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 true})))
(check-exn #px"SHEQ" (lambda () (top-interp 'undefined-var)))
(check-exn #px"SHEQ" (lambda () (top-interp '{if 5 1 2})))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda ([num x]) : x} 1 2})))
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4})))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 1 0})))
(check-exn #px"SHEQ" (lambda () (parse '{lambda ([num x] [num x]) : x})))
(check-exn #px"SHEQ" (lambda () (parse '{let {[num x = 1] [num x = 2]} in x end})))

;; Wrong arity for primitives
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0})))
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 3 5})))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen})))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen "hello" "world"})))

; ============================================
; := tests
; ============================================

; Uncomment when seq is implemented
(check-equal? (top-interp '{let {[num x = 5]} in {x := 10} end}) "null")

(check-equal? (top-interp '{let {[num x = 5]} in {seq {x := 10} x} end}) "10")

(check-exn #px"SHEQ" (lambda () (top-interp '{y := 5})))

(check-equal? (top-interp '{let {[num x = 1] [num y = 2]}
                              in {seq {x := 10}
                                      {y := 20}
                                      {+ x y}}
                              end}) "30")

(check-equal? (top-interp '{let {[num x = 5]}
                              in {seq {x := {+ x 10}} x}
                              end}) "15")

;; ============================================
;; make-array tests
;; ============================================

(check-equal? (top-interp '{make-array 1 0}) "#<array>")
(check-equal? (top-interp '{make-array 5 42}) "#<array>")

(check-equal? (top-interp '{make-array 3 3.14}) "#<array>")

(check-equal? (top-interp '{make-array {+ 2 3} 0}) "#<array>")
(check-equal? (top-interp '{make-array 4 {* 3 7}}) "#<array>")

(check-exn #px"SHEQ" (lambda () (top-interp '{make-array 0 5})))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array -1 5})))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array -10 "x"})))

(check-exn #px"SHEQ" (lambda () (top-interp '{make-array "five" 0})))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array true 0})))

;; ============================================
;; aref tests
;; ============================================

;; Basic aref functionality (converted from array to make-array)
; (check-equal? (top-interp '{let {[numarray arr = {make-array 3 0}]}
;                              in {seq {aset! arr 0 10}
;                                      {aset! arr 1 20}
;                                      {aset! arr 2 30}
;                                      {aref arr 0}}
;                              end}) "10")

; (check-equal? (top-interp '{let {[numarray arr = {make-array 3 0}]}
;                              in {seq {aset! arr 0 10}
;                                      {aset! arr 1 20}
;                                      {aset! arr 2 30}
;                                      {aref arr 1}}
;                              end}) "20")

; (check-equal? (top-interp '{let {[numarray arr = {make-array 3 0}]}
;                              in {seq {aset! arr 0 10}
;                                      {aset! arr 1 20}
;                                      {aset! arr 2 30}
;                                      {aref arr 2}}
;  end}) "30")

;; aref with make-array default values
(check-equal? (top-interp '{aref {make-array 5 42} 0}) "42")
(check-equal? (top-interp '{aref {make-array 5 42} 4}) "42")

;; aref with complex expressions for index
; (check-equal? (top-interp '{let {[numarray arr = {make-array 4 0}]}
;                              in {seq {aset! arr 0 1}
;                                      {aset! arr 1 2}
;                                      {aset! arr 2 3}
;                                      {aset! arr 3 4}
;                                      {aref arr {+ 1 2}}}
;                              end}) "4")

;; aref in let binding
; (check-equal? (top-interp '{let {[numarray arr = {make-array 3 0}]}
;                              in {seq {aset! arr 0 5}
;                                      {aset! arr 1 10}
;                                      {aset! arr 2 15}
;                                      {aref arr 1}}
;                              end}) "10")

(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 3 0} -1})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 3 0} 3})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 1 0} 1})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 2 0} 10})))

(check-exn #px"SHEQ" (lambda () (top-interp '{aref 42 0})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref "not an array" 0})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref true 0})))

(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 3 0} "zero"})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aref {make-array 3 0} true})))

;; ============================================
;; aset! tests
;; ============================================

; (check-equal? (top-interp '{aset! {make-array 3 0} 0 100}) "null")
; (check-equal? (top-interp '{aset! {make-array 3 0} 1 42}) "null")

; (check-equal? (top-interp '{let {[{numarray num} arr = {make-array 3 10}]}
;                           in {seq {aset! arr 1 99}
;                                   {aref arr 1}}
;                           end}) "99")

; (check-equal? (top-interp '{let {[{numarray num} arr = {make-array 3 0}]}
;                           in {seq {aset! arr 1 {+ 5 10}}
;                                   {aref arr 1}}
;                           end}) "15")

; (check-equal? (top-interp '{let {[{numarray num} arr = {make-array 5 0}]}
;                           in {seq {aset! arr 0 10}
;                                   {aset! arr 1 20}
;                                   {aset! arr 2 30}
;                                   {aset! arr 3 40}
;                                   {aset! arr 4 50}
;                                   {aref arr 2}}
;                           end}) "30")

(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 3 0} -1 100})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 3 0} 3 100})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 1 0} 1 100})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 2 0} 5 100})))

(check-exn #px"SHEQ" (lambda () (top-interp '{aset! 42 0 100})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aset! "not an array" 0 100})))

(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 3 0} "zero" 100})))
(check-exn #px"SHEQ" (lambda () (top-interp '{aset! {make-array 3 0} false 100})))

; ;; ============================================
; ;; Order of evaluation tests (with type annotations)
; ;; ============================================

; (check-equal? (top-interp '{let {[num x = 5]}
;                           in {make-array {seq {x := 3} x} {seq {x := 10} x}}
;                           end}) "#<array>")

; (check-equal? (top-interp '{let {[num x = 5]}
;                           in {let {[numarray arr = {make-array {seq {x := 3} x} {seq {x := 10} x}}]}
;                                 in {aref arr 2}
;                                 end}
;                           end}) "10")

; (check-equal? (top-interp '{let {[num idx = 0]
;                               [num val = 100]
;                               [numarray arr = {make-array 3 1}]}
;                           in {seq {aset! arr {seq {idx := 2} idx} {seq {val := 999} val}}
;                                   {aref arr 2}}
;                           end}) "999")
