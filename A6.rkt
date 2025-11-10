; Full project implemented.
#lang typed/racket
(require typed/rackunit)

;; ====================
;; SHEQ6 language AST structs, types, and utilites
;; ====================

; Core types
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [otherwise : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct PrimC ([f : Any]) #:transparent)
(struct AssignC ([var : Symbol] [val : ExprC]) #:transparent)
(define-type ExprC (U NumC IdC IfC LamC AppC StrC PrimC AssignC))

; Value types
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([f : Symbol]) #:transparent)
(struct NullV () #:transparent)
(struct ArrayV ([sto-pos : Natural] [len : Natural]) #:transparent)
(define-type Value (U NumV BoolV StrV CloV PrimV NullV ArrayV))

; serialize: produces a string representation of a given value
(define (serialize [v : Value]) : String
  (match v
    [(NumV n) (format "~v" n)]
    [(BoolV b) (if b "true" "false")]
    [(StrV s) (format "~v" s)]
    [(? CloV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]
    [(? NullV?) "null"]
    [(? ArrayV?) "#<array>"]))

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

(define top-level-env
  (Env (list
        ; 0 reserved for free location indicator
        (Binding '+ 1)
        (Binding '- 2)
        (Binding '* 3)
        (Binding '/ 4)
        (Binding '<= 5)
        (Binding 'substring 6)
        (Binding 'strlen 7)
        (Binding 'equal? 8)
        (Binding 'true 9)
        (Binding 'false 10)
        (Binding 'error 11)
        (Binding 'seq 12)
        (Binding 'make-array 13)
        (Binding 'array 14)
        (Binding 'aref 15)
        (Binding 'aset! 16)
        (Binding 'while 17)
        (Binding 'null 18))))

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
                   (PrimV 'substring)
                   (PrimV 'string-length)
                   (PrimV 'equal?)
                   (BoolV #t)
                   (BoolV #f)
                   (PrimV 'error)
                   (PrimV 'seq)
                   (PrimV 'make-array)
                   (PrimV 'array)
                   (PrimV 'aref)
                   (PrimV 'aset!)
                   (PrimV 'while)
                   (NullV)) memsize))
  (cond
    [(< memsize (vector-length (Store-vals init-sto)))
     ; Error if size is less than the number of initial bindings
     (error (format "SHEQ: initial storage size ~a is too small" memsize))]
    [else
     (begin
       ; Set first position to current length to indicate next free location
       (vector-set! (Store-vals init-sto) 0 (NumV (vector-length (Store-vals init-sto))))
       ; Extend storage to requested size
       (Store (vector-append
               (Store-vals init-sto)
               (cast (make-vector (- memsize (vector-length (Store-vals init-sto))) (NullV)) (Vectorof Value))) memsize))]))

; read-store: retrieves the value at a given position from a given store
(define (read-store [pos : Natural] [sto : Store]) : Value
  (vector-ref (Store-vals sto) pos))

; allocate: allocates a new location in sto for the value val provided there's enough memory remaining
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
           (error (format "SHEQ: cannot allocate ~a, exceeded memory of size ~a" (serialize val) (Store-memsize sto)))])])]))

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
    [(list 'equal? (list l r))
     (cond
       [(or (CloV? l) (CloV? r) (PrimV? l) (PrimV? r))
        (BoolV #f)]
       [(and (NullV? l) (NullV? r))
        (BoolV #t)]
       [(and (ArrayV? l) (ArrayV? r))
        (BoolV (equal? (ArrayV-sto-pos l) (ArrayV-sto-pos r)))]
       [(and (NumV? l) (NumV? r))
        (BoolV (= (NumV-n l) (NumV-n r)))]
       [(and (BoolV? l) (BoolV? r))
        (BoolV (equal? (BoolV-b l) (BoolV-b r)))]
       [(and (StrV? l) (StrV? r))
        (BoolV (string=? (StrV-s l) (StrV-s r)))]
       [else (BoolV #f)])]

    ;; Error primitive
    [(list 'error (list v)) (error (format "user-error: ~v" v))]

    [(list 'seq args)
     (cond
       [(empty? args) (error "SHEQ: seq requires at least one expression")]
       [else (last args)])]

    [(list 'make-array (list (NumV len) elm))
     (cond
       [(and (natural? len) (>= len 1)) (make-array len elm sto)]
       [else (error (format "SHEQ: cannot create array of length ~a" len))])]

    [(list 'array (list elms ...))
     (cond
       [(< (length elms) 1) (error "SHEQ: cannot create array of fewer than 1 element")]
       [else (array elms sto)])]

    [(list 'aref (list (? ArrayV? arr) (NumV i)))
     (cond
       [(not (natural? i)) (error (format "SHEQ: index ~a must be a non-negative integer" i))]
       [(>= i (ArrayV-len arr)) (error (format "SHEQ: index ~a out of bounds for array length ~a" i (ArrayV-len arr)))]
       [else (aref arr i sto)])]

    [(list 'aset! (list (? ArrayV? arr) (NumV i) val))
     (cond
       [(not (natural? i)) (error (format "SHEQ: index ~a must be a non-negative integer" i))]
       [(>= i (ArrayV-len arr)) (error (format "SHEQ: index ~a out of bounds for array length ~a" i (ArrayV-len arr)))]
       [else (aset! arr i val sto)])]


    ;; Catch-all for any other wrong arity/type
    [_ (error (format "SHEQ: bad primitive application ~a with args ~a" op args))]))

(define reserved-set (list 'if ': 'let '= 'in 'end ':=))
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
         [(> i 0) (begin (allocate elm sto) (repeat-alloc (- i 1)))]
         [else (void)]))
     (begin
       (repeat-alloc len)
       new-array)]))

; array: creates an array made up of the given values
(define (array [elms : (Listof Value)] [sto : Store]) : ArrayV
  (match (vector-ref (Store-vals sto) 0)
    [(NumV (? natural? free-pos))
     (define new-array (ArrayV free-pos (length elms)))
     (define (repeat-alloc [es : (Listof Value)]) : Void
       (match es
         ['() (void)]
         [(cons first rest) (begin (allocate first sto) (repeat-alloc rest))]))
     (begin
       (repeat-alloc elms)
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
    [(list 'lambda (list (? symbol? args) ...) ': body)
     (cond
       [(ormap is-reserved? (cast args (Listof Symbol)))
        (error "SHEQ: cannot use reserved keyword as function argument name")]
       [(check-duplicates args) (error "SHEQ: duplicate function argument names")]
       [else (LamC (cast args (Listof Symbol)) (parse body))])]
    [(list 'let other-sexps ...)
     (match other-sexps
       [(list (list (list (? symbol? ids) '= exprs) ...) 'in body 'end)
        (AppC (LamC (cond
                      [(ormap is-reserved? (cast ids (Listof Symbol)))
                       (error "SHEQ: cannot use reserved keyword as identifier in let statement")]
                      [(check-duplicates ids) (error "SHEQ: duplicate identifiers in let statement")]
                      [else (cast ids (Listof Symbol))])
                    (parse body)) (map parse (cast exprs (Listof Sexp))))]
       [_ (error (format "SHEQ: ill-formed \"let\" expression, ~a" sexp))])]
    [(list (? symbol? s) ':= val-sexp)
     (cond
       [(is-reserved? s)
        (error (format "SHEQ: cannot assign to reserved keyword ~a" s))]
       [else (AssignC s (parse val-sexp))])]
    [(list fun args ...) (AppC (parse fun) (map parse args))]
    [_ (error (format "SHEQ: ill-formed expression, ~a" sexp))]))

;; ====================
;; Interpreter
;; ====================

; top-interp: intializes program parsing and interpreting, given an s-expression and memory size
(define (top-interp [s : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse s) top-level-env (make-init-sto memsize))))

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
    [(LamC args body) (CloV args body env)]
    [(AssignC var val)
     (define loc (env-lookup var env))
     (define new-val (interp val env sto))
     (begin
       (vector-set! (Store-vals sto) loc new-val)
       (NullV))]
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

(define while
  '{let {[while = "whatever"]}
     in
     {seq
      {while := {lambda (guard body) :
                  {if {guard}
                      {seq {body} {while guard body}}
                      null}}}
      while}
     end})


(define in-order
  '{let {[in-order = "whatever"]}
     in
     {seq
      {in-order := {lambda (arr size) :
                     {let {[i = 0]
                           [ordered = true]
                           [while = {let {[while = "whatever"]}
                                      in
                                      {seq
                                       {while := {lambda (guard body) :
                                                   {if {guard}
                                                       {seq {body} {while guard body}}
                                                       null}}}
                                       while}
                                      end}]}
                       in
                       {seq
                        {while
                          {lambda () :
                            {if ordered
                                {<= i {- size 2}}
                                false}}
                          {lambda () :
                            {if {<= {aref arr i} {aref arr {+ i 1}}}
                                {i := {+ i 1}}
                                {ordered := false}}}}
                        ordered}
                       end}}}
      in-order}
     end})



;; ============================================
;; PARSING TESTS
;; ============================================
(define default-memsize 50)

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
(check-exn #px"SHEQ" (lambda ()
                       (top-interp
                        '{let ((let = "")) in "World" end} default-memsize)))
(check-exn #px"SHEQ" (lambda ()
                       (top-interp
                        '{lambda (let) : let} default-memsize)))
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
(check-equal? (serialize (NullV)) "null")


;; ============================================
;; TOP-LEVEL ENVIRONMENT TESTS
;; ============================================

(check-equal? (top-interp 'true default-memsize) "true")
(check-equal? (top-interp 'false default-memsize) "false")
(check-equal? (top-interp '+ default-memsize) "#<primop>")
(check-equal? (top-interp '- default-memsize) "#<primop>")
(check-equal? (top-interp '* default-memsize) "#<primop>")
(check-equal? (top-interp '/ default-memsize) "#<primop>")
(check-equal? (top-interp '<= default-memsize) "#<primop>")
(check-equal? (top-interp 'equal? default-memsize) "#<primop>")
(check-equal? (top-interp 'substring default-memsize) "#<primop>")
(check-equal? (top-interp 'strlen default-memsize) "#<primop>")
(check-equal? (top-interp 'error default-memsize) "#<primop>")

;; Undefined identifier
(check-exn #px"SHEQ" (lambda () (top-interp 'undefined default-memsize)))

;; ============================================
;; ARITHMETIC OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{+ 3 4} default-memsize) "7")
(check-equal? (top-interp '{- 10 3} default-memsize) "7")
(check-equal? (top-interp '{* 3 4} default-memsize) "12")
(check-equal? (top-interp '{/ 12 3} default-memsize) "4")

;; Arithmetic with non-numbers should error TODO: implement arg checks
(check-exn #px"SHEQ" (lambda () (top-interp '{+ true 3} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 3 "hello"} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{- "x" 3} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{* false true} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 false} default-memsize)))

; Division by zero
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 5 0} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 0 0} default-memsize)))

;; Wrong number of arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{+} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 2 3} default-memsize)))

;; Invalid substring range (stop < start)
(check-exn
 #px"SHEQ"
 (lambda () (top-interp '{substring "test" 3 1} default-memsize)))

;; Invalid substring start index (negative)
(check-exn
 #px"SHEQ"
 (lambda () (top-interp '{substring "test" -1 2} default-memsize)))

;; Non-integer substring index
(check-exn
 #px"SHEQ"
 (lambda () (top-interp '{substring "hello" 0.5 3} default-memsize)))

;; ============================================
;; COMPARISON OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{<= 3 4} default-memsize) "true")
(check-equal? (top-interp '{<= 4 3} default-memsize) "false")
(check-equal? (top-interp '{<= 3 3} default-memsize) "true")
(check-equal? (top-interp '{<= -5 -2} default-memsize) "true")

;; <= with non-numbers
(check-exn #px"SHEQ" (lambda () (top-interp '{<= "3" 4} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{<= true false} default-memsize)))

;; equal? tests
(check-equal? (top-interp '{equal? 3 3} default-memsize) "true")
(check-equal? (top-interp '{equal? 3 4} default-memsize) "false")
(check-equal? (top-interp '{equal? true true} default-memsize) "true")
(check-equal? (top-interp '{equal? false false} default-memsize) "true")
(check-equal? (top-interp '{equal? true false} default-memsize) "false")
(check-equal? (top-interp '{equal? "hello" "hello"} default-memsize) "true")
(check-equal? (top-interp '{equal? "hello" "world"} default-memsize) "false")
(check-equal? (top-interp '{equal? "" ""} default-memsize) "true")
(check-equal? (top-interp '{equal? "null" "null"} default-memsize) "true")
(check-equal? (top-interp '{equal? "null" "world"} default-memsize) "false")
(check-equal? (top-interp '{equal? "hello" "null"} default-memsize) "false")

;; equal? with different types returns false
(check-equal? (top-interp '{equal? 3 "3"} default-memsize) "false")
(check-equal? (top-interp '{equal? true 1} default-memsize) "false")
(check-equal? (top-interp '{equal? false 0} default-memsize) "false")

;; equal? with functions returns false
(check-equal? (top-interp '{equal? {lambda (x) : x} {lambda (x) : x}} default-memsize) "false")
(check-equal? (top-interp '{equal? + +} default-memsize) "false")
(check-equal? (top-interp '{equal? + -} default-memsize) "false")

;; Wrong number of arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{equal?} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{equal? 1} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{equal? 1 2 3} default-memsize)))

;; ============================================
;; STRING OPERATIONS TESTS
;; ============================================

(check-equal? (top-interp '{strlen "hello"} default-memsize) "5")
(check-equal? (top-interp '{strlen ""} default-memsize) "0")
(check-equal? (top-interp '{strlen "a"} default-memsize) "1")

;; strlen with non-string
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen 5} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen true} default-memsize)))

(check-equal? (top-interp '{substring "hello" 0 5} default-memsize) "\"hello\"")
(check-equal? (top-interp '{substring "hello" 1 4} default-memsize) "\"ell\"")
(check-equal? (top-interp '{substring "hello" 0 0} default-memsize) "\"\"")
(check-equal? (top-interp '{substring "hello" 2 2} default-memsize) "\"\"")

;; substring errors
(check-exn #px"SHEQ" (lambda () (top-interp '{substring 123 0 1} default-memsize))) ; non-string
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 1.5 3} default-memsize))) ; non-natural
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" -1 3} default-memsize))) ; negative
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 6} default-memsize))) ; out of range
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 3 2} default-memsize))) ; stop before start

;; ============================================
;; ERROR FUNCTION TESTS
;; ============================================

(check-exn #px"user-error.*42" (lambda () (top-interp '{error 42} default-memsize)))
(check-exn #px"user-error.*\"test\"" (lambda () (top-interp '{error "test"} default-memsize)))

;; ============================================
;; CONDITIONALS TESTS
;; ============================================

(check-equal? (top-interp '{if true 1 2} default-memsize) "1")
(check-equal? (top-interp '{if false 1 2} default-memsize) "2")
(check-equal? (top-interp '{if {<= 3 4} "yes" "no"} default-memsize) "\"yes\"")
(check-equal? (top-interp '{if {<= 5 4} "yes" "no"} default-memsize) "\"no\"")

;; Non-boolean test should error
(check-exn #px"SHEQ" (lambda () (top-interp '{if 1 2 3} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{if "true" 1 2} default-memsize)))

;; ============================================
;; LAMBDA AND APPLICATION TESTS
;; ============================================

(check-equal? (top-interp '{{lambda () : 5}} default-memsize) "5")
(check-equal? (top-interp '{{lambda (x) : x} 42} default-memsize) "42")
(check-equal? (top-interp '{{lambda (x y) : {+ x y}} 3 4} default-memsize) "7")
(check-equal? (top-interp '{{lambda (x y z) : {+ {+ x y} z}} 1 2 3} default-memsize) "6")

;; Higher-order functions
(check-equal? (top-interp '{{lambda (f x) : {f x}} {lambda (y) : {+ y 1}} 5} default-memsize) "6")
(check-equal? (top-interp '{{{lambda (x) : {lambda (y) : {+ x y}}} 3} 4} default-memsize) "7")

;; Wrong number of arguments
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x}} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x} 1 2} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x y) : x} 1} default-memsize)))

;; Application of non-function
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{true false} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{"not-a-function" 1 2} default-memsize)))

;; ============================================
;; LET BINDING TESTS
;; ============================================

(check-equal? (top-interp '{let {} in 5 end} default-memsize) "5")
(check-equal? (top-interp '{let {[x = 5]} in x end} default-memsize) "5")
(check-equal? (top-interp '{let {[x = 5] [y = 10]} in {+ x y} end} default-memsize) "15")

;; Shadowing
(check-equal? (top-interp '{let {[x = 5]} in {let {[x = 10]} in x end} end} default-memsize) "10")
(check-equal? (top-interp '{let {[+ = 100]} in + end} default-memsize) "100") ; shadows primitive

;; Scope tests - bindings don't see later bindings
(check-exn #px"SHEQ" (lambda () (top-interp '{let {[x = y] [y = 5]} in x end} default-memsize)))

;; Complex let expressions
(check-equal? (top-interp '{let {[f = {lambda (x) : {+ x 1}}]} in {f 5} end} default-memsize) "6")
(check-equal? (top-interp '{let {[x = 3] [y = 4]} in {let {[z = {+ x y}]} in z end} end} default-memsize) "7")

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
                             end} default-memsize) "15") ; uses x=10, not x=20

;; Returning closures
(check-equal? (top-interp '{{{lambda (x) : {lambda (y) : {+ x y}}} 10} 5} default-memsize) "15")

;; ============================================
;; MISC. TESTS
;; ============================================

;; Memory exceeded
(check-exn #px"SHEQ" (lambda () (top-interp
                                 '{let {[fact = {lambda (f n) :
                                                  {if {<= n 0}
                                                      1
                                                      {* n {f f {- n 1}}}}}]}
                                    in {fact fact 5} end} 2)))

;; ============================================
;; COMPLEX INTEGRATION TESTS
;; ============================================

;; Factorial
(check-equal? (top-interp
               '{let {[fact = {lambda (f n) :
                                {if {<= n 0}
                                    1
                                    {* n {f f {- n 1}}}}}]}
                  in {fact fact 5} end} default-memsize) "120")

;; Nested conditionals
(check-equal? (top-interp
               '{if {<= 3 4}
                    {if true "correct" "wrong1"}
                    "wrong2"} default-memsize) "\"correct\"")

;; String manipulation
(check-equal? (top-interp
               '{let {[s = "hello world"]} in
                  {substring s 0 {strlen {substring s 0 5}}}
                  end} default-memsize) "\"hello\"")

;; Error propagation
(check-exn #px"user-error" (lambda () (top-interp
                                       '{let {[f = {lambda (x) : {error x}}]} in
                                          {if true {f "oops"} 42}
                                          end} default-memsize)))

;; ============================================
;; EDGE CASES AND STRESS TESTS
;; ============================================

;; Empty string operations
(check-equal? (top-interp '{strlen ""} default-memsize) "0")
(check-equal? (top-interp '{substring "" 0 0} default-memsize) "\"\"")

;; Many let bindings
(check-equal? (top-interp
               '{let {[a = 1] [b = 2] [c = 3] [d = 4] [e = 5]}
                  in {+ {+ {+ {+ a b} c} d} e}
                  end} default-memsize) "15")

;; Primitive as first-class value
(check-equal? (top-interp
               '{let {[op = +]} in {op 3 4} end} default-memsize) "7")
(check-equal? (top-interp
               '{{lambda (f x y) : {f x y}} + 10 20} default-memsize) "30")

(check-exn #px"SHEQ" (lambda () (top-interp '{+ 1 true} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp 'undefined-var default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{if 5 1 2} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{{lambda (x) : x} 1 2} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{3 4} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{/ 1 0} default-memsize)))
(check-exn #px"SHEQ" (lambda () (parse '{lambda (x x) : x})))
(check-exn #px"SHEQ" (lambda () (parse '{let {[x = 1] [x = 2]} in x end})))

;; Wrong arity for primitives
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{substring "hello" 0 3 5} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen} 10)))
(check-exn #px"SHEQ" (lambda () (top-interp '{strlen "hello" "world"} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{error} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{error 1 2} default-memsize)))


;; ============================================
;; ASSIGNMENT (:=) TESTS
;; ============================================

;; Basic assignment returns null
(check-equal? (top-interp '{let {[x = 5]} in {x := 10} end} default-memsize) "null")

;; Assignment and then read updated value
(check-equal? (top-interp '{let {[x = 5]} in {seq {x := 10} x} end} default-memsize) "10")

;; Assignment to undefined variable should error
(check-exn #px"SHEQ" (lambda () (top-interp '{y := 5} default-memsize)))

;; Multiple assignments
(check-equal? (top-interp '{let {[x = 1] [y = 2]}
                             in {seq {x := 10}
                                     {y := 20}
                                     {+ x y}}
                             end} default-memsize) "30")

;; Assignment with expression
(check-equal? (top-interp '{let {[x = 5]}
                             in {seq {x := {+ x 10}} x}
                             end} default-memsize) "15")

;; ============================================
;; ARRAY OPERATION TESTS
;; ============================================

;; ============================================
;; make-array tests
;; ============================================

;; Basic make-array functionality
(check-equal? (top-interp '{make-array 1 0} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 5 42} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 10 "hello"} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 3 true} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 2 false} default-memsize) "#<array>")

;; make-array with different value types
(check-equal? (top-interp '{make-array 3 3.14} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 2 null} default-memsize) "#<array>")

;; make-array with complex expressions
(check-equal? (top-interp '{make-array {+ 2 3} 0} default-memsize) "#<array>")
(check-equal? (top-interp '{make-array 4 {* 3 7}} default-memsize) "#<array>")

;; Error: make-array with size < 1
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array 0 5} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array -1 5} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array -10 "x"} default-memsize)))

;; Error: make-array with non-numeric size
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array "five" 0} default-memsize)))
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array true 0} default-memsize)))

;; Error: out of memory (array too large)
(check-exn #px"SHEQ" (lambda () (top-interp '{make-array 1000 0} default-memsize)))

;; ============================================
;; array tests
;; ============================================

;; Basic array functionality
(check-equal? (top-interp '{array 1} default-memsize) "#<array>")
(check-equal? (top-interp '{array 1 2 3} default-memsize) "#<array>")
(check-equal? (top-interp '{array "a" "b" "c" "d"} default-memsize) "#<array>")

;; array with mixed types
(check-equal? (top-interp '{array 1 "hello" true 3.14} default-memsize) "#<array>")
(check-equal? (top-interp '{array false null 42 "world"} default-memsize) "#<array>")

;; array with expressions
(check-equal? (top-interp '{array {+ 1 2} {* 3 4} {- 10 5}} default-memsize) "#<array>")

;; Error: array with no elements
(check-exn #px"" (lambda () (top-interp '{array} default-memsize)))

;; ============================================
;; aref tests
;; ============================================

;; Basic aref functionality
(check-equal? (top-interp '{aref {array 10 20 30} 0} default-memsize) "10")
(check-equal? (top-interp '{aref {array 10 20 30} 1} default-memsize) "20")
(check-equal? (top-interp '{aref {array 10 20 30} 2} default-memsize) "30")

;; aref with different types
(check-equal? (top-interp '{aref {array "a" "b" "c"} 0} default-memsize) "\"a\"")
(check-equal? (top-interp '{aref {array true false} 1} default-memsize) "false")
(check-equal? (top-interp '{aref {array 3.14 2.71} 0} default-memsize) "3.14")

;; aref with make-array
(check-equal? (top-interp '{aref {make-array 5 42} 0} default-memsize) "42")
(check-equal? (top-interp '{aref {make-array 5 42} 4} default-memsize) "42")

;; aref with complex expressions for index
(check-equal? (top-interp '{aref {array 1 2 3 4} {+ 1 2}} default-memsize) "4")
(check-equal? (top-interp '{aref {array 10 20 30} {- 2 1}} default-memsize) "20")

;; aref in let binding
(check-equal? (top-interp '{let {[arr = {array 5 10 15}]}
                             in {aref arr 1}
                             end} default-memsize) "10")

;; Error: aref with negative index
(check-exn #px"" (lambda () (top-interp '{aref {array 1 2 3} -1} default-memsize)))

;; Error: aref with index >= array size
(check-exn #px"" (lambda () (top-interp '{aref {array 1 2 3} 3} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aref {array 1} 1} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aref {array 1 2} 10} default-memsize)))

;; Error: aref on non-array
(check-exn #px"" (lambda () (top-interp '{aref 42 0} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aref "not an array" 0} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aref true 0} default-memsize)))

;; Error: aref with non-numeric index
(check-exn #px"" (lambda () (top-interp '{aref {array 1 2 3} "zero"} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aref {array 1 2 3} true} default-memsize)))

; ============================================
; aset! tests
; ============================================

;; Basic aset! functionality (returns null)
(check-equal? (top-interp '{aset! {array 1 2 3} 0 100} default-memsize) "null")
(check-equal? (top-interp '{aset! {make-array 3 0} 1 42} default-memsize) "null")

;; aset! and then aref to verify mutation
(check-equal? (top-interp '{let {[arr = {array 10 20 30}]}
                             in {seq {aset! arr 1 99}
                                     {aref arr 1}}
                             end} default-memsize) "99")

(check-equal? (top-interp '{let {[arr = {make-array 5 0}]}
                             in {seq {aset! arr 0 100}
                                     {aset! arr 4 400}
                                     {aref arr 0}}
                             end} default-memsize) "100")

;; aset! with different types
(check-equal? (top-interp '{let {[arr = {array 1 2 3}]}
                             in {seq {aset! arr 0 "hello"}
                                     {aref arr 0}}
                             end} default-memsize) "\"hello\"")

(check-equal? (top-interp '{let {[arr = {array "a" "b"}]}
                             in {seq {aset! arr 1 true}
                                     {aref arr 1}}
                             end} default-memsize) "true")

;; aset! with expressions
(check-equal? (top-interp '{let {[arr = {array 0 0 0}]}
                             in {seq {aset! arr 1 {+ 5 10}}
                                     {aref arr 1}}
                             end} default-memsize) "15")

;; Multiple mutations
(check-equal? (top-interp '{let {[arr = {array 1 2 3 4 5}]}
                             in {seq {aset! arr 0 10}
                                     {aset! arr 1 20}
                                     {aset! arr 2 30}
                                     {aset! arr 3 40}
                                     {aset! arr 4 50}
                                     {aref arr 2}}
                             end} default-memsize) "30")

;; Error: aset! with negative index
(check-exn #px"" (lambda () (top-interp '{aset! {array 1 2 3} -1 100} default-memsize)))

;; Error: aset! with index >= array size
(check-exn #px"" (lambda () (top-interp '{aset! {array 1 2 3} 3 100} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aset! {array 1} 1 100} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aset! {make-array 2 0} 5 100} default-memsize)))

;; Error: aset! on non-array
(check-exn #px"" (lambda () (top-interp '{aset! 42 0 100} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aset! "not an array" 0 100} default-memsize)))

;; Error: aset! with non-numeric index
(check-exn #px"" (lambda () (top-interp '{aset! {array 1 2 3} "zero" 100} default-memsize)))
(check-exn #px"" (lambda () (top-interp '{aset! {array 1 2 3} false 100} default-memsize)))

; ============================================
; Order of evaluation tests
; ============================================

; NOTE: uncomment when := is implemented
; ;; make-array evaluates size before initial value
; (check-equal? (top-interp '{let {[x = 5]}
;                              in {make-array {seq {x := 3} x} {seq {x := 10} x}}
;                              end} default-memsize) "#<array>")

; ;; Verify the array was created with size 3 (after first mutation)
; (check-equal? (top-interp '{let {[x = 5]}
;                              in {let {[arr = {make-array {seq {x := 3} x} {seq {x := 10} x}}]}
;                                   in {aref arr 2}  ;; Should succeed since size is 3
;                                   end}
;                              end} default-memsize) "10")

; ;; aref evaluates array before index
; (check-equal? (top-interp '{let {[idx = 0]
;                                  [arr1 = {array 10 20}]
;                                  [arr2 = {array 30 40}]
;                                  [current = arr1]}
;                              in {aref {seq {current := arr2} current}
;                                       {seq {idx := 1} idx}}
;                              end} default-memsize) "40")

; ;; aset! evaluates array, then index, then value
; (check-equal? (top-interp '{let {[idx = 0]
;                                  [val = 100]
;                                  [arr = {array 1 2 3}]}
;                              in {seq {aset! arr {seq {idx := 2} idx} {seq {val := 999} val}}
;                                      {aref arr 2}}
;                              end} default-memsize) "999")

;; ============================================
;; Array equality tests
;; ============================================

;; Arrays are equal only if they are the same array
(check-equal? (top-interp '{let {[arr = {array 1 2 3}]}
                             in {equal? arr arr}
                             end} default-memsize) "true")

(check-equal? (top-interp '{equal? {array 1 2 3} {array 1 2 3}} default-memsize) "false")

(check-equal? (top-interp '{let {[arr1 = {array 1 2}]}
                             in {let {[arr2 = arr1]}
                                  in {equal? arr1 arr2} end} end} default-memsize) "true")


;; ============================================
;; while tests
;; ============================================
(check-equal?
 (top-interp
  '{let {[i = 0]
         [while = {let {[while = "bogus"]}
                     in
                     {seq
                      {while := {lambda (guard body) :
                                  {if {guard}
                                      {seq {body} {while guard body}}
                                      null}}}
                      while}
                     end}]}
     in
     {seq
      {while {lambda () : {<= i 3}}
             {lambda () : {i := {+ i 1}}}}
      i}
     end}
  default-memsize)
 "4")

(check-equal?
 (top-interp
  '{let {[arr = {array 1 2 3 4 5}]
         [size = 5]
         [in-order = {let {[in-order = "whatever"]}
                        in
                        {seq
                         {in-order := {lambda (arr size) :
                                        {let {[i = 0]
                                               [ordered = true]
                                               [while = {let {[while = "whatever"]}
                                                          in
                                                          {seq
                                                           {while := {lambda (guard body) :
                                                                       {if {guard}
                                                                           {seq {body} {while guard body}}
                                                                           null}}}
                                                           while}
                                                          end}]}
                                          in
                                          {seq
                                           {while
                                             {lambda () :
                                               {if ordered
                                                   {<= i {- size 2}}   ;; <-- FIXED HERE
                                                   false}}
                                             {lambda () :
                                               {if {<= {aref arr i} {aref arr {+ i 1}}}
                                                   {i := {+ i 1}}
                                                   {ordered := false}}}}
                                           ordered}
                                          end}}}
                         in-order}
                        end}]}
     in {in-order arr size}
     end}
  default-memsize)
 "true")
