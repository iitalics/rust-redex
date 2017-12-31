#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")
(provide Rust Rust+T Rust+S Rust+V
         const? rvalue? lvalue?
         type? shadow?
         value?)

;; ------------------------------------------------------------
;; base untyped language

(define-extended-language Rust Base
  [x ℓ ::= variable-not-otherwise-mentioned] ; variables, lifetimes
  [i ::= integer]
  [q ::= MUT IMM]
  ; l-values
  [lv ::=
      x
      (* lv)]
  ; r-values
  [rv ::=
      lv
      (ref ℓ q lv)]
  ; compound expressions
  [e ::=
     c
     rv
     (let ℓ ([x e]) e)
     (do e e ...)
     (set! lv e)
     (new e)]
  [c ::= i unit]
  #:binding-forms
  (let ℓ ([x e]) e #:refers-to x))

(define const?
  (redex-match? Rust c))

(define lvalue?
  (redex-match? Rust lv))

#;; new forms added in Rust+V, so rvalue? is actually defined at the bottom
(define rvalue?
  (redex-match? Rust rv))

;; ------------------------------------------------------------
;; types

(define-extended-language Rust+T Rust
  ; base types
  [BT ::= Unit Integer]
  ; types
  [τ ::=
     BT
     [Ref ℓ q τ]
     [Ptr τ]]
  ; type context
  [Γ ::= ([x τ] ...)]
  ; variable lifetimes
  [L ::= ([x ℓ] ...)])

(define type?
  (redex-match? Rust+T τ))

;; ------------------------------------------------------------
;; shadow heap

(define-extended-language Rust+S Rust
  ; loan "bank"
  [$ ::= ((ℓ q) ...)]
  ; shadow types
  [sτ ::=
      BT
      uninit
      [Ptr s]]
  ; shadows
  [s ::= ($ sτ)]
  ; shadow heap
  [Y ::= ([x s] ...)])

(define shadow?
  (redex-match? Rust+S s))

;; ------------------------------------------------------------
;; heap and evaluation context

(define-extended-language Rust+V Rust
  [a ::= variable-not-otherwise-mentioned] ; addresses
  ; pointers (addresses with a route)
  [ptr ::= a]
  ; value layout
  [v ::=
     c
     uninit
     (own a)
     (ref q ptr)]
  ; variable->address map
  [V ::= ([x a] ...)]
  ; heap store
  [H ::= ([a v] ...)]
  ; additional expressions
  [e ::= .... v (pop [x] e)]
  ; evaluation context
  [E ::=
     (let ℓ ([x E]) e)
     (pop [x] E)
     (do v ... E e ...)
     (set! lv E)
     (new E)
     hole])

(define value?
  (redex-match? Rust+V v))

(define rvalue?
  (redex-match? Rust+V rv))

(define expression?
  (redex-match? Rust+V e))
