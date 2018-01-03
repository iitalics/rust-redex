#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")
(provide Rust Rust+T Rust+S Rust+V)

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
  [e ::=
     c
     lv
     (ref ℓ q lv)
     (let ℓ ([x e]) e)
     (do e e ...)
     (set! lv e)
     (new e)]
  [c ::= i unit]
  #:binding-forms
  (let ℓ ([x e]) e #:refers-to x))

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
