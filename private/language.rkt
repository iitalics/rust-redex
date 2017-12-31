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
  [q ::= imm mut]

  ; l-values; paths from a variable
  [lv ::= (in-hole p x)]
  ; paths
  [p ::= (* p) hole]
  ; expressions (r-values)
  [e ::=
     c
     lv
     (ref ℓ q lv)
     (new e)
     (do e e ...)
     (let ℓ ([x e]) e)]
  [c ::= i unit]
  #:binding-forms
  (let ℓ ([x e]) e #:refers-to x))

(define const?
  (redex-match? Rust c))

#;; new forms added in Rust+V, so that is used instead
(define expr?
  (redex-match? Rust e))

(define lvalue?
  (redex-match? Rust lv))

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
  ; values
  [v ::=
     c
     (ptr a)
     (ref q a)]
  ; variable->address map
  [V ::= ([x a] ...)]
  ; heap store
  [H ::= ([a v] ...)]
  ; additional expressions
  [e ::= ....
     v
     (pop [x] e)]
  ; evaluation context
  [E ::=
     (new E)
     (do E e ...)
     (let ℓ ([x E]) e)
     (pop [x] E)
     hole])

(define value?
  (redex-match? Rust+V v))

(define rvalue?
  (redex-match? Rust+V e))
