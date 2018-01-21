#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")
(provide Rust Rust+T Rust+S Rust+V)

;; ------------------------------------------------------------
;; base untyped language

(define-extended-language Rust Base
  [x ℓ ::= variable-not-otherwise-mentioned] ; variables, lifetimes
  [i ::= integer]
  [q ::= MUT IMM] ; for bank coherence: IMM < MUT
  [$ ::= ([ℓ q] ...)]
  ; l-values
  [lv ::= (in-hole path x)]
  [path ::=
     hole
     (* path)]
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
  ; move vs copy
  [move/copy ::= MOVE COPY]
  ; type context
  [Γ ::= ([x τ] ...)]
  ; variable lifetimes
  [L ::= ([x ℓ] ...)]
  ; lifetime poset
  [LT ::= ([ℓ < ℓ ...] ...)])

;; ------------------------------------------------------------
;; shadow heap

(define-extended-language Rust+S Rust+T
  ; shadow types
  [sτ ::=
      BT
      uninit
      [Ref ℓ q s]
      [Ptr s]]
  ; shadows
  ;   NOTE: τ ⊆ s
  ;   TODO: shadow ref types don't need lifetimes!
  ;         but removing them would break our precious subsumption
  [s ::= (loan ℓ q s) sτ]
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
