#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")

;; ------------------------------------------------------------
;; base utyped language

(define-extended-language Rust Base
  [x ℓ ::= variable-not-otherwise-mentioned]
  [i ::= integer]
  [q ::= imm mut]

  ; expressions
  [e ::=
     unit
     i
     (let ℓ ([x e]) e)
     (new e)
     lv
     (ref ℓ q lv)]

  ; paths
  [p ::= hole (* p)]

  ; an l-value is just a variable + path
  [lv ::= (in-hole p x)]
  )

(define lv?
  (redex-match? Rust lv))


;; ------------------------------------------------------------
;; types

(define-extended-language Rust+T Rust
  ; types
  [τ ::=
     Unit
     Integer
     [Ref ℓ q τ]
     [Ptr τ]]

  ; type context
  [Γ ::= ([x τ] ...)])

(define-judgment-form Rust+T
  ;; typecheck l-values
  #:mode (⊢lv I I O)
  #:contract (⊢lv Γ lv τ)

  [(where [τ] (find x Γ))
   ------ "TL-Var"
   (⊢lv Γ x τ)]

  [(⊢lv Γ lv [Ref _ _ τ])
   ------ "TL-Ref"
   (⊢lv Γ (* lv) τ)]

  [(⊢lv Γ lv [Ptr τ])
   ------ "TL-Ptr"
   (⊢lv Γ (* lv) τ)])

(module+ test
  (test-judgment-holds (⊢lv ([x (Ptr Integer)]) x (Ptr Integer)))
  (test-judgment-holds (⊢lv ([x (Ptr Integer)]) (* x) Integer))
  (test-judgment-holds (⊢lv ([x (Ref ℓ1 imm Unit)]) (* x) Unit)))
