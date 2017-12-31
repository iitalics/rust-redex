#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")

;; ------------------------------------------------------------
;; base untyped language

(define-extended-language Rust Base
  [x ℓ ::= variable-not-otherwise-mentioned]
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
     (let ℓ ([x e]) e)
     (new e)
     (do e ... e)]
  [c ::= i | unit])

(define lv?
  (redex-match? Rust lv))


;; ------------------------------------------------------------
;; types

(define-extended-language Rust+T Rust
  ; base types
  [bτ ::= Unit Integer]
  ; types
  [τ ::=
     BT
     [Ref ℓ q τ]
     [Ptr τ]]
  ; type context
  [Γ ::= ([x τ] ...)]
  ; variable lifetimes
  [L ::= ([x ℓ] ...)])

(define-metafunction Rust+T
  typeof-c : c -> BT
  [(typeof-c i) Integer]
  [(typeof-c unit) Unit])

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
