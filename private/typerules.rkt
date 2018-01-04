#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt")
(provide <: ⊢c ⊢lv ⊢)

(define-relation Rust+T
  ;; subtyping relation
  <: ⊂ τ × τ
  [(<: τ τ)])

(define-judgment-form Rust+T
  ;; typecheck constants
  #:mode (⊢c I O)
  #:contract (⊢c c τ)
  [------ "TC-Int"
   (⊢c i Integer)]
  [------ "TC-Unit"
   (⊢c unit Unit)])

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
  (test-judgment-holds (⊢lv ([x [Ptr Integer]]) x (Ptr Integer)))
  (test-judgment-holds (⊢lv ([x [Ptr Integer]]) (* x) Integer))
  (test-judgment-holds (⊢lv ([x [Ref ℓ IMM Unit]]) (* x) Unit))
  (test-judgment-holds (⊢c 5 Integer))
  (test-judgment-holds (⊢c unit Unit)))

(define-judgment-form Rust+S
  ;; typecheck r-values
  #:mode     (⊢ I  I I I I O O)
  #:contract (⊢ LT L Γ Y e τ Y)

  [(⊢c c τ)
   ------ "TR-Const"
   (⊢ _ _ _ Y c τ Y)]

  [(⊢lv Γ lv τ)
   ; TODO: check can-write, and update Y if necessary
   ------ "TR-Use"
   (⊢ _ _ Γ Y lv τ Y)]

  [(⊢lv Γ lv τ)
   ; TODO: check valid
   ; TODO: check freezable, can-read (IMM)
   ; TODO: check unique, can-write (MUT)
   ; TODO: record loan in Y
   ------ "TR-Ref"
   (⊢ _ _ Γ Y (ref ℓ q lv) [Ref ℓ q τ] Y)]

  [(⊢ LT L Γ Y_1 e_1 τ_1 Y_2)
   ; TODO: extend LT
   (⊢ LT
      (ext [x ℓ] L)
      (ext [x τ_1] Γ)
      Y_2 ; (ext [x s_1] Y_2) ; TODO: create fresh shadow from type
      e_2 τ_2
      Y_3)
   ; TODO: well-formedness checks; restrict Y_3
   ------ "TR-Let"
   (⊢ LT L Γ Y_1 (let ℓ ([x e_1]) e_2) τ_2 Y_3)]

  [(⊢ LT L Γ Y_1 e τ Y_2)
   ------ "TR-Do1"
   (⊢ LT L Γ Y_1 (do e) τ Y_2)]

  [(⊢ LT L Γ Y_1 e_1 τ_1 Y_2)
   (⊢ LT L Γ Y_2 (do e_2 ...) τ_2 Y_3)
   ------ "TR-DoN"
   (⊢ LT L Γ Y_1 (do e_1 e_2 ...) τ_2 Y_3)]

  [(⊢lv Γ lv τ_1)
   (⊢ LT L Γ Y_1 e τ_2 Y_2)
   (<: τ_2 τ_1)
   ; TODO: check can-write
   ------ "TR-Set"
   (⊢ LT L Γ Y_1 (set! lv e) Unit Y_2)]

  [(⊢ LT L Γ Y_1 e τ Y_2)
   ------ "TR-New"
   (⊢ LT L Γ Y_1 (new e) [Ptr τ] Y_2)]

  )

(module+ test
  (test-judgment-holds (⊢ () () () () unit Unit ()))
  (test-judgment-holds (⊢ ()
                          ([x ℓ])
                          ([x Integer])
                          ([x (() Integer)])
                          x Integer
                          ([x (() Integer)]))))


(module+ test
  (test-results))
