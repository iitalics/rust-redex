#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt"
         "poset.rkt")
(provide <: ⊢c ⊢lv ⊢)

(define-relation Rust+T
  ;; subtyping relation
  <: ⊂ τ × τ
  [(<: τ τ)])

(define-relation Rust+T
  ;; determine if type is affine ("move") or unrestricted ("copy")
  affinity ⊂ τ × m/c
  [(affinity Integer COPY)]
  [(affinity Unit COPY)]
  [(affinity [Ref ℓ IMM τ]) COPY]
  [(affinity [Ref ℓ MUT τ]) MOVE]
  [(affinity [Ptr τ]) MOVE])

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
  #:mode     (can-read? I I)
  #:contract (can-read? Y lv)
  [------ "CR" ; TODO: can-read?
   (can-read? Y lv)])

(define-judgment-form Rust+S
  #:mode     (can-write? I I)
  #:contract (can-write? Y lv)
  [------ "CW" ; TODO: can-write?
   (can-write? Y lv)])

(define-judgment-form Rust+S
  #:mode     (can-move? I I)
  #:contract (can-move? Y lv)
  [------ "CM" ; TODO: can-move?
   (can-move? Y lv)])

;; NOTE: CM => CW => CR

(define-judgment-form Rust+S
  #:contract (valid-for? LT L Γ lv ℓ)
  #:mode     (valid-for? I  I I I  I)
  [------ "VF" ; TODO: valid-for?
   (valid-for? LT L Γ lv ℓ)])

(define-judgment-form Rust+S
  ;; typecheck r-values
  #:mode     (⊢ I  I I I I O O)
  #:contract (⊢ LT L Γ Y e τ Y)

  [(⊢c c τ)
   ------ "TR-Const"
   (⊢ LT L Γ Y c τ Y)]

  [(⊢lv Γ lv τ)
   (affinity τ COPY)
   (can-read? Y lv)
   ------ "TR-Copy"
   (⊢ LT L Γ Y lv τ Y)]

  [(⊢lv Γ lv τ)
   (affinity τ MOVE)
   (can-move? Y_1 lv)
   ; TODO: record use in Y_2
   ------ "TR-Move"
   (⊢ LT L Γ Y_1 lv τ Y_1)]

  [(⊢lv Γ lv τ)
   (can-read? Y_1 lv)
   (valid-for? LT L Γ lv ℓ)
   ; TODO: freezable?
   ; TODO: record loan in Y_2
   ------ "TR-RefImm"
   (⊢ LT L Γ Y_1 (ref ℓ IMM lv) [Ref ℓ IMM τ] Y_1)]

  [(⊢lv Γ lv τ)
   (can-write? Y_1 lv)
   (valid-for? LT L Γ lv ℓ)
   ; TODO: unique-access?
   ; TODO: record loan in Y_2
   ------ "TR-RefMut"
   (⊢ LT L Γ Y_1 (ref ℓ MUT lv) [Ref ℓ MUT τ] Y_1)]

  [(⊢ LT L Γ Y_1 e_1 τ_1 Y_2)
   (⊢ (pos-ext LT ℓ)
      (ext [x ℓ] L)
      (ext [x τ_1] Γ)
      (ext [x τ_1] Y_2)
      e_2 τ_2
      Y_3)
   (where Y_4 (rem x Y_3))
   ; TODO: well-formed check
   ; TODO: remove all ℓ from Y_3
   ------ "TR-Let"
   (⊢ LT L Γ Y_1 (let ℓ ([x e_1]) e_2) τ_2 Y_4)]

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
                          ([x Integer])
                          x Integer
                          ([x Integer])))
  (test-judgment-holds (⊢ () () () ()
                          (let ℓ ([x 4]) x) Integer
                          ()))
  )


(module+ test
  (test-results))
