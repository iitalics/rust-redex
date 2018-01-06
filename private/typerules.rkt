#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt"
         "poset.rkt")
(provide <: affinity ⊢c ⊢lv ⊢)

;; --------------------------------------------------
;; relations on types

(define-relation Rust+T
  ;; subtyping relation
  <: ⊂ τ × τ
  [(<: τ τ)])

(define-relation Rust+T
  ;; determine if type is affine ("move") or unrestricted ("copy")
  affinity ⊂ τ × move/copy
  [(affinity Integer COPY)]
  [(affinity Unit COPY)]
  [(affinity [Ref ℓ IMM τ]) COPY]
  [(affinity [Ref ℓ MUT τ]) MOVE]
  [(affinity [Ptr τ]) MOVE])

;; --------------------------------------------------
;; easy typerules: constants, l-values

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
  (test-judgment-holds (⊢lv ([x [Ptr Integer]]) x [Ptr Integer]))
  (test-judgment-holds (⊢lv ([x [Ptr Integer]]) (* x) Integer))
  (test-judgment-holds (⊢lv ([x [Ptr [Ptr Integer]]]) (* (* x)) Integer))
  (test-judgment-holds (⊢lv ([x [Ref ℓ IMM Unit]]) (* x) Unit))
  (test-judgment-holds (⊢c 5 Integer))
  (test-judgment-holds (⊢c unit Unit)))

;; --------------------------------------------------
;; ensuring operations do not violate loans

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

;; --------------------------------------------------
;; ensuring loan promises can be upheld

(define-judgment-form Rust+S
  #:contract (valid-for? LT L Γ lv ℓ)
  #:mode     (valid-for? I  I I I  I)
  [(where [ℓ_1] (find x L))
   (LT ℓ . pos-≤ . ℓ_1)
   ------ "VF-Base"
   (valid-for? LT L Γ (in-hole path x) ℓ)])

(define-judgment-form Rust+S
  #:contract (freezable-for? LT Γ lv ℓ)
  #:mode     (freezable-for? I  I I  I)
  [------ "FF-Base"
   (freezable-for? LT Γ x ℓ)]

  [(⊢lv Γ lv [Ptr τ])
   (freezable-for? LT Γ lv ℓ)
   ------ "FF-Deown"
   (freezable-for? LT Γ (* lv) ℓ)]

  [(⊢lv Γ lv [Ref ℓ_1 IMM τ])
   (LT ℓ . pos-≤ . ℓ_1)
   ------ "FF-DerefImm"
   (freezable-for? LT Γ (* lv) ℓ)]

  [(⊢lv Γ lv [Ref ℓ_1 MUT τ])
   (freezable-for? LT Γ lv ℓ)
   (LT ℓ . pos-≤ . ℓ_1)
   ------ "FF-DerefMut"
   (freezable-for? LT Γ (* lv) ℓ)])

(define-judgment-form Rust+S
  #:contract (unique-for? LT Γ lv ℓ)
  #:mode     (unique-for? I  I I  I)
  [------ "UF-Base"
   (unique-for? LT Γ x ℓ)]

  [(⊢lv Γ lv [Ptr τ])
   (unique-for? LT Γ lv ℓ)
   ------ "UF-Deown"
   (unique-for? LT Γ (* lv) ℓ)]

  [(⊢lv Γ lv [Ref ℓ_1 MUT τ])
   (unique-for? LT Γ lv ℓ)
   (LT ℓ . pos-≤ . ℓ_1)
   ------ "UF-DerefMut"
   (unique-for? LT Γ (* lv) ℓ)])

;; NOTE: UF => FF

;; --------------------------------------------------
;; finally, typechecking r-values

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
   (freezable-for? LT Γ lv ℓ)
   ; TODO: record loan in Y_2
   ------ "TR-RefImm"
   (⊢ LT L Γ Y_1 (ref ℓ IMM lv) [Ref ℓ IMM τ] Y_1)]

  [(⊢lv Γ lv τ)
   (can-write? Y_1 lv)
   (valid-for? LT L Γ lv ℓ)
   (unique-for? LT Γ lv ℓ)
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
   ------ "TR-DoMore"
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

  (define LT1 '([ℓ2 < ℓ1] [ℓ1 <]))
  (define L1  '([y ℓ2] [x ℓ1]))
  (define Γ1  '([y Integer] [x [Ptr Integer]]))
  (define Y1  Γ1)

  (test-equal (judgment-holds (⊢lv ,Γ1 x τ) τ) '[[Ptr Integer]])
  (test-judgment-holds (,LT1 ℓ2 . pos-≤ . ℓ1))
  (test-judgment-holds (can-read? ,Y1 x))
  (test-judgment-holds (valid-for? ,LT1 ,L1 ,Γ1 x ℓ2))
  (test-judgment-holds (freezable-for? ,LT1 ,Γ1 x ℓ2))

  (test-equal (judgment-holds (⊢ ,LT1 ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM x) τ _) τ)
              '[(Ref ℓ1 IMM [Ptr Integer])]) ; borrow x for duration of x
  (test-equal (judgment-holds (⊢ ,LT1 ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM (* x)) τ _) τ)
              '[(Ref ℓ1 IMM Integer)]) ; borrow *x for duration of x
  (test-equal (judgment-holds (⊢ ,LT1 ,L1 ,Γ1 ,Y1 (ref ℓ2 IMM x) τ _) τ)
              '[(Ref ℓ2 IMM [Ptr Integer])]) ; borrow x for duration of y
  (test-equal (judgment-holds (⊢ ,LT1 ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM y) τ _) τ)
              '()) ; borrow y for duration of x

  )


(module+ test
  (test-results))
