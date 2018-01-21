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
  ;; typecheck l-value, collecting the lifetimes/mutability
  ;; of each dereference. the first element of the bank $ is the
  ;; most shallow reference, and the last is the deepest.
  #:mode     (⊢lv* I I  O O)
  #:contract (⊢lv* Γ lv τ $)

  [(where [τ] (find x Γ))
   ------ "TL-Var"
   (⊢lv* Γ x τ ())]

  [(⊢lv* Γ lv [Ref ℓ q τ] $)
   ------ "TL-Deref"
   (⊢lv* Γ (* lv) τ ([ℓ q] . $))]

  [(⊢lv* Γ lv [Ptr τ] $)
   ------ "TL-Deown"
   (⊢lv* Γ (* lv) τ $)])

(define-judgment-form Rust+T
  ;; typecheck l-values
  #:mode     (⊢lv I I  O)
  #:contract (⊢lv Γ lv τ)
  [(⊢lv* Γ lv τ $)
   ------ "TL"
   (⊢lv Γ lv τ)])

(module+ test
  (test-judgment-holds (⊢lv ([i Integer]) i Integer))
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

;; discussion:
;;   "we cannot promise that the interior of a borrowed reference will be
;;   valid for longer than that reference's lifetime, nor can we promise
;;   that the interior of a immutable borrowed reference will have unique access"
;;  pg 25

(define-judgment-form Rust+S
  #:contract (valid-for? LT L Γ lv ℓ)
  #:mode     (valid-for? I  I I I  I)
  [(⊢lv* Γ lv τ ())
   (where (in-hole path x) lv)
   (where [ℓ_x] (find x L))
   (LT ℓ . pos-≤ . ℓ_x)
   ------ "VF-Base"
   (valid-for? LT L Γ lv ℓ)]

  [(⊢lv* Γ lv τ ([ℓ_1 q_1] [ℓ_i q_i] ...))
   (LT ℓ . pos-≤ . ℓ_1)
   ------ "VF-Deref"
   (valid-for? LT L Γ lv ℓ)])

(define-judgment-form Rust+S
  #:contract (freezable-for? LT Γ lv ℓ)
  #:mode     (freezable-for? I  I I  I)
  [(⊢lv* Γ lv τ ())
   ------ "FF"
   (freezable-for? LT Γ lv ℓ)]

  [(⊢lv* Γ lv τ ([ℓ_i q_i] ... [ℓ_ref IMM] [ℓ_j MUT] ...))
   (LT ℓ . pos-≤ . ℓ_ref)
   ------ "FF-DerefImm"
   (freezable-for? LT Γ lv ℓ)]

  [(⊢lv* Γ lv τ ([ℓ_ref MUT] [ℓ_j MUT] ...))
   (LT ℓ . pos-≤ . ℓ_ref)
   ------ "FF-DerefMut"
   (freezable-for? LT Γ lv ℓ)])

(define-judgment-form Rust+S
  #:contract (unique-for? LT Γ lv ℓ)
  #:mode     (unique-for? I  I I  I)
  [(⊢lv* Γ lv τ ())
   ------ "UF"
   (unique-for? LT Γ lv ℓ)]

  [(⊢lv* Γ lv τ ([ℓ_ref MUT] [ℓ_i MUT] ...))
   (LG ℓ . pos-≤ . ℓ_ref)
   ------ "UF-Ref"
   (unique-for? LT Γ lv ℓ)])

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

  ; ℓ3 < ℓ2 < ℓ1 < ℓ0 < ø
  (define the-LT '([ℓ3 < ℓ2 ℓ1 ℓ0] [ℓ2 < ℓ1 ℓ0] [ℓ1 < ℓ0] [ℓ0 <]))

  (define L1  '([y ℓ2] [x ℓ1]))
  (define Γ1  '([y Integer] [x [Ptr Integer]]))
  (define Y1  Γ1)

  (test-equal (judgment-holds (⊢lv ,Γ1 x τ) τ) '[[Ptr Integer]])
  (test-judgment-holds (,the-LT ℓ2 . pos-≤ . ℓ1))
  (test-judgment-holds (can-read? ,Y1 x))
  (test-judgment-holds (can-write? ,Y1 x))
  (test-judgment-holds (valid-for? ,the-LT ,L1 ,Γ1 x ℓ2))
  (test-judgment-holds (freezable-for? ,the-LT ,Γ1 x ℓ2))

  ; can only borrow y for ℓ < L(y) = ℓ2
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ3 IMM y) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ2 IMM y) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM y) _ _)) #f)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ0 IMM y) _ _)) #f)

  ; lifetime constraints on x are the same as (* x), since x is a Ptr
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ2 IMM x) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM x) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ0 IMM x) _ _)) #f)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ2 IMM (* x)) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ1 IMM (* x)) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L1 ,Γ1 ,Y1 (ref ℓ0 IMM (* x)) _ _)) #f)

  (define L2 '([z ℓ2]))
  (define Γ2 '([z [Ref ℓ1 IMM Integer]]))
  (define Y2 Γ2)

  ; cannot borrow for ℓ1 because ℓ1 > L(z) = ℓ2
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ3 IMM z) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ2 IMM z) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ1 IMM z) _ _)) #f)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ0 IMM z) _ _)) #f)

  ; CAN borrow for ℓ1 because we don't care about L(z), only the sub-lifetime (ℓ1)
  ; but cannot borrow for ℓ0 because ℓ0 > ℓ1
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ3 IMM (* z)) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ2 IMM (* z)) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ1 IMM (* z)) _ _)) #t)
  (test-equal (judgment-holds (⊢ ,the-LT ,L2 ,Γ2 ,Y2 (ref ℓ0 IMM (* z)) _ _)) #f)

  (test-equal (judgment-holds (can-read? ,Y2 z)) #t)
  (test-equal (judgment-holds (can-write? ,Y2 z)) #t)
  (test-equal (judgment-holds (can-read? ,Y2 (* z))) #t)
  ;(test-equal (judgment-holds (can-write? ,Y2 (* z))) #f)

  )


(module+ test
  (test-results))
