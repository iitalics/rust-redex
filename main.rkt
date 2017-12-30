#lang racket/base
(require redex/reduction-semantics)

;; ------------------------------------------------------------
;; base language definition
;; ------------------------------------------------------------

(define-language Rust
  [x ℓ ::= variable-not-otherwise-mentioned]
  [i ::= integer]
  [q ::= imm mut]

  ; expressions
  [e ::=
     unit
     i
     (let ℓ ([x e]) e)
     (new e)
     (in-hole p x)
     (ref q ℓ (in-hole p x))]

  ; paths
  [p ::=
     hole
     (* p)]
  )
