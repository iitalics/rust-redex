#lang racket/base
(require redex/reduction-semantics)

;; ------------------------------------------------------------
;; base utyped language

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
     lv
     (ref q ℓ lv)]

  ; paths
  [p ::= hole (* p)]

  ; an l-value is just a variable + path
  [lv ::= (in-hole p x)]
  )

(define lv?
  (redex-match? Rust lv))
