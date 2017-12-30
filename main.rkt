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
     (ref q ℓ lv)]

  ; paths
  [p ::= hole (* p)]

  ; an l-value is just a variable + path
  [lv ::= (in-hole p x)]
  )

(define lv?
  (redex-match? Rust lv))
