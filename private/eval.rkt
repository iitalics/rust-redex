#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt")
(provide lv= RRR)

(define-judgment-form Rust+V
  ;; evaluate l-value address
  #:mode (lv= I I I O)
  #:contract (lv= H V lv a)
  [(where [a] (find x V))
   ------ "EL-Var"
   (lv= H V x a)]

  [(lv= H V lv a_1)
   (where [(ref _ a_2)] (find a_1 H))
   ------ "EL-De-ref"
   (lv= H V (* lv) a_2)]

  [(lv= H V lv a_1)
   (where [(ptr a_2)] (find a_1 H))
   ------ "EL-De-ptr"
   (lv= H V (* lv) a_2)])


(define RRR
  ;; "rust reduction relation"
  ;; expression evaluation!
  (reduction-relation Rust+V #:domain (H V e)
   (--> (H V (in-hole E (ref _ q lv)))
        (H V (in-hole E (ref q a)))
        "R-ref"
        (judgment-holds (lv= H V lv a)))

   (--> (H   V (in-hole E (new v)))
        (H_2 V (in-hole E (ptr a)))
        "R-new"
        (fresh a)
        (where ([a_2 v_2] ...) H)
        (where H_2 ([a v] [a_2 v_2] ...)))

   (--> (H V (in-hole E (do v)))
        (H V (in-hole E v))
        "R-done")
   (--> (H V (in-hole E (do v e_1 e_2 ...)))
        (H V (in-hole E (do e_1 e_2 ...)))
        "R-shift")

   (--> (H V (in-hole E (let _ ([x v]) e)))
        (([a v] [a_3 v_3] ...)
         ([x a] [x_2 a_2] ...)
         (in-hole E (pop [x] e)))
        "R-let"
        (where ([x_2 a_2] ...) V)
        (where ([a_3 v_3] ...) H))

   (--> (H   V   (in-hole E (pop [x] v)))
        (H_2 V_2 (in-hole E v))
        "R-pop"
        (where [a] (find x V))
        (where V_2 (rem x V))
        (where H_2 (rem a H)))))

(module+ test
  (test-judgment-holds (lv= () ([x a]) x a))
  (test-judgment-holds (lv= ([a (ptr b)]) ([x a]) (* x) b))
  (test-judgment-holds (lv= ([a (ref imm b)]) ([x a]) (* x) b))

  (test--> RRR
           (term (()      () (new 4)))
           (term (([a 4]) () (ptr a))))
  (test--> RRR
           (term (([a unit]) ([x a]) (ref ℓ imm x)))
           (term (([a unit]) ([x a]) (ref imm a))))
  (test--> RRR
           (term (() () (let ℓo ([x 3]) (ref ℓ imm x))))
           (term (([a 3]) ([x a]) (pop [x] (ref ℓ imm x)))))

  ; redex is failing to reduce this pop expression :/
  (test--> RRR
           (term (([a 3]) ([x a]) (pop [x] 4)))
           (term (() () 4)))

  (test-->> RRR
            (term (() () (do 1 2 3 4)))
            (term (() () 4))))
