#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt")
(provide addr-of RRR)

(define-metafunction Rust+V
  H-read : H ptr -> v or #f
  [(H-read H a) v
   (where [v] (find a H))]
  [(H-read H _) #f])

(define-metafunction Rust+V
  H-write : H ptr v -> H
  [(H-write H a v) (chg a v H)])

(define-judgment-form Rust+V
  ;; evaluate l-value as pointer
  #:mode (addr-of I I I O)
  #:contract (addr-of H V lv ptr)
  [(where [a] (find x V))
   ------ "EL-Var"
   (addr-of H V x a)]

  [(addr-of H V lv ptr_1)
   (where (ref _ ptr_2) (H-read H ptr_1))
   ------ "EL-Deref"
   (addr-of H V (* lv) ptr_2)]

  [(addr-of H V lv ptr_1)
   (where (own a_2) (H-read H ptr_1))
   ------ "EL-Deow"
   (addr-of H V (* lv) a_2)])

(define RRR
  ;; "rust reduction relation"
  ;; expression evaluation!
  (reduction-relation Rust+V #:domain (H V e)
   (--> (H V (in-hole E (ref _ q lv)))
        (H V (in-hole E (ref q ptr)))
        "R-ref"
        (judgment-holds (addr-of H V lv ptr)))

   (--> (H   V (in-hole E (set! lv v)))
        (H_2 V (in-hole E unit))
        "R-set!"
        (judgment-holds (addr-of H V lv ptr))
        (where H_2 (H-write H ptr v)))

   (--> (H   V (in-hole E (new v)))
        (H_2 V (in-hole E (own a)))
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
  (test-judgment-holds (addr-of () ([x a]) x a))
  (test-judgment-holds (addr-of ([a (own b)]) ([x a]) (* x) b))
  (test-judgment-holds (addr-of ([a (ref IMM b)]) ([x a]) (* x) b))

  (test--> RRR
    (term (()      () (new 4)))
    (term (([a 4]) () (own a))))
  (test--> RRR
    (term (([a unit]) ([x a]) (ref ℓ IMM x)))
    (term (([a unit]) ([x a]) (ref IMM a))))
  (test--> RRR
    (term (() () (let ℓo ([x 3]) (ref ℓ IMM x))))
    (term (([a 3]) ([x a]) (pop [x] (ref ℓ IMM x)))))
  (test--> RRR
    (term (([a 3]) ([x a]) (pop [x] 4)))
    (term (() () 4)))
  (test--> RRR
    (term (([a 0]) ([x a]) (set! x 2)))
    (term (([a 2]) ([x a]) unit)))
  (test--> RRR
    (term (([a (own b)] [b 0]) ([x a]) (set! (* x) 2)))
    (term (([a (own b)] [b 2]) ([x a]) unit)))
  (test-->> RRR
    (term (() () (do 1 2 3 4)))
    (term (() () 4)))
  )

(module+ test
  (test-results))
