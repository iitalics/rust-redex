#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt"
         "language.rkt")
(provide H-read H-write lv--> RRR)

(module+ test

  (define H1 '(        [a_0 (own a_1)] [a_1 (own a_2)] [a_2 0]))
  (define H2 '([a_3 9] [a_0 (own a_1)] [a_1 (own a_2)] [a_2 0]))
  (define H3 '([a_3 8] [a_0 (own a_1)] [a_1 (own a_2)] [a_2 0]))
  (define H4 '(        [a_0 uninit]    [a_1 (own a_2)] [a_2 0]))

  (define V1 '(          [x_0 a_0]))
  (define V2 '([x_1 a_3] [x_0 a_0]))

  )

(define-judgment-form Rust+V
  #:mode     (H-read I I O)
  #:contract (H-read H ptr v)
  [(where [v] (find a H))
   ------ "Read"
   (H-read H a v)])

(define-judgment-form Rust+V
  #:mode     (H-write I I I O)
  #:contract (H-write H ptr v H)
  [------ "Write"
   (H-write H a v (chg a v H))])

(define-metafunction Rust+V
  use : v -> v
  [(use c) c]
  [(use (ref IMM ptr)) (ref IMM Ptr)]
  [(use (ref MUT ptr)) uninit]
  [(use (own a)) uninit])

(define-judgment-form Rust+V
  ;; evaluate l-value as pointer
  #:mode (lv--> I O)
  #:contract (lv--> (H V lv) ptr)
  [(where [a] (find x V))
   ------ "EL-Var"
   (lv--> (H V x) a)]

  [(lv--> (H V lv) ptr_1)
   (H-read H ptr_1 (ref _ ptr_2))
   ------ "EL-Deref"
   (lv--> (H V (* lv)) ptr_2)]

  [(lv--> (H V lv) ptr_1)
   (H-read H ptr_1 (own a_2))
   ------ "EL-Deown"
   (lv--> (H V (* lv)) a_2)])

(module+ test
  (test-judgment-holds (lv--> (,H1 ,V1 x_0)         a_0))
  (test-judgment-holds (lv--> (,H1 ,V1 (* x_0))     a_1))
  (test-judgment-holds (lv--> (,H1 ,V1 (* (* x_0))) a_2))
  (test-judgment-holds (lv--> (,H2 ,V2 x_1)         a_3)))


(define RRR
  (reduction-relation Rust+V
   #:domain (H V e)

   (--> (H   V (in-hole E lv))
        (H_2 V (in-hole E v))
        "Use"
        (judgment-holds (lv--> (H V lv) ptr))
        (judgment-holds (H-read H ptr v))
        (judgment-holds (H-write H ptr (use v) H_2)))

   (--> (H V (in-hole E (ref ℓ q lv)))
        (H V (in-hole E (ref q ptr)))
        "Ref"
        (judgment-holds (lv--> (H V lv) ptr)))

   (--> (H   V   (in-hole E (let ℓ ([x v]) e)))
        (H_2 V_2 (in-hole E (pop [x] e)))
        "Let"
        (fresh a)
        (where ([a_1 v_1] ...) H)
        (where ([x_2 a_2] ...) V)
        (where H_2 ([a v] [a_1 v_1] ...))
        (where V_2 ([x a] [x_2 a_2] ...)))

   (--> (H   V   (in-hole E (pop [x] v)))
        (H_2 V_2 (in-hole E v))
        "Pop"
        (where [a] (find x V))
        (where H_2 (rem a H))
        (where V_2 (rem x V)))

   (--> (H V (in-hole E (do v_1 ... v_2)))
        (H V (in-hole E v_2))
        "Do")

   (--> (H   V (in-hole E (set! lv v)))
        (H_2 V (in-hole E unit))
        "Set"
        (judgment-holds (lv--> (H V lv) ptr))
        (judgment-holds (H-write H ptr v H_2)))

   (--> (H   V (in-hole E (new v)))
        (H_2 V (in-hole E (own a)))
        "New"
        (fresh a)
        (where ([a_1 v_1] ...) H)
        (where H_2 ([a v] [a_1 v_1] ...)))

   ))

(module+ test
  (test--> RRR
    (term (,H1 ,V1 (ref ℓ IMM x_0)))
    (term (,H1 ,V1 (ref IMM a_0))))
  (test--> RRR
    (term (,H1 ,V1 (ref ℓ IMM (* x_0))))
    (term (,H1 ,V1 (ref IMM a_1))))
  (test--> RRR
    (term (,H1 ,V1 (do 1 2 3)))
    (term (,H1 ,V1 3)))
  (test--> RRR
    (term (,H2 ,V2 (set! x_1 8)))
    (term (,H3 ,V2 unit)))
  (test--> RRR
    (term (,H1 ,V1 x_0))
    (term (,H4 ,V1 (own a_1)))))

(module+ test
  (test-results))
