#lang racket/base
(require redex/reduction-semantics
         (only-in racket/list remf splitf-at))
(provide Base
         find rem chg)

(define-language Base)

;; -----------------------------
;; various useful metafunctions

(define-metafunction Base
  ;; given key k and list l, returns [v] for the first pair [k v] in l,
  ;; or #f if not found
  find : any ([any any] ...) -> [any] or #f
  [(find any_k any_l) [any_v]
   (where [_ any_v] ,(assoc (term any_k) (term any_l)))]
  [(find _ _) #f])

(module+ test
  (test-equal (term (find x ([y 3] [x 4] [x 5]))) '[4])
  (test-equal (term (find z ([y 3] [x 4] [x 5]))) #f))

(define-metafunction Base
  ;; given key k and list l, remove first pair [k v] from l
  rem : any (any ...) -> (any ...)
  [(rem any_k any_l) ,(remf (λ (p) ((default-equiv)
                                    (car p)
                                    (term any_k)))
                            (term any_l))])

(module+ test
  (test-equal (term (rem x ([y 2] [x 4] [x 6]))) (term ([y 2] [x 6])))
  (test-equal (term (rem z ([y 2] [x 4] [x 6]))) (term ([y 2] [x 4] [x 6]))))

(define-metafunction Base
  ;; given key k and value v, and list l, replaces first [k v0] with [k v]
  chg : any any ([any any] ...) -> ([any any] ...)
  [(chg any_k any_v any_l)
   ,(let-values ([(l r) (splitf-at (term any_l)
                                   (λ (p) (not ((default-equiv)
                                                (car p)
                                                (term any_k)))))])
      (append l (term ([any_k any_v])) (cdr r)))])

(module+ test
  (test-equal (term (chg x 9 ([y 3] [x 4] [x 5])))
              (term ([y 3] [x 9] [x 5]))))

(module+ test
  (test-results))
