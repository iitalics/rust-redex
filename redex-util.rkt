#lang racket/base
(require redex/reduction-semantics)
(provide Base find)

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

(module+ test
  (test-results))
