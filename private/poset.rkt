#lang racket/base
(require redex/reduction-semantics
         "redex-util.rkt")

(provide poset<= poset< pos-≤ pos-<)

;; returns #t if x ≤ y according to the partially ordered
;; set 'po'. the set is represented as a list of (cons a bs),
;; which indicates that a < b for each b in bs
;; poset<= : [listof [listof X]] X X -> Boolean
(define (poset<= pos x y #:equal? [=? equal?])
  (or (=? x y)
      (poset< pos x y #:equal? =?)))

;; like poset<=, but only returns #t if x < y
;; poset<= : [listof [listof X]] X X -> Boolean
(define (poset< pos x y #:equal? [=? equal?])
  (cond
    [(assoc x pos)
     => (λ (rel)
          (for/or ([x- (in-list (cdr rel))])
            (poset<= pos x- y #:equal? =?)))]
    [else #f]))

(module+ test
  (define pos '([b c d] [a b] [e b]))
  (test-equal (poset<= pos 'a 'a) #t)
  (test-equal (poset< pos 'a 'a) #f)
  (test-equal (poset<= pos 'a 'b) #t)
  (test-equal (poset<= pos 'a 'c) #t)
  (test-equal (poset<= pos 'a 'd) #t)
  (test-equal (poset<= pos 'a 'e) #f)
  (test-equal (poset<= pos 'e 'a) #f)
  (test-equal (poset<= pos 'e 'd) #t)
  )

(define-metafunction Base
  pos-≤ : ([any < any ...] ...) any any -> boolean
  [(pos-≤ ([any_1 < any_2 ...] ...) any_l any_r)
   ,(poset<= (term ([any_1 any_2 ...] ...))
             (term any_l)
             (term any_r)
             #:equal? (default-equiv))])

(define-metafunction Base
  pos-< : ([any < any ...] ...) any any -> boolean
  [(pos-< ([any_1 < any_2 ...] ...) any_l any_r)
   ,(poset< (term ([any_1 any_2 ...] ...))
            (term any_l)
            (term any_r)
            #:equal? (default-equiv))])

(module+ test
  (define P (term ([b < c d] [a < b] [e < b])))
  (test-equal (term (pos-≤ ,P e e)) #t)
  (test-equal (term (pos-< ,P e d)) #t)
  (test-equal (term (pos-< ,P e a)) #f)
  (test-results))
