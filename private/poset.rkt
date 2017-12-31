#lang racket/base
(require racket/dict)
(provide poset?
         make-poset
         make-poseteq
         poset-contains?
         poset-add!
         poset-add*!
         poset-<= (rename-out [poset-<= poset-≤])
         poset-copy)

;; --------------------------------------------------------------
;; data structure for partially ordered set (PO-Set)

(struct poset [=? elems])

(define (make-poset/roots #:dict make-dict
                          #:equal? =?
                          roots)
  (define pos
    (poset =? (make-dict)))
  (for ([x (in-list roots)])
    (poset-add! pos x))
  pos)

;; X ... -> [poset-of X]
;; construct a new PO-Set, with any additional args as initial
;; maximal elements.
(define (make-poset #:dict [make-dict make-hash]
                    #:equal? [=? equal?]
                    . roots)
  (make-poset/roots #:dict make-dict
                    #:equal? =?
                    roots))

;; X ... -> [poset-of X]
;; construct a new PO-Set using eq? to compare elements
(define (make-poseteq . roots)
  (make-poset/roots #:dict make-hasheq
                    #:equal? eq?
                    roots))

;; [poset-of X] X -> Bool
;; does the given poset contain the given element?
(define (poset-contains? pos x)
  (dict-has-key? (poset-elems pos) x))

;; [poset-of X] X [listof X] -> Void
;; add element x to poset, such that each y in ys is greater than x
(define (poset-add*! pos x ys)
  (when (poset-contains? pos x)
    (error 'poset-add! "poset already contains element" x))
  (dict-set! (poset-elems pos) x ys))

;; [poset-of X] X X ... -> Void
;; add element x to poset, such that each y in ys is greater than x
(define (poset-add! pos x . ys)
  (poset-add*! pos x ys))

;; [poset-of X] X X -> Boolean
;; [poset-of X] -> [X X -> Boolean]
;; check the ordering between two elements
(define poset-<=
  (case-lambda
    [(pos) (λ (x y) (poset-<= pos x y))]
    [(pos x y)
     (define =? (poset-=? pos))
     (let trav ([xs (list x)])
       (for/or ([x (in-list xs)])
         (or (=? x y)
             (trav (dict-ref (poset-elems pos) x)))))]))

;; [poset-of X] -> [poset-of X]
(define (poset-copy pos)
  (poset (poset-=? pos)
         (dict-copy (poset-elems pos))))


;; ------------------------------
;; tests

(module+ test
  (require rackunit)
  (define P (make-poseteq 'z))
  (poset-add! P 'y 'z)
  (poset-add! P 'x 'y)
  (poset-add! P 'w 'y)
  (define ≤ (poset-<= P))
  (for ([s '(x y z w)])
    (check-true (≤ s s)))
  (for ([a '(x x y w w)]
        [b '(y z z y z)])
    (check-true (≤ a b))
    (check-false (≤ b a))))
