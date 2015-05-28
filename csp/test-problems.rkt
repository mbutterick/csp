#lang racket/base
(require racket/function racket/generator rackunit racket/list sugar/define sugar/debug sugar/list "problem.rkt" "solver.rkt" "world.rkt")
(provide (all-defined-out))

;; map problem in AINA

(define map2
  (make-problem
   (make-variables ['(WA NT SA Q NSW V T) '(r g b)])
   (make-constraints ['((WA NT) (Q NT) (SA NT) (Q NSW) (NSW V) (SA V) (SA Q) (SA NSW) (SA WA)) (negate equal?)])))

(module+ test
  (check-hash-items (solve map2 backtracking-solver)
                    '#hash((T . r) (WA . r) (NT . g) (SA . b) (Q . r) (NSW . g) (V . r))))

;; ABC problem:
;; what is the minimum value of

;;       ABC
;;     -------
;;      A+B+C

(define abc-problem (make-problem (make-variables ['("a" "b" "c") (range 1 10)])))
(define (test-solution s) (let ([a (solution-ref s "a")]
                                [b (solution-ref s "b")]
                                [c (solution-ref s "c")])
                            (/ (+ (* 100 a) (* 10 b) c) (+ a b c))))
(module+ test
  (check-hash-items (argmin test-solution (solve* abc-problem)) #hash(("c" . 9) ("b" . 9) ("a" . 1))))


;; quarter problem:
;; 26 coins, dollars and quarters
;; that add up to $17.

(define quarter-problem (make-problem
                         (make-variables ['("dollars" "quarters") (range 1 27)])
                         (make-constraints
                          ['("dollars" "quarters") (λ(d q) (= 26 (+ d q)))]
                          ['("dollars" "quarters") (λ(d q) (= 17 (+ d (* 0.25 q))))])))

(module+ test
  (check-hash-items (solve quarter-problem) '#hash(("dollars" . 14) ("quarters" . 12))))


;; coin problem 2
#|
A collection of 33 coins, consisting of nickels, dimes, and quarters, has a value of $3.30. If there are three times as many nickels as quarters, and one-half as many dimes as nickels, how many coins of each kind are there?
|#
(define nickel-problem (make-problem (make-variables ['(nickels dimes quarters) (range 1 34)])
                             (make-constraints
                              ['(nickels) even?]
                              ['(nickels dimes quarters) (λ(n d q) (= 33 (+ n d q)))]
                              ['(nickels dimes quarters) (λ(n d q) (= 3.30 (+ (* 0.05 n) (* 0.1 d) (* 0.25 q))))]
                              ['(nickels quarters) (λ(n q) (= n (* 3 q)))]
                              ['(dimes nickels) (λ(d n) (= n (* 2 d)))])))

(module+ test
  (check-hash-items (solve nickel-problem) #hash((nickels . 18) (quarters . 6) (dimes . 9))))


;; word math
#|
# Assign equal values to equal letters, and different values to
# different letters, in a way that satisfies the following sum:
#
#    TWO
#  + TWO
#  -----
#   FOUR
|#


(define two-four-problem (make-problem
                          (make-variables ['(t w o f u r) (range 10)])
                          (make-constraints
                           ['(r) zero?]
                           ['(t) positive?]
                           ['(f) positive?]
                           ['(t w o f u r) (λ (t w o f u r)
                                             (let ([two (word-value t w o)]
                                                   [four (word-value f o u r)])
                                               ((two . + . two) . = . four)))]
                           ['() all-different?])))
;(check-equal? (length (send two-four-problem get-solutions)) 7)
;(send two-four-problem add-constraint )
;(check-hash-items (send two-four-problem get-solution) #hash((o . 5) (w . 6) (u . 3) (f . 1) (r . 0) (t . 7)))

(define (print-two-four s)
  (displayln (apply format "  ~a~a~a\n+ ~a~a~a\n-----\n ~a~a~a~a"
                    (map (curry hash-ref s) '(t w o t w o f o u r)))))

(module+ test
  (check-hash-items (solve two-four-problem) #hash((o . 5) (w . 6) (u . 3) (f . 1) (r . 0) (t . 7))))


;; xsum
#|
# Reorganize the following numbers in a way that each line of
# 5 numbers sum to 27.
#
#       1   6
#        2 7
#         3
#        8 4
#       9   5
#
|#


(define xsum-problem (make-problem
                      (make-variables ['(l1 l2 l3 l4 r1 r2 r3 r4 x) (range 10)])
                      (make-constraints
                       ['(l1 l2 l3 l4 x) (λ (l1 l2 l3 l4 x) 
                                           (and (< l1 l2 l3 l4)
                                                (= 27 (+ l1 l2 l3 l4 x))))]
                       ['(r1 r2 r3 r4 x) (λ (r1 r2 r3 r4 x) 
                                           (and (< r1 r2 r3 r4)
                                                (= 27 (+ r1 r2 r3 r4 x))))]
                       ['() all-different?])))

;(check-equal? (length (solve* xsum-problem)) 8)






;; send more money problem
#|
# Assign equal values to equal letters, and different values to
# different letters, in a way that satisfies the following sum:
#
#    SEND
#  + MORE
#  ------
#   MONEY
|#

(define sm-problem (make-problem
                    (make-variables
                     ['(s e n d m o r y) (range 10)])
                    (make-constraints
                     ['(s) (λ(x) (> x 0))]
                     ['(m) (λ(x) (> x 0))]
                     ['(d e y) (λ(d e y) (= (modulo (+ d e) 10) y))]
                     ['(n d r e y) (λ(n d r e y)
                                     (= (modulo (+ (word-value n d) (word-value r e)) 100)
                                        (word-value e y)))]
                     ['(e n d o r y) (λ(e n d o r y)
                                       (= (modulo (+ (word-value e n d) (word-value o r e)) 1000) (word-value n e y)))]
                     ['(s e n d m o r y) (λ(s e n d m o r y) (=  (+ (word-value s e n d)
                                                                    (word-value m o r e))
                                                                 (word-value m o n e y)))]
                     ['() all-different?])))

(module+ test
  (check-hash-items (solve sm-problem) '#hash((m . 1) (e . 5) (r . 8) (n . 6) (y . 2) (o . 0) (d . 7) (s . 9))))


#|
;; queens problem
;; place queens on chessboard so they do not intersect

(define queens-problem (new problem%))
(define cols (range 8))
(define rows (range 8))
(send queens-problem add-variables cols rows)
(for* ([col1 (in-list cols)] [col2 (in-list cols)] #:when (< col1 col2))
  (send queens-problem add-constraint (λ(row1 row2 [col1 col1][col2 col2])
                                        (and 
                                         ;; test if two cells are on a diagonal
                                         (not (= (abs (- row1 row2)) (abs (- col1 col2))))
                                         ;; test if two cells are in same row
                                         (not (= row1 row2)))) (list col1 col2))) 
(check-equal? (length (send queens-problem get-solutions)) 92)

(module+ main
  (displayln "Tests passed"))

|#