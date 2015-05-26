#lang racket/base
(require racket/function racket/generator rackunit racket/list sugar/define sugar/debug sugar/list)


(define variable? (λ(x) (or (string? x) (number? x) (symbol? x))))
(define value? (λ(x) #t))
(define (listof? proc) (λ(x) (and (list? x) (andmap proc x))))
(define (pairof? proc1 proc2) (λ(x) (and (pair? x) (proc1 (car x)) (proc2 (cdr x)))))
(define domain? (listof? string?))
(define variable-domain-pair? (pairof? variable? domain?))

(define (empty-assignment) (hash))
(define assignment-variables hash-keys)
(define assignment-values hash-values)
(define assignment-set hash-set)
(define assignment-ref hash-ref)
(define assignment-has-variable? hash-has-key?)
(define assignment? (λ(x) (and (hash? x) (andmap variable? (assignment-variables x)) (andmap value? (assignment-values x)))))

(define scope? (listof? variable?))
(define relation? procedure?)
(define constraint? (pairof? scope? relation?))
(define constraint-scope car)
(define constraint-relation cdr)
(struct problem (variables domains constraints [variables-ordered #:auto]) #:transparent #:auto-value empty #:mutable)
(define natural? exact-nonnegative-integer?)

(define current-ordering-heuristic (make-parameter 'degree))

(define/contract (assignment-complete? prob assn)
  (problem? assignment? . -> . boolean?)
  (andmap (curry assignment-has-variable? assn) (problem-variables prob)))


;; which variable should be assigned next?
;; for now, just take the first available.
(define/contract (get-unassigned-variable prob assn)
  (problem? assignment? . -> . (or/c #f variable?))
  (let* ([vars (problem-variables-ordered prob)]
         [vars (if (empty? vars) (problem-variables prob) vars)])
    (for/first ([var (in-list vars)]
                #:when (not (assignment-has-variable? assn var)))
      var)))


;; in what order should possible values be tried?
(define/contract (get-sorted-domain-values prob assn unassigned-var)
  (problem? assignment? variable? . -> . (listof value?))
  (define var-domain (for/first ([(var domain) (in-parallel (problem-variables prob) (problem-domains prob))]
                                 #:when (equal? unassigned-var var))
                       domain))
  (define sort-domain identity) ; for now, no reordering
  (if var-domain
      (sort-domain var-domain)
      (error 'get-sorted-domain-values "No domain found for ~a" unassigned-var)))


;; would the proposed new value break any constraints?
(define/contract (value-consistent? prob assn new-var proposed-val)
  (problem? assignment? variable? value? . -> . boolean?)
  (define assn-to-test (assignment-set assn new-var proposed-val))
  ;; select every constraint whose scope is a subset of assigned vars + new-var
  ;; not actually going to use `subset?` because it's slow, `member` is fast
  ;; keep testing constraints till one fails
  (for/and ([c (in-list (problem-constraints prob))] 
            #:when (andmap (curryr member (assignment-variables assn-to-test)) (constraint-scope c))) 
    (define assn-vals-to-test (map (curry assignment-ref assn-to-test) (constraint-scope c)))
    (apply (constraint-relation c) assn-vals-to-test)))


(define/contract (order-variables prob)
  (problem? . -> . (listof variable?))
  (case (current-ordering-heuristic)
    ['(degree) ; degree heuristic: sort vars from most constrained to least
     (define var-degree-pairs (hash->list (frequency-hash (append-map constraint-scope (problem-constraints prob)))))
     (map car (sort var-degree-pairs > #:key cdr))]
    [else ; no ordering
     (problem-variables prob)]))

(define/contract (backtracking-generator prob)
  (problem? . -> . generator?)
  
  ;; order variables for every invocation of the solver (not when creating problem)
  ;; because constraints may change
  (set-problem-variables-ordered! prob (order-variables prob)) 
  
  (generator ()
             (let assign-next-var ([prob prob] [assn (empty-assignment)])
               (define unassigned-var (get-unassigned-variable prob assn))
               (cond
                 [(not unassigned-var) (yield assn)] ; assignment is complete, thus we are done
                 [else
                  (for ([possible-val (in-list (get-sorted-domain-values prob assn unassigned-var))]
                        #:when (value-consistent? prob assn unassigned-var possible-val))
                    ;; todo: add inference checking
                    (define new-assn (assignment-set assn unassigned-var possible-val))
                    (assign-next-var prob new-assn))]))))


(define/contract (get-solution-generator prob solver)
  (problem? procedure? . -> . generator?)
  (solver prob))


(define/contract (get-solution prob solver)
  (problem? procedure? . -> . (or/c #f assignment?))
  (define results (get-solutions prob solver #:count 1))
  (and (not (empty? results)) (car results)))


(define/contract (get-solutions prob solver #:count [count +inf.0])
  ((problem? procedure?) (#:count natural?) . ->* . (listof assignment?))
  (for/list ([solution (in-producer (get-solution-generator prob solver) (void))]
             ;; #:final is better than #:when because it avoids generating a superfluous solution at the end
             [index (in-naturals)] #:final (= (add1 index) count))
    solution))


(module+ test
  (define prob (problem (list "foo" "zim") (list (range 10) (range 5)) '()))
  (check-true (assignment-complete? prob '#hash(("foo" . bar) ("zim" . zam))))
  (check-false (assignment-complete? prob '#hash(("foo" . bar))))
  (check-false (get-unassigned-variable prob '#hash(("foo" . bar) ("zim" . zam))))
  (check-equal? (get-unassigned-variable prob '#hash(("foo" . bar))) "zim")
  (check-equal? (get-sorted-domain-values prob '#hash(("foo" . bar)) "zim") '(0 1 2 3 4))
  (check-exn exn:fail? (λ _ (get-sorted-domain-values prob '#hash(("foo" . bar) ("zim" . zam)) "not-in-vars"))))

(define (check-hash-items h1 h2)
  (check-true (for/and ([(k v) (in-hash h1)])
                (equal? (hash-ref h2 k) v))))



;; ABC problem:
;; what is the minimum value of

;;       ABC
;;     -------
;;      A+B+C

(define abc-problem (problem '("a" "b" "c") (make-list 3 (range 1 10)) empty))
(define (test-solution s) (let ([a (hash-ref s "a")]
                                [b (hash-ref s "b")]
                                [c (hash-ref s "c")])
                            (/ (+ (* 100 a) (* 10 b) c) (+ a b c))))




;; quarter problem:
;; 26 coins, dollars and quarters
;; that add up to $17.
(define quarter-problem (problem '("dollars" "quarters") (make-list 2 (range 1 27))
                                 (list (cons '("dollars" "quarters") (λ(d q) (= 17 (+ d (* 0.25 q)))))
                                       (cons '("dollars" "quarters") (λ(d q) (= 26 (+ d q)))))))



;; coin problem 2
#|
A collection of 33 coins, consisting of nickels, dimes, and quarters, has a value of $3.30. If there are three times as many nickels as quarters, and one-half as many dimes as nickels, how many coins of each kind are there?
|#
(define nickel-problem (problem '(nickels dimes quarters) (make-list 3 (range 1 34))
                                (list
                                 (cons '(nickels dimes quarters) (λ(n d q) (= 33 (+ n d q))))
                                 (cons '(nickels dimes quarters) (λ(n d q) (= 3.30 (+ (* 0.05 n) (* 0.1 d) (* 0.25 q)))))
                                 (cons '(nickels quarters) (λ(n q) (= n (* 3 q))))
                                 (cons '(dimes nickels) (λ(d n) (= n (* 2 d)))))))


(time-repeat 25
             (check-hash-items (argmin test-solution (get-solutions abc-problem backtracking-generator))
                               #hash(("c" . 9) ("b" . 9) ("a" . 1)))
             (check-hash-items (get-solution nickel-problem backtracking-generator) #hash((nickels . 18) (quarters . 6) (dimes . 9)))
             (check-hash-items (get-solution quarter-problem backtracking-generator) #hash(("dollars" . 14) ("quarters" . 12))))

(parameterize ([current-ordering-heuristic #f])
  (time-repeat 25
               (check-hash-items (argmin test-solution (get-solutions abc-problem backtracking-generator))
                                 #hash(("c" . 9) ("b" . 9) ("a" . 1)))
               (check-hash-items (get-solution nickel-problem backtracking-generator) #hash((nickels . 18) (quarters . 6) (dimes . 9)))
               (check-hash-items (get-solution quarter-problem backtracking-generator) #hash(("dollars" . 14) ("quarters" . 12)))))



#|
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


(define two-four-problem (new problem%))
(send two-four-problem add-variables '(t w o f u r) (range 10))
(send two-four-problem add-constraint (new all-different-constraint%))
(send two-four-problem add-constraint (λ(t w o) (> (word-value t w o) 99)) '(t w o))
(send two-four-problem add-constraint (λ(f o u r) (> (word-value f o u r) 999)) '(f o u r))
(send two-four-problem add-constraint 
      (λ (t w o f u r)
        (let ([two (word-value t w o)]
              [four (word-value f o u r)])
          ((two . + . two) . = . four))) '(t w o f u r))
(check-equal? (length (send two-four-problem get-solutions)) 7)
(send two-four-problem add-constraint (λ(r) (= r 0)) '(r))
(check-hash-items (send two-four-problem get-solution) #hash((o . 5) (w . 6) (u . 3) (f . 1) (r . 0) (t . 7)))


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

(define xsum-problem (new problem%))
(send xsum-problem add-variables '(l1 l2 l3 l4 r1 r2 r3 r4 x) (range 10))
(send xsum-problem add-constraint (λ (l1 l2 l3 l4 x) 
                                   (and (< l1 l2 l3 l4)
                                        (= 27 (+ l1 l2 l3 l4 x)))) '(l1 l2 l3 l4 x))
(send xsum-problem add-constraint (λ (r1 r2 r3 r4 x) 
                                   (and (< r1 r2 r3 r4)
                                        (= 27 (+ r1 r2 r3 r4 x)))) '(r1 r2 r3 r4 x))
(send xsum-problem add-constraint (new all-different-constraint%))
(check-equal? (length (send xsum-problem get-solutions)) 8)



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

(define sm-problem (new problem%))
(send sm-problem add-variables '(s e n d m o r y) (range 10))
(send sm-problem add-constraint (λ(x) (> x 0)) '(s))
(send sm-problem add-constraint (λ(x) (> x 0)) '(m))
(send sm-problem add-constraint (λ(d e y) (= (modulo (+ d e) 10) y)) '(d e y))
(send sm-problem add-constraint (λ(n d r e y)
                                 (= (modulo (+ (word-value n d) (word-value r e)) 100)
                                    (word-value e y))) '(n d r e y))
(send sm-problem add-constraint (λ(e n d o r y)
                                 (= (modulo (+ (word-value e n d) (word-value o r e)) 1000) (word-value n e y))) '(e n d o r y))
(send sm-problem add-constraint (λ(s e n d m o r y) (=
                                                    (+ (word-value s e n d)
                                                       (word-value m o r e))
                                                    (word-value m o n e y))) '(s e n d m o r y))
(send sm-problem add-constraint (new all-different-constraint%))

(check-hash-items (send sm-problem get-solution) '#hash((m . 1) (e . 5) (r . 8) (n . 6) (y . 2) (o . 0) (d . 7) (s . 9)))


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