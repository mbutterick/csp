#lang racket/base
(require racket/function racket/generator rackunit racket/list sugar/define sugar/debug sugar/list)


(define variable? (λ(x) (or (string? x) (number? x) (symbol? x))))
(define value? (λ(x) #t))
(define (listof? proc) (λ(x) (and (list? x) (andmap proc x))))
(define (pairof? proc1 proc2) (λ(x) (and (pair? x) (proc1 (car x)) (proc2 (cdr x)))))
(define (hashof? keyproc valproc) (λ(x) (and (hash? x) (andmap keyproc (hash-keys x)) (andmap valproc (hash-values x)))))
(define domain? (listof? value?))


(define (empty-assignment) (hash))
(define assignment-variables hash-keys)
(define assignment-values hash-values)
(define assignment-set hash-set)
(define assignment-ref hash-ref)
(define assignment-has-variable? hash-has-key?)
(define assignment? (hashof? variable? value?))

(define scope? (listof? variable?))
(define relation? procedure?)
(struct constraint (scope relation-code relation) #:transparent #:omit-define-syntaxes
  #:constructor-name new-constraint)
(define-syntax-rule (constraint scope-vars relation)
  (new-constraint scope-vars 'relation relation))


(define vardom? (hashof? variable? domain?))
(define vardom-ref hash-ref)
(define vardom-domains hash-values)
(define vardom-variables hash-keys)
(define vardom-set hash-set)
(struct problem (vardom constraints) #:transparent)
(define natural? exact-nonnegative-integer?)
(define solution-ref hash-ref)
(define solution? (hashof? variable? value?))

(define current-ordering-heuristic (make-parameter 'degree))

#;(define/contract (assignment-complete? prob assn)
    (problem? assignment? . -> . boolean?)
    (andmap (curry assignment-has-variable? assn) (problem-variables prob)))


;; which variable should be assigned next?
(define/contract (select-unassigned-variable prob)
  (problem? . -> . (or/c #f variable?))
  (define ordered-unassigned-vars
    (let ([unassigned-vars (for/list ([(var dom) (in-hash (problem-vardom prob))]
                                      #:when (> (length dom) 1)) ; if length = 1, it's assigned
                             var)])
      (if (empty? unassigned-vars)
          empty
          (case (current-ordering-heuristic)
            ['(degree) ; degree heuristic: sort vars from most constrained to least
             (define var-degree-table (frequency-hash (append-map constraint-scope (problem-constraints prob))))
             (define unassigned-var-degree-pairs (map (λ(var) (cons var (hash-ref var-degree-table var))) unassigned-vars))
             (map car (sort unassigned-var-degree-pairs > #:key cdr))]
            ['(mrv) ; MRV heuristic: sort vars from smallest domain to largest
             (define var-domainsize-pairs (for/list ([uv (in-list unassigned-vars)])
                                            (cons uv (length (problem-vardom uv)))))
             (map car (sort var-domainsize-pairs < #:key cdr))]
            [else ; no ordering
             unassigned-vars]))))
  (and (not (empty? ordered-unassigned-vars)) (car ordered-unassigned-vars)))


;; in what order should possible values be tried?
(define/contract (get-sorted-domain-values prob unassigned-var)
  (problem? variable? . -> . (listof value?))
  (define unassigned-var-domain (vardom-ref (problem-vardom prob) unassigned-var))
  unassigned-var-domain) ; for now, no reordering

(define/contract (get-assigned-variables prob)
  (problem? . -> . (listof variable?))
  (for/list ([(var dom) (in-hash (problem-vardom prob))]
             #:when (= 1 (length dom)))
    var))

;; would the proposed new value break any constraints?
(define/contract (value-consistent? prob new-var proposed-val)
  (problem? variable? value? . -> . boolean?)
  (define assigned-vars (cons new-var (get-assigned-variables prob)))
  ;; take the current vardom and udpate with the new assignment
  (define updated-vardom (vardom-set (problem-vardom prob) new-var (list proposed-val)))
  ;; select every constraint whose scope includes new-var plus some subset of assigned vars
  ;; not actually going to use `subset?` because it's slow, `member` is fast
  ;; keep testing constraints till one fails
  (for/and ([c (in-list (problem-constraints prob))] 
            #:when (let ([scope-vars (constraint-scope c)])
                     (and (member new-var scope-vars) ; new-var must be in scope
                          ; only care about scopes using assigneed vars 
                          (andmap (curryr member assigned-vars) scope-vars))))
    ;; since we are testing only assigned vars, each domain will have only one value
    (define vals-to-test (map (compose1 first (curry vardom-ref updated-vardom)) (constraint-scope c)))
    (apply (constraint-relation c) vals-to-test)))


#;(define/contract (order-variables prob)
    (problem? . -> . (listof variable?))
    (case (current-ordering-heuristic)
      ['(degree) ; degree heuristic: sort vars from most constrained to least
       (define var-degree-pairs (hash->list (frequency-hash (append-map constraint-scope (problem-constraints prob)))))
       (map car (sort var-degree-pairs > #:key cdr))]
      [else ; no ordering
       (problem-variables prob)]))

(define/contract (problem-solved? prob)
  (problem? . -> . boolean?)
  (andmap (curry = 1) (map length (vardom-domains (problem-vardom prob)))))


(define/contract (add-assignment-to-problem prob var val)
  (problem? variable? value? . -> . problem?)
  (problem (vardom-set (problem-vardom prob) var (list val)) (problem-constraints prob)))


(define/contract (problem->solution prob)
  (problem? . -> . solution?)
  (for/hash ([(var vals) (in-hash (problem-vardom prob))])
    (values var (car vals))))

(define/contract (backtracking-generator prob)
  (problem? . -> . generator?)
  (generator ()
             (let loop ([prob prob])
               (cond
                 [(problem-solved? prob) (yield (problem->solution prob))]
                 [else
                  (let ([unassigned-var (select-unassigned-variable prob)])
                    (for ([possible-val (in-list (get-sorted-domain-values prob unassigned-var))]
                          #:when (value-consistent? prob unassigned-var possible-val))
                      (loop (add-assignment-to-problem prob unassigned-var possible-val))))]))))


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


#;(module+ test
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


(define/contract (make-problem vardom-pairs [constraint-pairs empty])
  (((listof (or/c variable? domain?))) ((listof constraint?)) . ->* . problem?)
  (define vardom-table (apply hash vardom-pairs))
  (problem vardom-table constraint-pairs))

(define abc-problem (make-problem (list "a" (range 1 10)
                                        "b" (range 10)
                                        "c" (range 10))))
(define (test-solution s) (let ([a (solution-ref s "a")]
                                [b (solution-ref s "b")]
                                [c (solution-ref s "c")])
                            (/ (+ (* 100 a) (* 10 b) c) (+ a b c))))


(check-hash-items (argmin test-solution (get-solutions abc-problem backtracking-generator))
                  #hash(("c" . 9) ("b" . 9) ("a" . 1)))

;; quarter problem:
;; 26 coins, dollars and quarters
;; that add up to $17.



(define quarter-problem (make-problem
                         (list "dollars" (range 1 27) "quarters" (range 1 27))
                         (list (constraint '("dollars" "quarters") (λ(d q) (= 17 (+ d (* 0.25 q)))))
                               (constraint '("dollars" "quarters") (λ(d q) (= 26 (+ d q)))))))



;; coin problem 2
#|
A collection of 33 coins, consisting of nickels, dimes, and quarters, has a value of $3.30. If there are three times as many nickels as quarters, and one-half as many dimes as nickels, how many coins of each kind are there?
|#
(define nickel-problem (make-problem (list 'nickels (range 1 34)
                                           'dimes (range 1 34)
                                           'quarters (range 1 34))
                                     (list
                                      (constraint '(nickels dimes quarters) (λ(n d q) (= 33 (+ n d q))))
                                      (constraint '(nickels dimes quarters) (λ(n d q) (= 3.30 (+ (* 0.05 n) (* 0.1 d) (* 0.25 q)))))
                                      (constraint '(nickels quarters) (λ(n q) (= n (* 3 q))))
                                      (constraint '(dimes nickels) (λ(d n) (= n (* 2 d)))))))

(define (quick-test)
  (time-repeat 25
               (check-hash-items (argmin test-solution (get-solutions abc-problem backtracking-generator))
                                 #hash(("c" . 9) ("b" . 9) ("a" . 1)))
               (check-hash-items (get-solution nickel-problem backtracking-generator) #hash((nickels . 18) (quarters . 6) (dimes . 9)))
               (check-hash-items (get-solution quarter-problem backtracking-generator) #hash(("dollars" . 14) ("quarters" . 12)))))

(parameterize ([current-ordering-heuristic 'degree])
  (quick-test))

(parameterize ([current-ordering-heuristic 'mrv])
  (quick-test))

(parameterize ([current-ordering-heuristic #f])
  (quick-test))



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