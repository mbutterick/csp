#lang racket/base
(require racket/generator racket/list rackunit "problem.rkt" "world.rkt" sugar/list racket/function)
(require (rename-in racket/base [define define/contract]) (except-in racket/contract define/contract))
(provide (all-defined-out))

(define/contract (sort-unassigned-variables prob)
  (problem? . -> . (listof variable?))
  (define unassigned-vars (get-unassigned-variables prob))
  (if (empty? unassigned-vars)
      empty
      (case (current-ordering-heuristic)
        [(degree) ; degree heuristic: take var involved in most constraints
         (define var-degree-table (frequency-hash (append-map constraint-scope (problem-constraints prob))))
         (sort unassigned-vars > #:key (λ(uv) (curryr hash-ref var-degree-table uv 0)))]
        [(mrv) ; MRV heuristic: take var with smallest domain
         (sort unassigned-vars < #:key (λ(uv) (length (vardom-ref (problem-vardom prob) uv))))]
        [else ; no ordering
         unassigned-vars])))

;; which variable should be assigned next?
(define/contract (next-unassigned-variable prob vars)
  (problem? (listof variable?) . -> . (or/c #f variable?))
  (for/first ([var (in-list vars)]
              #:unless (variable-assigned? prob var))
    var))

(define/contract (backtracking-solver prob)
  (problem? . -> . generator?)
  (define vars-to-assign (sort-unassigned-variables prob))
  (generator ()
             (let loop ([prob prob])
               (cond
                 [(all-vars-assigned? prob)
                  (if (var-assignments-consistent? prob)
                      (yield (problem->solution prob))
                      (error 'backtracking-solver (format "got complete but inconsistent assignment: ~a" (problem->solution prob))))]
                 [else (define unassigned-var (next-unassigned-variable prob vars-to-assign))
                       (for ([possible-val (in-list (get-sorted-domain-values prob unassigned-var))]
                             #:when (value-consistent? prob unassigned-var possible-val))
                         (define updated-problem (assign-and-infer prob unassigned-var possible-val))
                         (when updated-problem
                           (loop updated-problem)))]))))

(define bts backtracking-solver)

(define/contract (get-solution-generator prob solver)
  (problem? procedure? . -> . generator?)
  (solver prob))


(define/contract (solve prob [solver backtracking-solver])
  ((problem?) (procedure?) . ->* . (or/c #f solution?))
  (define results (solve* prob solver #:count 1))
  (and (not (empty? results)) (car results)))


(define/contract (solve* prob [solver backtracking-solver] #:count [count +inf.0])
  ((problem?) (procedure? #:count natural?) . ->* . (listof solution?))
  (for/list ([solution (in-producer (get-solution-generator prob solver) (void))]
             ;; #:final is better than #:when because it avoids generating a superfluous solution at the end
             [index (in-naturals)] #:final (= (add1 index) count))
    solution))


(define-simple-check (check-hash-items h1 h2)
  (for/and ([(k1 v1) (in-hash h1)])
    (equal? (hash-ref h2 k1) v1)))

(require racket/format racket/string)
(define (word-value . xs)
  (string->number (string-append* (map ~a xs))))

(check-equal? (word-value 1 2 3 4 5) 12345)

(define mapc (make-problem
              (make-variables ['(WA NT SA Q NSW V T) '(r g b)])
              (make-constraints ['((WA NT) (Q NT) (SA NT) (Q NSW) (NSW V) (SA V) (SA Q) (SA NSW) (SA WA)) (negate equal?)])))