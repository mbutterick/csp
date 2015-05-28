#lang racket/base
(require racket/generator racket/list sugar/define rackunit "problem.rkt")
(provide (all-defined-out))


(define/contract (backtracking-solver prob)
  (problem? . -> . generator?)
  (generator ()
             (let loop ([prob (preprocess prob)])
               (cond
                 [(all-vars-assigned? prob)
                  (if (var-assignments-consistent? prob)
                      (yield (problem->solution prob))
                      (error 'backtracking-solver (format "got complete but inconsistent assignment: ~a" (problem->solution prob))))]
                 [else (define unassigned-var (get-unassigned-variable prob))
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