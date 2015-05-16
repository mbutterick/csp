#lang typed/racket/base
(require typed/sugar/define "types.rkt" racket/list)
(provide (all-defined-out))

(define/typed (get-args p)
  (Problem -> (Values Variable-Domain-Table Constraints (HashTable Variable Constraints)))
  (define variable-domains (hash-copy (problem-variable-domains p)))
  
  (define constraints
    (let ([all-variables (hash-keys variable-domains)])
      (for/list ([(constraint variables) (in-parallel (map first (problem-constraints p)) (map second (problem-constraints p)))])
        (list constraint (if (null? variables) all-variables variables)))))
  
  (define vconstraints 
    (hash-copy ; converts for/hash to mutable hash
     (for/hash ([variable (in-hash-keys variable-domains)])
       (values variable null))))
  
  (for* ([(constraint variables) (in-parallel (map first constraints) (map second constraints))]
         [variable (in-list variables)])
    (hash-update! vconstraints variable (λ(val) (cons (list constraint variables) val))))
  
  (for ([(constraint variables) (in-parallel (map first constraints) (map second constraints))])
    (send constraint preprocess variables variable-domains constraints vconstraints))
  
  (if (for/or ([domain (in-hash-values variable-domains)])
        (send domain reset-state)
        (null? (domain)))
      (values null null null)
      (values variable-domains constraints vconstraints)))

(define/typed (make-backtracking-solver)
  (-> (Problem -> Solutions))
  (define/typed solve
    (Problem -> Solutions)
    (λ(p) (list '#hash(("foo" . bar)))))
  solve)
