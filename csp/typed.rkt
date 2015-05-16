#lang typed/racket/base

(require/typed
  "problem.rkt"
  [problem% (Class [reset (->m void?)]
           [set-solver (solver%? . ->m . void?)] 
           [get-solver (->m solver%?)]
           [add-variable (any/c (or/c list? domain%?) . ->m . void?)]
           [add-variables ((listof any/c) (or/c list? domain%?) . ->m . void?)]
           [add-constraint (((or/c constraint%? procedure?)) ((listof any/c)) . ->*m . void?)]
           [get-solution (->m any/c)]
           [get-solutions (->m list?)])])
#;(provide (all-from-out
  "problem.rkt"
  "constraint.rkt"
  "solver.rkt"
  "helper.rkt"))

