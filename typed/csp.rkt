#lang racket/base

(define-syntax-rule (r/p name)
  (begin
    (require name)
    (provide (all-from-out name))))

#|
(r/p "csp/constraint.rkt")
(r/p "csp/domain.rkt")
(r/p "csp/helper.rkt")
(r/p "csp/problem.rkt")
(r/p "csp/solver.rkt")
|#