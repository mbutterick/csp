#lang racket
(require (for-syntax racket/syntax) sugar/debug)

(require (prefix-in 0: csp0/test-problems) csp/test-problems csp/solver csp/problem csp/world)

(define-syntax (race stx)
  (syntax-case stx ()
    [(_ prob)
     #'(race prob 1)]
    [(_ prob laps)
     (with-syntax ([0:prob (format-id stx "0:~a" #'prob)])
       #'(for-each displayln
                   (map ~v (list
                            (time-repeat laps (send 0:prob get-solution))
                            
                            
                            (parameterize ([current-ordering-heuristic #f]
                                           [current-inference-rule #f]
                                           [current-preprocessing #t])
                              (time-repeat laps (solve prob)))))))]))
;(race quarter-problem 1)
;(race nickel-problem 1)
(race two-four-problem 1)
;(race xsum-problem)