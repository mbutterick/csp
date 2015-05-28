#lang racket/base
(provide (all-defined-out))

(define current-ordering-heuristic (make-parameter 'mrv))
(define current-inference-rule (make-parameter 'forward-check))
(define current-preprocessing (make-parameter 'delete-singletons))
