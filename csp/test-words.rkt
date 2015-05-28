#lang racket/base
(require racket/file racket/function)
(require "problem.rkt" "solver.rkt" "world.rkt")

(define (word-filter x)
  (and (= 5 (string-length x)) (equal? (string-downcase x) x)))

(define words (filter word-filter (file->lines "/usr/share/dict/words")))

(define wp (make-problem
            (make-variables ['(h1 h2 h3 h4) '(hello world pecan)])
            (make-constraints)))

(time (solve wp))
