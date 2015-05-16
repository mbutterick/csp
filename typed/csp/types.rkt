#lang typed/racket/base
(provide (all-defined-out))

(define-type Variable String)
(define-type Variables (Listof Variable))
(define-type Value Any)
(define-type Variable-Domain-Pair (Pairof Variable Domain))
(define-type Domain (Listof Value))
(define-type Domains (Listof Domain))
(define-predicate domains? Domains)
(define-type Variable-Domain-Table (HashTable Variable Domain))

(define-type Constraint Procedure)

(struct problem ([constraints : (Listof Constraint)] [variable-domains : Variable-Domain-Table]) #:transparent)
(define-type Problem problem)

(define-type Solver Procedure)
(define-type Solution (HashTable Variable Value))
(define-type Solutions (Listof Solution))