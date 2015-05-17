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

(define-type Scope (Listof Variable))
(define-type Relation (Value * -> Boolean))
(define-type Constraint (Pairof Scope Relation))

(struct problem ([constraints : (Listof Constraint)] [variables : Variables][domains : Domains]) #:transparent)
(define-type Problem problem)

(define-type Solver Procedure)

(define-type Assignment (HashTable Variable Value))
(define-type Solution Assignment) ; that is also consistent (= satisfies constraints) and complete (= uses all variables)
(define-type Solutions (Listof Solution))