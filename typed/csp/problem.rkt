#lang typed/racket/base
(require "types.rkt" typed/sugar/define racket/list)
(provide (all-defined-out))

(define/typed (make-vdtable vars domain-or-domains)
  (Variables (U Domain Domains) -> Variable-Domain-Table)
  (define domains-in (if (domains? domain-or-domains) domain-or-domains (list domain-or-domains)))
  (define domains
    (cond
      [(= (length domains-in) (length vars)) domains-in]
      [(< (length domains-in) (length vars)) (append domains-in (make-list (- (length vars) (length domains-in)) (last domains-in)))]
      [else (error 'make-vdtable "got fewer variables than domains")]))
  (make-hash ((inst map Variable-Domain-Pair Variable Domain) cons vars domains)))
