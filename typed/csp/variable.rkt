#lang typed/racket/base
(require typed/racket/class "helper.rkt")
(provide (all-defined-out))

(define variable%
  (class object% 
    (super-new)

    (: repr (-> String))
    (define (repr) (format "<variable% ~a>" _name))
    
    (: custom-print (Output-Port Integer -> Void))
    (define/public (custom-print out quoting-depth) (print (repr) out))
    
    (: custom-display (Output-Port -> Void))
    (define/public (custom-display out) (displayln (repr) out))

    (: custom-write (Output-Port -> Void))
    (define/public (custom-write out) (write (repr) out))

    (init-field [name : String])

    (field [_name : String name])))

(define Unassigned (new variable% [name "Unassigned"]))