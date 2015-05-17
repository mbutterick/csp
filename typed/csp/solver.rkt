#lang typed/racket/base
(require typed/sugar/define "types.rkt" racket/list)
(provide (all-defined-out))

(define/typed (make-backtracking-solver)
  (-> (Problem -> Solutions))
  (define/typed solve
    (Problem -> Solutions)
    (λ(p) (list '#hash(("foo" . bar)))))
  solve)
