#lang racket/base
(require (for-syntax racket/base racket/syntax racket/list racket/function))
(require sugar/define sugar/list sugar/debug racket/list racket/function "world.rkt")
(provide (all-defined-out))

(define variable? (λ(x) (or (string? x) (number? x) (symbol? x))))
(define value? (λ(x) #t))
(define (listof? proc) (λ(x) (and (list? x) (andmap proc x))))
(define (pairof? proc1 proc2) (λ(x) (and (pair? x) (proc1 (car x)) (proc2 (cdr x)))))
(define (hashof? keyproc valproc) (λ(x) (and (hash? x) (andmap keyproc (hash-keys x)) (andmap valproc (hash-values x)))))
(define domain? (listof? value?))


(define scope? (listof? variable?))
(define relation? procedure?)
(struct constraint (scope relation-code relation) #:transparent #:omit-define-syntaxes
  #:constructor-name new-constraint)
(define-syntax-rule (constraint scope-vars relation)
  (new-constraint scope-vars 'relation relation))


(define vardom? (hashof? variable? domain?))
(define vardom-ref hash-ref)
(define vardom-domains hash-values)
(define vardom-variables hash-keys)
(define vardom-set hash-set)
(define vardom-set! hash-set!)

(struct problem (vardom constraints) #:transparent)

(define natural? exact-nonnegative-integer?)
(define solution-ref hash-ref)
(define solution? (hashof? variable? value?))


;; which variable should be assigned next?
(define/contract (get-unassigned-variable prob)
  (problem? . -> . (or/c #f variable?))
  (define ordered-unassigned-vars
    (let ([unassigned-vars (for/list ([(var dom) (in-hash (problem-vardom prob))]
                                      #:when (> (length dom) 1)) ; if length = 1, it's assigned
                             var)])
      (if (empty? unassigned-vars)
          empty
          (case (current-ordering-heuristic)
            [(degree) ; degree heuristic: take var involved in most constraints
             (define var-degree-table (frequency-hash (append-map constraint-scope (problem-constraints prob))))
             (list (argmax (λ(uv) (curryr hash-ref var-degree-table uv 0)) unassigned-vars))]
            [(mrv) ; MRV heuristic: take var with smallest domain
             (list (argmin (λ(uv) (length (vardom-ref (problem-vardom prob) uv))) unassigned-vars))]
            [else ; no ordering
             unassigned-vars]))))
  (and (not (empty? ordered-unassigned-vars)) (car ordered-unassigned-vars)))


;; in what order should possible values be tried?
(define/contract (get-sorted-domain-values prob unassigned-var)
  (problem? variable? . -> . (listof value?))
  (define unassigned-var-domain (vardom-ref (problem-vardom prob) unassigned-var))
  unassigned-var-domain) ; for now, no reordering


(define/contract (get-assigned-variables prob)
  (problem? . -> . (listof variable?))
  (for/list ([(var dom) (in-hash (problem-vardom prob))]
             #:when (= 1 (length dom)))
    var))


(define/contract (all-vars-assigned? prob)
  (problem? . -> . boolean?)
  ;; all vars are assigned, i.e., have only one value in domain
  (= (length (vardom-variables (problem-vardom prob))) (length (get-assigned-variables prob))))

(define/contract (any-arity-constraint? c)
  (constraint? . -> . boolean?)
  (empty? (constraint-scope c)))

;; would the proposed new value break any constraints?
(define/contract (value-consistent? prob new-var proposed-val)
  (problem? variable? value? . -> . boolean?)
  (define assigned-vars (cons new-var (get-assigned-variables prob)))
  ;; take the current vardom and udpate with the new assignment
  (define updated-vardom (vardom-set (problem-vardom prob) new-var (list proposed-val)))
  ;; select every constraint whose scope includes new-var plus some subset of assigned vars
  ;; not actually going to use `subset?` because it's slow, `member` is fast
  ;; keep testing constraints till one fails
  (for/and ([c (in-list (problem-constraints prob))] 
            #:when
            (or (any-arity-constraint? c) ; any args
                (and (member new-var (constraint-scope c)) ; new-var must be in scope
                     ; only care about scopes using assigneed vars 
                     (andmap (curryr member assigned-vars) (constraint-scope c)))))
    ;; since we are testing only assigned vars, each domain will have only one value
    (apply-constraint-to-vardom c updated-vardom assigned-vars)))

(define/contract (apply-constraint-to-vardom c vd [vars #f])
  ((constraint? vardom?) ((listof? variable?)) . ->* . boolean?)
  (define vars-to-test (or vars (vardom-variables vd)))
  (define scope (if (any-arity-constraint? c)
                    vars-to-test
                    (constraint-scope c)))
  (define vals-to-test (map (compose1 first (curry vardom-ref vd)) scope))
  (apply (constraint-relation c) vals-to-test))

(define/contract (var-assignments-consistent? prob)
  (problem? . -> . boolean?)
  ;; values do not violate any constraints
  (for/and ([c (in-list (problem-constraints prob))])
    (apply-constraint-to-vardom c (problem-vardom prob))))


(define/contract (problem->solution prob)
  (problem? . -> . solution?)
  (for/hash ([(var vals) (in-hash (problem-vardom prob))])
    (values var (car vals))))


(define/contract (assign-and-infer prob var val)
  (problem? variable? value? . -> . (or/c #f problem?))
  (struct exn:empty-domain exn:fail ())
  (define updated-problem (problem (vardom-set (problem-vardom prob) var (list val)) (problem-constraints prob)))
  (case (current-inference-rule)
    [(forward-check) ; delete impossible values from each remaining domain
     (define pruned-vardom
       (with-handlers ([exn:empty-domain? (λ(exn) #f)]) ; an empty domain is an instant fail
         (for/fold ([acc-vardom (problem-vardom updated-problem)])
                   ([var (in-hash-keys (problem-vardom updated-problem))])
           (define current-domain (vardom-ref acc-vardom var))
           (define pruned-domain
             (cond
               [(= 1 (length current-domain)) current-domain] ; it's assigned
               [else
                (define filtered-domain (filter (λ(val) (value-consistent? (problem acc-vardom (problem-constraints updated-problem)) var val)) current-domain))
                (if (empty? filtered-domain)
                    (raise (exn:empty-domain "irrelevant error msg" (current-continuation-marks)))
                    filtered-domain)]))
           (vardom-set acc-vardom var pruned-domain))))
     (and pruned-vardom (problem pruned-vardom (problem-constraints updated-problem)))]
    [else updated-problem]))

(define/contract (preprocess prob)
  (problem? . -> . problem?)
  (case (current-preprocessing)
    [(delete-singletons)
     ;; two steps:
     ;; filter constraints with only one var in scope.
     ;; apply those constraint to the domains.
     (define constraint-has-one-var? (λ(c) (= 1 (length (constraint-scope c)))))
     (define-values (unary-constraints other-constraints) (partition constraint-has-one-var? (problem-constraints prob)))
     (define preprocessed-vardom
       (for/fold ([updated-vardom (problem-vardom prob)])
                 ([uc (in-list unary-constraints)])
         (define var (car (constraint-scope uc)))
         (define pruned-domain (filter (constraint-relation uc) (vardom-ref updated-vardom var)))
         (vardom-set updated-vardom var pruned-domain)))
     (problem preprocessed-vardom other-constraints)]
    [else prob]))


(define/contract (make-problem vardom-or-vardom-pairs [constraint-pairs empty])
  (((or/c vardom? (listof (or/c variable? domain?)))) ((listof constraint?)) . ->* . problem?)
  (define vardom-table (if (hash? vardom-or-vardom-pairs)
                           vardom-or-vardom-pairs
                           (apply hash vardom-or-vardom-pairs)))
  (problem vardom-table constraint-pairs))



(define-syntax (make-variables stx)
  (syntax-case stx ()
    [(_ vdlists ...)
     (let ([my-vdlists (syntax->datum #'(vdlists ...))])
       (define alternating-vars-and-domains
         (append*
          (for/list ([vdlist (in-list my-vdlists)])
            (let* ([var-or-vars (cadar vdlist)]
                   [domain (cadr vdlist)]
                   [vars (if (list? var-or-vars) var-or-vars (list var-or-vars))])
              (append-map (λ(var) (list `(quote ,var) domain)) vars)))))
       (datum->syntax stx `(list ,@alternating-vars-and-domains)))]))

(define-syntax (make-constraints stx)
  (syntax-case stx ()
    [(_ sflists ...) ; sflist = scope-function list
     (let ([my-sflists (syntax->datum #'(sflists ...))])
       (define constraints
         (append*
          (for/list ([sflist (in-list my-sflists)])
            (let* ([scope-or-scopes (cadar sflist)]
                   [function (cadr sflist)]
                   [scopes (if (andmap list? scope-or-scopes) scope-or-scopes (list scope-or-scopes))])
              (map (λ(scope) `(constraint (quote ,scope) ,function)) scopes)))))
       (datum->syntax stx `(list ,@constraints)))]))

(define all-different? (λ xs (members-unique? xs)))
