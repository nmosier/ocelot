#lang rosette

(require "../lang/bounds.rkt" "../lang/universe.rkt" "matrix.rkt"
         (only-in "../lang/ast.rkt" relation-arity node/expr/relation? node/function?)
         (prefix-in $ racket))
(provide (all-defined-out))

; An interpretation is a universe and an association list of (relation, matrix)
; pairs
(struct interpretation (universe entries) #:transparent)

; receives an ast/node/relation and an uninterpreted bound

; Create an interpretation of the given bounds
(define (instantiate-bounds bounds)
  (define U (bounds-universe bounds))
  (interpretation
    U
    (for/list ([bnd (in-list (bounds-entries bounds))])
      (define rel (bound-relation bnd))
      (define size (expt (universe-size U) (relation-arity rel)))
      (define-values (type always never)
        (cond [(node/expr/relation? rel) (values boolean? #t #f)]
              [(node/function? rel) (values integer? 1 0)]
              [else (raise-argument-error 'instantiate-bounds "(or/c node/expr/relation? node/function?)" rel)]))
      (define mat
        (cond [(equal? (bound-lower bnd) (bound-upper bnd))
               (define members ($map (curry tuple->idx U) (bound-upper bnd)))
               (matrix (for/list ([i (in-range size)])
                         (if (set-member? members i) always never)))]
              [else
               (define lower ($map (curry tuple->idx U) (bound-lower bnd)))
               (define upper ($map (curry tuple->idx U) (bound-upper bnd)))
               (matrix (for/list ([i (in-range size)])
                           (cond [(set-member? lower i) always]
                                 [(set-member? upper i) (define-symbolic* r type) r]
                                 [else never])))]))
      (cons rel mat))))

(define (interpretation-union . interps)
  (define U (interpretation-universe (car interps)))
  (interpretation U (for*/list ([i (in-list interps)][e (in-list (interpretation-entries i))]) e)))

(define (interpretation->relations interp)
  (match-define (interpretation U entries) interp)
  (for/hash ([pair (in-list entries)])
    (match-define (cons rel mat) pair)
    (define contents (matrix-entries mat))
    (define arity (matrix-arity U contents))
    (values rel (for/list ([(x i) (in-indexed contents)] #:when x)
                  (idx->tuple U arity i)))))