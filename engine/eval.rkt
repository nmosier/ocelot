#lang racket

(require racket/require (matching-identifiers-in #rx"^node/.+$" "../lang/ast.rkt")
         (only-in "../lang/ast.rkt" relation-name relation-arity node?)
         "../lang/bounds.rkt" "../lang/universe.rkt"
         "matrix.rkt" "matrix-ops.rkt" "symmetry.rkt" "interpretation.rkt"
         rosette/lib/match
         (prefix-in $ racket ))

(provide evaluate-node)

(define tuple? (listof any/c))
(define element? (or/c tuple? (cons/c tuple? integer?)))
(define elements? (listof element?))
(define relfun? (or/c node/expr/relation? node/function?))
(define model? (hash/c relfun? elements?))
         
(define/contract (evaluate-node formula model)
  ($-> node? model? elements?)
  (evaluate-rec formula model))

(define/contract (evaluate-rec formula model)
  ($-> node? model? elements?)
  (match formula
    [(node/expr/op arity args)
     (let ([args* (for/list ([arg (in-list args)])
                    (evaluate-rec arg model))])
       (evaluate-expr-op formula args*))]
    [(? node/expr/relation?) (hash-ref model formula)]
    [(? node/function?) (hash-ref model formula)]
    [(node/expr/constant arity type) (evaluate-constant)]
    [(node/expr/comprehension arity decls f)
     (let ([decls* (for/list ([decl (in-list decls)])
                     (cons (car decl) (evaluate-rec (cdr decl) model)))])
       (evaluate-comprehension decls* f model))]
    [(node/formula/op args)
     (let ([args* (for/list ([arg (in-list args)])
                    (evaluate-rec arg model))])
       (evaluate-formula-op formula args*))]
    ))

(define (evaluate-expr-op op args)
  (match op
    [(? node/expr/op/+?) (apply set-union args)]
    [(? node/expr/op/&?) (apply set-intersect args)]
    [(? node/expr/op/-?) (apply set-subtract args)]
    [(? node/expr/op/->?) (apply cartesian-product (map (curry map car) args))]
    [(? node/expr/op/~?) (map (curry map reverse) args)]
    [(? node/expr/op/join?) (evaluate-expr-op-join (drop-right args 1) (last args))]
    [(? node/expr/op/^?) (evaluate-expr-op-^ (first args))]
    [(? node/expr/op/<:?) (filter (lambda (tuple) (set-member? (first args) (first tuple)))
                                  (second args))]
    [(? node/expr/op/:>?) (filter (lambda (tuple) (set-member? (second args) (last tuple)))
                                  (first args))]
    ))

(define (evaluate-expr-op-join args acc)
  (for/fold ([acc* acc]) ([arg (in-list args)])
    (for*/list ([prefix (in-list arg)] [suffix (in-list acc*)]
                                       #:when (equal? (last prefix) (first suffix)))
      (append (drop-right prefix 1) (drop suffix 1)))))

(define (evaluate-expr-op-^ tuples)
  (define (rec tuples) 
    (define new-tuples (for*/list ([t1 (in-list tuples)]
                                   [t2 (in-list tuples)]
                                   #:when (equal? (last t1) (first t2)))
                         (list (first t1) (last t2))))
    (define tuples* (set-union tuples new-tuples))
    (if (equal? tuples tuples*)
        tuples
        (rec tuples*)))
  (rec tuples))
                         
      
(define (evaluate-constant type)
  (case type
    ['none '()]
    [else (error "evaluating " type " not supported")]
    ))

(define (evaluate-comprehension decls f model)
  (if (null? decls)
      (evaluate-rec f model)
      (let* ([decl (car decls)]
             [decls* (cdr decls)]
             [model* (hash-set model (car decl) (evaluate-rec (cdr decl) model))])
        (evaluate-comprehension decls* f model*))))

(define (evaluate-formula-op op args)
  (match op
    [(? node/formula/op/||?) (for/or ([arg (in-list args)]) arg)]
    [(? node/formula/op/&&?) (for/and ([arg (in-list args)]) arg)]
    [(? node/formula/op/=>?) (if (first args) (second args) #t)]
    [(? node/formula/op/in?) (apply subset? args)]
    [(? node/formula/op/=?) (apply equal? args)]
    [(? node/formula/op/!?) (apply not args)]))
     
