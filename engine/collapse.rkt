#lang racket

(require "../lang/bounds.rkt" "../lang/universe.rkt"
         "interpretation.rkt" "matrix.rkt" "tuple.rkt"
         "../lang/ast.rkt"
         (only-in "../lang/ast.rkt" relation-arity relation-name declare-relation)
         (only-in rosette <=>)
         (prefix-in $ racket/contract)
         )

;; utilities -------------------------

(define (setof c)
  (lambda (s)
    (if (set? s)
        (for/and ([x (in-set s)]) (c x))
        #f)))

(define (hashof ck cv)
  (lambda (h)
    (if (hash? h)
        (for/and ([(k v) (in-hash h)]) (and (ck k) (cv v)))
        #f)))

(define bnd? (setof list?))
(define interference? (hashof symbol? (setof symbol?)))

; recall: (upper) bounds are sets of tuples.
(define (add-interference b1 b2 i)
  ($-> bnd? bnd? interference?)
  (define (add-pair a1 a2 i)
    (define (add-pair-half a1 a2 i)
      (let* ([i* (i)]
             [s1 (hash-ref i* a1 (list->set '()))]
             [s1* (set-add s1 a2)])
        (i (hash-set i* a1 s1*))))
    
    (add-pair-half a1 a2 i)
    (add-pair-half a2 a1 i))

  (for ([t1 (in-set b1)])
    (for ([t2 (in-set b2)])
      (for ([a1 (in-list t1)] [a2 (in-list t2)])
        (add-pair a1 a2 i)))))

(define (bound-product b1 . bs)
  (define (bound-product-pair b1 b2)
    (define resl (for/list ([t1 (in-set b1)])
                   (for/set ([t2 (in-set b2)])
                     (append t1 t2))))
    (apply set-union resl))

  (for/fold ([acc b1]) ([bi (in-list bs)])
    (bound-product-pair acc bi)))

; bounds are list of tuples this time
(define (bound-join . bs)
  (define (bound-join-pair b1 b2)
    (define b1* (for/set ([t (in-set b1)]) (drop-right t 1)))
    (define b2* (for/set ([t (in-set b2)]) (drop t 1)))
    (bound-product b1* b2*))
  (for/fold ([bres (last bs)]) ([bi (in-list (drop-right bs 1))])
    (bound-join-pair bi bres)))
    

;; universe collapsing --------------

; track symmetry classes in hash map: atom -> interference set (atoms)
    ; bounds: hash map: symbol -> bound

;; Expressions: return updated bounds and indirectly updates interference graph.

(define (collapse node bnds)
  (define bnds* (for/hash ([bnd (in-list (bounds-entries bnds))])
                  (values (bound-relation bnd) (bound-upper bnd))))
  (define interference (make-parameter (hash)))
  (collapse* node bnds* interference)
  (interference))

(define (collapse* node bnds interference)
  (pretty-print (interference))
  (pretty-print node)
  (match node
    [(? node/formula?) (collapse-formula node bnds interference)]
    [(? node/expr?) (collapse-expr node bnds interference)]
    ))
  

(define (collapse-formula formula bnds interference)
  (match formula
    [(node/formula/op args) (collapse-formula-op formula args bnds interference)]
    [(node/formula/quantified quantifier decls f) (collapse-formula-quantified)]
    [(node/formula/multiplicity mult expr) (collapse-expr expr)]
    ))

(define (collapse-formula-op formula args bnds interference)
  (define args* (for/list ([arg (in-list args)]) (collapse* arg bnds interference)))
  (match formula
    [(or (? node/formula/op/&&?)
         (? node/formula/op/||?)
         (? node/formula/op/=>?)
         (? node/formula/op/!?))
     (void)]
    [(or (? node/formula/op/in?)
         (? node/formula/op/=?))
     (add-interference (first args*) (second args*) interference)]
    ))

(define (collapse-formula-quantified quantifier decls f bnds interference)
  (define decl-bnds (for/list ([decl (in-list decls)])
                      (cons (car decl) (collapse* (cdr decl) bnds interference))))
  (define bnds* (apply (curry hash-set* bnds) decl-bnds))
  (collapse-formula f bnds* interference))
  
(define (collapse-expr expr bnds i)
  (match expr
    [(node/expr/op arity children) (collapse-expr-op expr children bnds i)]
    [(node/expr/relation arity name) (collapse-expr-relation expr bnds i)]
    ))

(define (collapse-expr-op expr children bnds i)
  (define children* (for/list ([child (in-list children)]) (collapse* child bnds i)))
  (match expr
    [(or (? node/expr/op/+?)
         (? node/expr/op/-?)
         (? node/expr/op/&?))
     (for ([cp (in-list (cartesian-product children* children*))])
       (add-interference (first cp) (second cp) i))]
    [(or (? node/expr/op/->?)
         (? node/expr/op/~?))
     (void)]
    [(? node/expr/op/join?) (collapse-join children* i)]
    )
  (match expr
    [(? node/expr/op/+?) (apply set-union children*)]
    [(? node/expr/op/-?) (first children*)]
    [(? node/expr/op/&?) (apply set-intersect children*)]
    [(? node/expr/op/->?) (apply bound-product children*)]
    [(? node/expr/op/~?) (for/set ([p (in-set (first children*))])
                          (list (second p) (first p)))]
    [(? node/expr/op/join?) (apply bound-join children*)]
    )
  )

(define (collapse-expr-relation rel bnds i)
  (define bnd (hash-ref bnds rel))
  (add-interference bnd bnd i)
  bnd)

(define (collapse-join bs i)
  (define (collapse-join-pair bl br index i)
    (define (get-ith b index)
      (for/set ([t (in-set b)]) (list (list-ref t index))))
    (define bl-last (get-ith bl (- (length (set-first bl)) 1)))
    (define br-ith (get-ith br index))
    (add-interference bl-last br-ith i))
  (define bn (last bs))
  (define bs* (drop-right bs 1))
  (for ([pos (in-range (length bs*))])
    (collapse-join-pair (list-ref bs* pos) bn pos i)))
             
    
(provide collapse)
