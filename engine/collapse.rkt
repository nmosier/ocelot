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
  (match node
    [(? node/formula?) (collapse-formula node bnds interference)]
    [(? node/expr?) (collapse-expr node bnds interference)]
    ))
  

(define (collapse-formula formula bnds interference)
  (match formula
    [(node/formula/op args) (collapse-formula-op formula args bnds interference)]
    [(node/formula/quantified quantifier decls f)
     (collapse-formula-quantified quantifier decls f bnds interference)]
    [(node/formula/multiplicity mult expr) (collapse-expr expr bnds interference)]
    [(node/function/quantified quantifier decls formula)
     (collapse-function-quantified quantifier decls formula bnds interference)]
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
  (define decl-bnds (for/fold ([acc (list)]) ([decl (in-list decls)])
                      (append acc (list (car decl)
                                        (collapse* (cdr decl) bnds interference)))))
  (define bnds* (apply (curry hash-set* bnds) decl-bnds))
  (collapse-formula f bnds* interference))
  
(define (collapse-expr expr bnds i)
  (match expr
    [(node/expr/op arity children) (collapse-expr-op expr children bnds i)]
    [(node/expr/relation arity name) (collapse-expr-relation expr bnds i)]
    [(node/expr/f/dom arity func) (collapse* func bnds i)]
    [(? node/fexpr?) (collapse-fexpr expr bnds i)]
    [(node/expr/constant arity type) (collapse-expr-constant type i)]
    ))

(define (collapse-expr-constant type i)
  (match type
    ['none (list->set '())]
    ; 'iden: (disabled)
    ; 'univ: (disabled)
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


(define (collapse-fexpr fexpr bnds i)
  (match fexpr
    [(node/function arity name) (collapse-fexpr-function fexpr bnds i)]
    [(node/fexpr/image arity func expr) (collapse-fexpr-image func expr bnds i)]
    ))


(define (collapse-fexpr-function func bnds i)
  (define bnd (hash-ref bnds func))
  (add-interference bnd bnd i)
  bnd)

(define (collapse-function-quantified quantifier decls formula bnds i)
  (for ([decl (in-list decls)])
    (collapse* (cdr decl) bnds i)))

(define (collapse-fexpr-image func expr bnds i)
  (define func-bnds (collapse* func bnds i))
  (define expr-bnds (collapse* expr bnds i))
  (add-interference func-bnds expr-bnds i)
  func-bnds)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; COLORING ;;;;;;;;;;;;;;;;;;;;;

(define graph? (hashof symbol? (setof symbol?)))

(define/contract (check-graph g)
  ($-> graph? boolean?)
  (for/and ([(src src-adj) (in-hash g)])
    (for/and ([dst (in-set src-adj)])
      (define dst-adj (hash-ref g dst))
      (set-member? dst-adj src))))

(define/contract (remove-node g rm-node)
  ($-> graph? symbol? graph?)
  (define g* (hash-remove g rm-node))
  (for/hash ([(node adj) (in-hash g*)])
    (values node (set-remove adj rm-node))))

(define/contract (color g)
  ($-> graph? (hashof symbol? integer?))
  (unless (check-graph g) (raise-argument-error color "check-graph" g))
  ; remove self-edges
  (define g* (for/hash ([(node adj) (in-hash g)])
               (values node (set-remove adj node))))
  (define (color-rec g)
    ; find min degree
    (if (hash-empty? g)
        (hash)
        (let*-values
            ([(_ node) (for/fold ([min-deg (hash-count g)] [min-node (void)])
                                 ([(node adj) (in-hash g)])
                         (define deg (set-count adj))
                         (if (<= deg min-deg)
                             (values deg node)
                             (values min-deg min-node)))]
             [(coloring) (color-rec (remove-node g node))]
             [(used) (for/set ([adj-node (in-set (hash-ref g node))])
                              (hash-ref coloring adj-node))]
             ; find minimum nonnegative integer not in `used`
             [(color) (for/first ([color (in-range (+ 1 (set-count used)))]
                                         #:unless (set-member? used color))
                      color)]
             )
          (hash-set coloring node color))))
  (color-rec g*))
               
(provide collapse color)
