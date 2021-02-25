#lang racket

(require "../lang/bounds.rkt" "../lang/universe.rkt"
         "interpretation.rkt" "matrix.rkt" "tuple.rkt"
         "../lang/ast.rkt"
         (only-in "../lang/ast.rkt" relation-arity relation-name declare-relation)
         (only-in rosette <=>)
         (prefix-in $ racket/contract)
         )

;; utilities -------------------------

(define bnd? (listof (set/c symbol?)))
(define bnds? (hash/c (or/c node/expr/relation? node/function?) bnd?))
(define graph? (hash/c symbol? (set/c symbol?)))
(define interference? graph?)

(define/contract (get-ith b i)
  ($-> bnd? natural? bnd?)
  (list (list-ref b i)))

(define/contract (add-edge g n1 n2)
  ($-> graph? symbol? symbol? graph?)
  (define (half g n1 n2) (hash-update g n1 (lambda (s) (set-add s n2)) (list->set '())))
  (half (half g n1 n2) n2 n1))

; recall: (upper) bounds are sets of tuples.
(define/contract (add-interference b1 b2 i)
  ($-> bnd? bnd? (parameter/c interference?) void?)
  (define/contract (add-interference-set s1 s2 i)
    ($-> (set/c symbol?) (set/c symbol?) interference? interference?)
    (for*/fold ([i* i]) ([a1 (in-set s1)] [a2 (in-set s2)]) (add-edge i* a1 a2)))
  (define i* (for/fold ([i* (i)]) ([s1 (in-list b1)] [s2 (in-list b2)])
               (add-interference-set s1 s2 i*)))
  (i i*))

(define/contract (bound-product . bs)
  ($-> bnd? ... bnd?)
  (apply append bs))

; bounds are list of tuples this time
(define/contract (bound-join . bs)
  ($-> bnd? ... bnd?)
  (for/fold ([acc (last bs)]) ([bi (in-list (drop-right bs 1))])
    (append (drop-right bi 1) (drop acc 1))))

;; universe collapsing --------------

; track symmetry classes in hash map: atom -> interference set (atoms)
    ; bounds: hash map: symbol -> bound

;; Expressions: return updated bounds and indirectly updates interference graph.

(define/contract (collapse node bnds)
  ($-> (or/c node/expr? node/formula?) bounds? interference?)
  (define bnds* (for/hash ([bnd (in-list (bounds-entries bnds))])
                  (let* ([rel (bound-relation bnd)]
                         [bndl (bound-upper bnd)]
                         [arity (relation-arity rel)])
                    (values rel
                            (for/list ([i (in-range arity)])
                              (for/set ([t (in-list bndl)])
                                (list-ref t i)))))))
  (define interference (make-parameter (hash)))
  (collapse* node bnds* interference)
  (interference))

(define (check i)
  (define i* (i))
  (define stages (list->set '(FetchStage ExecuteStage WritebackStage MemoryHierarchy)))
  (define cur (hash-ref i* 'FetchStage (list->set '())))
  (subset? cur stages))

(define/contract (collapse* node bnds interference)
  ($-> (or/c node/formula? node/expr?) bnds? parameter? (or/c bnd? void?))
  (unless (check interference) (raise "damn"))
  (define bnd (match node
                [(? node/formula?) (collapse-formula node bnds interference)]
                [(? node/expr?) (collapse-expr node bnds interference)]
                ))
  (unless (check interference) (begin (pretty-print node)
                                      (raise "stopping")))
  bnd)
  

(define/contract (collapse-formula formula bnds interference)
  ($-> node/formula? bnds? (parameter/c interference?) void?)
  (match formula
    [(node/formula/op args) (collapse-formula-op formula args bnds interference)]
    [(node/formula/quantified quantifier decls f)
     (collapse-formula-quantified quantifier decls f bnds interference)]
    [(node/formula/multiplicity mult expr) (collapse-expr expr bnds interference)]
    [(node/function/quantified quantifier decls formula)
     (collapse-function-quantified quantifier decls formula bnds interference)]
    )
  (void))

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
     (add-interference (first args*) (second args*) interference)
     (pretty-print args*)]
    ))

(define (collapse-formula-quantified quantifier decls f bnds interference)
  (define decl-bnds (for/fold ([acc (list)]) ([decl (in-list decls)])
                      (append acc (list (car decl)
                                        (collapse* (cdr decl) bnds interference)))))
  (define bnds* (apply (curry hash-set* bnds) decl-bnds))
  (collapse-formula f bnds* interference))
  
(define/contract (collapse-expr expr bnds i)
  ($-> node/expr? bnds? (parameter/c interference?) bnd?)
  (match expr
    [(node/expr/op arity children) (collapse-expr-op expr children bnds i)]
    [(node/expr/relation arity name) (collapse-expr-relation expr bnds i)]
    [(node/expr/f/dom arity func) (collapse* func bnds i)]
    [(? node/fexpr?) (collapse-fexpr expr bnds i)]
    [(node/expr/constant arity type) (collapse-expr-constant type i)]
    [(node/expr/comprehension arity decls formula)
     (collapse-expr-comprehension decls formula bnds i)]
    [(node/expr/domain arity expr) (collapse-expr-domain expr bnds i)]
    ))

(define (collapse-expr-comprehension decls formula bnds i)
  ; TODO: This is shared -- create shared function
  (define decl-kv (for/fold ([acc (list)]) ([decl (in-list decls)])
                      (append acc (list (car decl)
                                        (collapse* (cdr decl) bnds i)))))
  (define bnds* (apply (curry hash-set* bnds) decl-kv))
  (collapse-formula formula bnds* i)
  (define decl-v (for/list ([n (in-range (length decl-kv))] #:when (odd? n))
                   (list-ref decl-kv n)))
  (apply bound-product decl-v)
  )

(define (collapse-expr-domain expr bnds i)
  (define expr-bnds (collapse* expr bnds i))
  (define domain-bnds (get-ith expr-bnds 0))
  (add-interference domain-bnds domain-bnds i) ; NOTE: this is unnecessary
  domain-bnds)
  

(define (collapse-expr-constant type i)
  (match type
    ['none (list (list->set '()))]
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
    [(or (? node/expr/op/^?)
         (? node/expr/op/*?))
     (let ([child (first children*)])
       (add-interference (get-ith child 0) (get-ith child 1) i))]
    [(? node/expr/op/:>?)
     (let* ([a (first children*)]
            [b (second children*)]
            [arity (length a)]
            [index (- arity 1)])
       (add-interference b (get-ith a index) i))]
    [(? node/expr/op/<:?)
     (let* ([a (first children*)]
            [b (second children*)])
       (add-interference a (get-ith b 0) i))]
    )
  (match expr
    [(? node/expr/op/+?) (for/list ([index (in-range (node/expr-arity expr))])
                           (for/fold ([acc (list->set '())]) ([bnd (in-list children*)])
                             (set-union acc (list-ref bnd index))))]
    [(? node/expr/op/-?) (first children*)]
    [(? node/expr/op/&?) (for/list ([index (in-range (node/expr-arity expr))])
                           (for/fold ([acc (list->set '())]) ([bnd (in-list children*)])
                             (set-intersect acc (list-ref bnd index))))]
    [(? node/expr/op/->?) (apply bound-product children*)]
    [(? node/expr/op/~?) (reverse (first children*))]
    [(? node/expr/op/join?) (apply bound-join children*)]
    [(or (? node/expr/op/^?)
         (? node/expr/op/*?))
     (let* ([child (first children*)]
            [union (set-union (get-ith child 0) (get-ith child 1))])
       (bound-product union union))]
    [(? node/expr/op/:>?)
     (let ([a (first children*)]
           [b (second children*)])
       (list-update a 0 (lambda (s) (set-subtract s (first b)))))]
    [(? node/expr/op/<:?)
     (let ([a (first children*)]
           [b (second children*)])
       (list-update b 0 (lambda (s) (set-subtract s (first a)))))]
    )
  )

(define (collapse-expr-relation rel bnds i)
  (define bnd (hash-ref bnds rel))
  (add-interference bnd bnd i)
  bnd)

(define (collapse-join bs i)
  (define (collapse-join-pair bl br index i)
    (define bl-last (get-ith bl (- (length bl) 1)))
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
  ($-> graph? (hash/c symbol? integer?))
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
