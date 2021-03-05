#lang racket

(require "lang/ast.rkt" "lang/bounds.rkt" "lang/sketch.rkt" "lang/universe.rkt"
         "engine/engine.rkt" "engine/interpretation.rkt"
         "lib/print.rkt" "lib/simplify.rkt" "lib/simplify-solve.rkt"
         "engine/matrix.rkt" "engine/collapse.rkt")

(provide
 ; lang/ast.rkt
 declare-relation
 + - & -> ~ join
 <: :>
 set
 ^ *
 inttag inteq
 none univ iden
 in =
 and or => ! not
 all some no
 one lone
 unary-op?
 (struct-out prefab)
 ; lang/bounds.rkt
 make-bound make-exact-bound make-upper-bound make-product-bound
 (struct-out bounds)
 get-upper-bound bounds-union bounds-variables
 ; lang/sketch.rkt
 expression-sketch
 ; lang/universe.rkt
 universe universe-atoms universe-inverse
 ; engine/engine.rkt
 interpret interpret*
 ; engine/interpretation.rkt
 instantiate-bounds interpretation->relations interpretation-union
 ; lib/print.rkt
 ast->datum ast->alloy
 ; lib/simplify.rkt
 simplify simplify/solve
 ; NHM 02/09/2021
 declare-function
 image image?
 f/all f/some f/max f/domain
 domain
 collapse-universe
 expand-solution
 node/formula?
 node/expr/relation?
 node/function?
 relation-arity
 relation-name
 node-name
 ; TMP:
 matrix-entries
 relation-name
 )
