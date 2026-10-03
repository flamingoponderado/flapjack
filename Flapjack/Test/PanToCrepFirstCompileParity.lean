import Flapjack.Pancake.Proofs.PanToCrep.FirstCompileProgAllDistinct

/-! Direct HOL oracle rows for `first_compile_prog_all_distinct`
(`scripts/hol-probes/pan_to_crep_first_compile_oracle_probe.out`): the source
and compiled name lists of a distinct-name program are both distinct
(`distinct_names=(T,T)`), and those of a duplicate-name program both are not
(`duplicate_names=(F,F)`), over the exact `functionsHOL` and
`compileProgDeclsHOLW`. -/

namespace Flapjack.Test.PanToCrepFirstCompileParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

private def mkFn (name : String) (inl exp : Bool) (body : ProgHOL 8) : DeclHOL 8 :=
  .function (FunDeclHOL.mk (ofString name) inl exp [] body .one)

private def distinctNames : List (DeclHOL 8) :=
  [mkFn "leaf" true false (.return (.const 7)),
   mkFn "mid" true false (.call none (ofString "leaf") []),
   mkFn "main" false true (.call none (ofString "mid") [])]

private def duplicateNames : List (DeclHOL 8) :=
  [mkFn "id" true false (.return (.const 7)),
   mkFn "id" true false (.return (.const 9)),
   mkFn "main" false true (.call none (ofString "id") [])]

private def namesDistinct (p : List (DeclHOL 8)) : Bool × Bool :=
  (decide ((functionsHOL p).map Prod.fst).Nodup,
   decide ((compileProgDeclsHOLW p).map Prod.fst).Nodup)

#guard namesDistinct distinctNames = (true, true)
#guard namesDistinct duplicateNames = (false, false)

end Flapjack.Test.PanToCrepFirstCompileParity
