import Flapjack.Pancake.Proofs.PanToCrep

/-! Exact-carrier regression for `first_compile_to_crep_all_distinct`:
the fixture is paired with direct HOL EVAL row `distinct_function_names` in
`scripts/hol-probes/compile_to_crep_probe.out`. -/

namespace Flapjack.Test.FirstCompileToCrepAllDistinctExact

open Flapjack
open Flapjack.Pancake.PanLang (DeclHOL FunDeclHOL MlS ShapeHOL)
open Flapjack.Basis.Pure.MlString

private def name (text : String) : MlS := ofString text

private def twoDistinctFunctions : List (DeclHOL 8) :=
  [ .function
      { name := name "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := ShapeHOL.one }
  , .function
      { name := name "g", inline := false, exported := false, params := [],
        body := .skip, returnShape := ShapeHOL.one }
  ]

private theorem sourceNamesNodup :
    (Flapjack.Pancake.PanLang.functionsHOL twoDistinctFunctions).map Prod.fst |>.Nodup := by
  decide

theorem exactTheoremApplies :
    (compileToCrepExactHOLW twoDistinctFunctions).map Prod.fst |>.Nodup :=
  firstCompileToCrepAllDistinctExact twoDistinctFunctions sourceNamesNodup

def distinctFunctionNamesOracle : Bool :=
  match compileToCrepExactHOLW twoDistinctFunctions with
  | [(first, [], .skip), (second, [], .skip)] =>
      first == name "f" && second == name "g"
  | _ => false

#guard distinctFunctionNamesOracle
#eval distinctFunctionNamesOracle

end Flapjack.Test.FirstCompileToCrepAllDistinctExact
