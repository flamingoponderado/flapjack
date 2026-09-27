import Flapjack.Pancake.PanToCrep.CompileExact

/-! Exact-carrier regressions for original HOL `comp_func_def` rows in
`scripts/hol-probes/pan_to_crep_comp_func_probe.out`. -/

namespace Flapjack.Test.PanToCrepCompFuncExactParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

private def emptyFunctions : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL) :=
  HolFiniteMapExact.empty

private def emptyEids : HolFiniteMapExact MlS (BitVec 8) :=
  HolFiniteMapExact.empty

private def x : MlS := ofString "x"
private def pair : MlS := ofString "pair"

def skipRow : Bool :=
  match compFuncExactHOLW emptyFunctions emptyEids [] (.skip : ProgHOL 8) with
  | .skip => true
  | _ => false

#guard skipRow

def oneParameterReturnRow : Bool :=
  match compFuncExactHOLW emptyFunctions emptyEids [(x, .one)]
      (.return (.var .local x) : ProgHOL 8) with
  | .return [.var 0] => true
  | _ => false

#guard oneParameterReturnRow

def pairParameterReturnRow : Bool :=
  match compFuncExactHOLW emptyFunctions emptyEids
      [(pair, .comb [.one, .one])]
      (.return (.var .local pair) : ProgHOL 8) with
  | .return [.var 0, .var 1] => true
  | _ => false

#guard pairParameterReturnRow

end Flapjack.Test.PanToCrepCompFuncExactParity
