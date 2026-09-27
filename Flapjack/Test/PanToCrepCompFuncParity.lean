import Flapjack.Pancake.PanToCrep.CompileExact

/-!
# `pan_to_crep$comp_func` exact-carrier parity

Direct original-HOL oracle rows for the exact tagged definition
`Flapjack.compFuncExactHOL` (the Lean counterpart of HOL `pan_to_crep$comp_func`,
`cakeml/pancake/pan_to_crepScript.sml:337-343`). The oracle values are those
recorded by `scripts/hol-probes/comp_func_probe.out`, produced by running HOL
`pan_to_crep$comp_func` on the concrete inputs in
`scripts/hol-probes/comp_func_probeScript.sml`.

Each row exercises the parameter-driven context construction: `make_vmap` over
the parameter list, the `Comb` slot bound `size_of_shape (Comb (MAP SND params)) - 1`,
and the `compile` dispatch for the body. The Lean guards call `compFuncExactHOL`
over the exact `MlS`/`ShapeHOL`/`ProgHOL`/`CrepProgHOL` carriers and pattern
match the resulting `CrepProgHOL`.
-/

namespace Flapjack.Test.PanToCrepCompFuncParity

open Flapjack
open Flapjack.Pancake.PanLang

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

/-- Oracle `skip`: the empty parameter list and `Skip` body compile to `Skip`. -/
def compFuncSkipGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      ([] : List (MlS × ShapeHOL)) (ProgHOL.skip (width := 8)) with
  | .skip => true
  | _ => false

/-- Oracle `tick`: `Tick` is preserved. -/
def compFuncTickGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      ([] : List (MlS × ShapeHOL)) (ProgHOL.tick (width := 8)) with
  | .tick => true
  | _ => false

/-- Oracle `local_assign_from_param`: `make_vmap` gives `x` slot 0 and `y` slot
    1, so `y := x` compiles to `Seq (Assign 1 (Var 0)) Skip`. -/
def compFuncLocalAssignGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      [(ml "x", .one), (ml "y", .one)]
      (ProgHOL.assign .local (ml "y") (ExpHOL.var .local (ml "x"))) with
  | .seq (.assign 1 (.var 0)) .skip => true
  | _ => false

/-- Oracle `global_assign_from_param`: a global destination is not in the
    parameter-built `vars` map, so the assignment falls back to `Skip`. -/
def compFuncGlobalAssignGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      [(ml "x", .one)]
      (ProgHOL.assign .global (ml "g") (ExpHOL.var .local (ml "x"))) with
  | .skip => true
  | _ => false

/-- Oracle `primitive_params`: a primitive destination not present in the
    parameter-built `vars` map falls back to `Skip`. -/
def compFuncPrimitiveGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      [(ml "x", .one), (ml "y", .one)]
      (ProgHOL.primitive (ml "r") PrimOp.addCarry
        [ExpHOL.var .local (ml "x"), ExpHOL.var .local (ml "y")]) with
  | .skip => true
  | _ => false

/-- Oracle `seq_tick_return`: sequential composition and a constant return. -/
def compFuncSeqTickReturnGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      [(ml "x", .one)]
      (ProgHOL.seq (ProgHOL.tick (width := 8))
        (ProgHOL.return (ExpHOL.const (BitVec.ofNat 8 5)))) with
  | .seq .tick (.return [.const 5]) => true
  | _ => false

/-- Oracle `combined_param_shape`: a single `Comb [One;One]` parameter gives
    `vmax = 1`, and a two-word `RStruct` return needs no temporaries. -/
def compFuncCombinedParamGuard : Bool :=
  match compFuncExactHOL
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS
        (List (MlS × ShapeHOL) × ShapeHOL))
      (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec 8))
      [(ml "pair", .comb [.one, .one])]
      (ProgHOL.return
        (ExpHOL.rstruct
          [ExpHOL.const (BitVec.ofNat 8 1), ExpHOL.const (BitVec.ofNat 8 2)])) with
  | .return [.const 1, .const 2] => true
  | _ => false

def compFuncParityGuard : Bool :=
  compFuncSkipGuard && compFuncTickGuard && compFuncLocalAssignGuard &&
    compFuncGlobalAssignGuard && compFuncPrimitiveGuard &&
    compFuncSeqTickReturnGuard && compFuncCombinedParamGuard

#guard compFuncSkipGuard
#guard compFuncTickGuard
#guard compFuncLocalAssignGuard
#guard compFuncGlobalAssignGuard
#guard compFuncPrimitiveGuard
#guard compFuncSeqTickReturnGuard
#guard compFuncCombinedParamGuard
#guard compFuncParityGuard

def runChecks : IO Bool := do
  if compFuncParityGuard then
    IO.println "PASS exact pan_to_crep comp_func matches HOL oracle rows"
    pure true
  else
    IO.println "FAIL exact pan_to_crep comp_func matches HOL oracle rows"
    pure false

end Flapjack.Test.PanToCrepCompFuncParity
