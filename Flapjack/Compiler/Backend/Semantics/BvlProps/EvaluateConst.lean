module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
public import Flapjack.Compiler.Backend.Bvl.Boolean
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift
public import Flapjack.HolRef

@[expose] public section

/-!
# Constant and Boolean evaluation in HOL `bvlProps`

Counterpart of `cakeml/compiler/backend/semantics/bvlPropsScript.sml:403-415`:
`evaluate_MAP_Const` and `evaluate_Bool`.
-/

namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

namespace EvaluateConstCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvaluateConstCarrier

/-- A single constant integer operation evaluates to its constant. -/
private theorem evaluateIntConst {C F : Type} (i : Int) (env : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    evaluateTuple ([.op (.intOp (.const i)) []], env, s) = (.val [.number i], s) := by
  simp [evaluateTuple, evaluate, doApp, applyNumeric, doIntApp, fixClock]

/-- Evaluating a list of constant integer operations yields those constants. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_MAP_Const"
  (fmap_as_finite_support := [refs])]
theorem evaluateMapConst {α C F : Type} (exps : List α) (i : Int)
    (env : List BvlSem.Value) (t1 : Flapjack.Compiler.Backend.BvlSem.State C F) :
    evaluateTuple (exps.map (fun _ => .op (.intOp (.const i)) []), env, t1) =
      (.val (exps.map (fun _ => .number i)), t1) := by
  induction exps with
  | nil => simp [evaluateTuple, evaluate]
  | cons x xs ih =>
    conv_lhs => rw [List.map_cons, evaluateCons]
    simp only [evaluateIntConst, ih]
    simp [Flapjack.holHd]

/-- Evaluating the Boolean constructor yields the Boolean value. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_Bool"
  (fmap_as_finite_support := [refs])]
theorem evaluateBool {C F : Type} (b : Bool) (env : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    evaluateTuple ([Bvl.boolExp b], env, s) = (.val [boolValue b], s) := by
  simp [evaluateTuple, evaluate, Bvl.boolExp, boolValue, doApp, applyBlock, fixClock]

end Flapjack.Compiler.Backend.BvlProps
