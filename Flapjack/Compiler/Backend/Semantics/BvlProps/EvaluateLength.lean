import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.HolRef

/-! Successful-result length properties of BVL evaluation. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Successful evaluation returns as many values as input expressions. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_LENGTH" 225
  (fmap_as_finite_support := [refs])]
theorem evaluateLength {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) :
    match evaluateTuple (expressions, env, state) with
    | (.val values, _) => expressions.length = values.length
    | (.err _, _) => True := by
  cases run : evaluateTuple (expressions, env, state) with
  | mk result next =>
    cases result with
    | err error => trivial
    | val values =>
      have length := evaluate_length expressions env state next values run
      exact length.symm

/-- A successful result has the same length as its expression list. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_IMP_LENGTH"
  (fmap_as_finite_support := [refs])]
theorem evaluateImpLength {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (values : List Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : evaluateTuple (expressions, env, state) = (.val values, next)) :
    expressions.length = values.length := by
  exact (evaluate_length expressions env state next values run).symm

/-- A successful singleton evaluation returns a singleton value list. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_SING"
  (fmap_as_finite_support := [refs])]
theorem evaluateSing {C F : Type} (expression : Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (values : List Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : evaluateTuple ([expression], env, state) = (.val values, next)) :
    ∃ value, values = [value] := by
  exact evaluate_singleton expression env state next values run

end Flapjack.Compiler.Backend.BvlProps
