module

public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
public import Flapjack.HolRef

@[expose] public section

/-!
# Successful-result length properties of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:139-155`:
`evaluate_LENGTH`, `evaluate_IMP_LENGTH` and `evaluate_SING_IMP`, the BVI twins
of the `bvlProps` length lemmas.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue)

/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BviSem.BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- Successful evaluation returns as many values as input expressions. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_LENGTH" 139
  (fmap_as_finite_support := [refs])]
theorem evaluateLength {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) :
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
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_IMP_LENGTH"
  (fmap_as_finite_support := [refs])]
theorem evaluateImpLength {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (values : List Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : evaluateTuple (expressions, env, state) = (.val values, next)) :
    expressions.length = values.length := by
  exact (evaluate_length expressions env state next values run).symm

/-- A successful singleton evaluation returns a singleton value list. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_SING_IMP"
  (fmap_as_finite_support := [refs])]
theorem evaluateSingImp {C F : Type} (expression : Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (values : List Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : evaluateTuple ([expression], env, state) = (.val values, next)) :
    ∃ value, values = [value] := by
  exact evaluate_singleton expression env state next values run

end Flapjack.Compiler.Backend.BviProps
