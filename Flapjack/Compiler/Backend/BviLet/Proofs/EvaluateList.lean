module

public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList

@[expose] public section

/-! Evaluation-list facts for the BVI let correctness proof. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

namespace EvaluateListCarrier
/-- The BVI reference state and its finite-support representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end EvaluateListCarrier

/-- A successful evaluation ending in one expression decomposes into the
prefix result and the final singleton result. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "evaluate_SNOC_Rval"
  (fmap_as_finite_support := [refs])]
theorem evaluateSnocRval {C F : Type} (x : Bvi.Exp) (y : List Bvi.Exp) (env : List Value)
    (s r : BviState C F) (a : List Value)
    (run : evaluateTuple (y ++ [x], env, s) = (.val a, r)) :
    ∃ a1 a2 r1, a = a2 ++ [a1] ∧ y.length = a2.length ∧
      evaluateTuple (y, env, s) = (.val a2, r1) ∧
      evaluateTuple ([x], env, r1) = (.val [a1], r) := by
  have split := evaluateSnoc y env s x
  rw [run] at split
  cases first : evaluateTuple (y, env, s) with
  | mk firstResult middle =>
    cases firstResult with
    | err err => simp [first] at split
    | val values =>
      cases second : evaluateTuple ([x], env, middle) with
      | mk secondResult final =>
        cases secondResult with
        | err err => simp [first, second] at split
        | val tail =>
          simp [first, second] at split
          obtain ⟨rfl, rfl⟩ := split
          obtain ⟨value, rfl⟩ := evaluateSing x env middle r tail second
          exact ⟨value, values, middle, rfl, evaluateImpLength y env s middle values first, rfl, second⟩

end Flapjack.Compiler.Backend.BviLet.Proofs
