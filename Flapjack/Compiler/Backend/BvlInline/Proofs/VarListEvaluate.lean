import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpProduction
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Evaluation of consecutive variable expressions for BVL let optimization. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace VarListCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end VarListCarrier

/-- Consecutive variables read the segment following the before. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "var_list_IMP_evaluate" 1449
  (fmap_as_finite_support := [refs])]
theorem varListEvaluate {C F : Type} (values before : List BvlSem.Value)
    (expressions xs : List Bvl.Exp) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (env : List BvlSem.Value)
    (h : varListHOL before.length expressions xs = true ∧ xs.length = values.length) :
    evaluateTuple (expressions, before ++ values ++ env, state) = (.val values, state) := by
  induction values generalizing before expressions xs with
  | nil =>
    have empty : xs = [] := by cases xs <;> simp_all
    subst xs
    cases expressions with
    | nil => simp [evaluateTuple, evaluate]
    | cons head tail => cases head <;> simp [varListHOL] at h
  | cons value values ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases expressions with
      | nil => simp [varListHOL] at h
      | cons expression expressions =>
        cases expression with
        | var index =>
          simp only [varListHOL, Bool.and_eq_true, beq_iff_eq, List.length_cons,
            Nat.succ.injEq] at h
          rcases h with ⟨⟨rfl, rest⟩, lengths⟩
          have headRun : evaluateTuple ([.var before.length], before ++ (value :: values) ++ env, state) =
              (.val [value], state) := by
            simp [evaluateTuple, evaluate]
          have tailRun := ih (before ++ [value]) expressions xs (by simpa using ⟨rest, lengths⟩)
          have tailRun' : evaluateTuple (expressions, before ++ (value :: values) ++ env, state) =
              (.val values, state) := by simpa [List.append_assoc] using tailRun
          simp only [List.append_assoc, List.cons_append] at tailRun'
          rw [evaluateCons, headRun]
          simp [tailRun', Flapjack.holHd]
        | _ => simp [varListHOL] at h

/-- A zero-based variable list evaluates to the matching argument list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "var_list_IMP_evaluate" 1468
  (fmap_as_finite_support := [refs])]
theorem varListEvaluate_zero {C F : Type} (expressions xs : List Bvl.Exp)
    (values env : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (h : varListHOL 0 expressions xs = true ∧ xs.length = values.length) :
    evaluateTuple (expressions, values ++ env, state) = (.val values, state) := by
  simpa using varListEvaluate values [] expressions xs state env h

/-- A successful variable-list test compares lists of the same length. This
helper has no standalone HOL declaration. -/
theorem varListHOL_length {α : Type} (n : Nat) (expressions : List Bvl.Exp) (xs : List α)
    (valid : varListHOL n expressions xs = true) : expressions.length = xs.length := by
  induction expressions generalizing n xs with
  | nil => cases xs <;> simp_all [varListHOL]
  | cons expression rest ih =>
    cases xs with
    | nil => cases expression <;> simp_all [varListHOL]
    | cons x xs =>
      cases expression with
      | var index =>
        simp only [varListHOL, Bool.and_eq_true] at valid
        simp [ih (n + 1) xs valid.2]
      | _ => simp [varListHOL] at valid

/-- The local reduction underlying the let-operation pass preserves BVL
evaluation for all results, including type errors. This is a proof helper,
not a standalone HOL declaration. -/
theorem evaluateLetOpReduction {C F : Type} (bindings variables : List Bvl.Exp) (op : ClosLang.Op)
    (env : List BvlSem.Value) (state : State C F)
    (valid : varListHOL 0 variables bindings = true) :
    evaluateTuple ([.let bindings (.op op variables)], env, state) =
      evaluateTuple ([.op op bindings], env, state) := by
  cases bindingsRun : evaluate bindings env state with
  | mk result middle =>
    have bound : middle.clock ≤ state.clock := by
      have h := evaluate_clock_le bindings env state
      simpa [bindingsRun] using h
    cases result with
    | err error => simp [evaluateTuple, evaluate, bindingsRun, fixClock]
    | val values =>
      have resultLength := evaluateImpLength bindings env state values middle bindingsRun
      have varsRun := varListEvaluate_zero variables bindings values env middle ⟨valid, resultLength⟩
      change evaluate variables (values ++ env) middle = _ at varsRun
      simp [evaluateTuple, evaluate, bindingsRun, fixClock, Nat.min_eq_right bound, varsRun]

end Flapjack.Compiler.Backend.BvlInline.Proofs
