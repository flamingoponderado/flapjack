module

public import Flapjack.Compiler.Backend.ClosLetop.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

@[expose] public section

/-! Consecutive variables in closure let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop.Proofs
open ClosLang ClosSem

namespace VarListCarrier
/-- Canonical closure-state finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end VarListCarrier

/-- Successful variable-list recognition preserves length. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_IMP_LENGTH"]
theorem varList_length {α : Type} (n : Nat) (expressions : List ClosLang.Exp) (xs : List α)
    (valid : varList n expressions xs = true) : expressions.length = xs.length := by
  induction expressions generalizing n xs with
  | nil => cases xs <;> simp_all [varList]
  | cons expression rest ih =>
    cases xs with
    | nil => cases expression <;> simp_all [varList]
    | cons x xs =>
      cases expression with
      | var trace index =>
        simp only [varList, Bool.and_eq_true] at valid
        simp [ih (n + 1) xs valid.2]
      | _ => simp [varList] at valid

/-- Consecutive variable expressions recover the segment after a prefix. This
is the closure evaluator instance used by the let-operation simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_IMP_evaluate" 188
  (fmap_as_finite_support := [refs, code])]
theorem varListEvaluate {C F : Type} (values before : List Value)
    (expressions xs : List ClosLang.Exp) (state : State C F) (env : List Value)
    (h : varList before.length expressions xs = true ∧ xs.length = values.length) :
    evaluate expressions (before ++ values ++ env) state = (.val values, state) := by
  induction values generalizing before expressions xs with
  | nil =>
    have empty : xs = [] := by cases xs <;> simp_all
    subst xs
    cases expressions with
    | nil => simp [evaluate]
    | cons head tail => cases head <;> simp [varList] at h
  | cons value values ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases expressions with
      | nil => simp [varList] at h
      | cons expression expressions =>
        cases expression with
        | var trace index =>
          simp only [varList, Bool.and_eq_true, beq_iff_eq, List.length_cons,
            Nat.succ.injEq] at h
          rcases h with ⟨⟨rfl, rest⟩, lengths⟩
          have headRun : evaluate [.var trace before.length] (before ++ (value :: values) ++ env) state =
              (.val [value], state) := by
            simp [evaluate]
          have tailRun := ih (before ++ [value]) expressions xs (by simpa using ⟨rest, lengths⟩)
          have tailRun' : evaluate expressions (before ++ (value :: values) ++ env) state =
              (.val values, state) := by simpa [List.append_assoc] using tailRun
          rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ headRun, tailRun']
        | _ => simp [varList] at h

/-- Zero-based variable expressions recover the newly bound values. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_IMP_evaluate" 206
  (fmap_as_finite_support := [refs, code])]
theorem varListEvaluate_zero {C F : Type} (expressions xs : List ClosLang.Exp)
    (values env : List Value) (state : State C F)
    (h : varList 0 expressions xs = true ∧ xs.length = values.length) :
    evaluate expressions (values ++ env) state = (.val values, state) := by
  simpa using varListEvaluate values [] expressions xs state env h

/-- The local let-operation rewrite preserves the full closure evaluation,
including errors and effects. This helper has no standalone HOL declaration. -/
theorem evaluateLetOpReduction {C F : Type} (bindings variables : List ClosLang.Exp)
    (letTrace opTrace : BackendCommon.Tra) (op : ClosLang.Op)
    (env : List Value) (state : State C F)
    (valid : varList 0 variables bindings = true) :
    evaluate [.let letTrace bindings (.op opTrace op variables)] env state =
      evaluate [.op letTrace op bindings] env state := by
  cases bindingsRun : evaluate bindings env state with
  | mk result middle =>
    conv_lhs => rw [evaluate, fixClock_evaluate, bindingsRun]
    conv_rhs => rw [evaluate, fixClock_evaluate, bindingsRun]
    cases result with
    | err error => rfl
    | val values =>
      have length := (evaluate_length (C := C) (F := F)).1 bindings env state middle values bindingsRun
      have varsRun := varListEvaluate_zero variables bindings values env middle ⟨valid, length.symm⟩
      dsimp only
      conv_lhs => rw [evaluate, fixClock_evaluate, varsRun]

end Flapjack.Compiler.Backend.ClosLetop.Proofs
