module

public import Flapjack.Compiler.Inference.Unify.Occurs.WorklistWellFounded
public import Flapjack.Compiler.Inference.Unify.Occurs.Correctness

@[expose] public section

/-! The total occurs-check model and its connection to executed worklists. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- A solution of HOL's tail-recursion equation. On divergent inputs HOL's
    specified choice is unconstrained; agreement is claimed only under cwfs. -/
noncomputable def tcocwlModel (s : Spt InferT) (n : Nat) (work : List (List InferT)) : Bool :=
  Flapjack.HOL.tailRecModel (kcocwlCodeModel s n) work

private theorem occursWorkPartialEqTail (s : Spt InferT) (n : Nat) (hw : cwfs s) :
    ∀ work, occursWorkPartial s n work = Flapjack.HOL.tailRecPartial (kcocwlCodeModel s n) work := by
  have wf : WellFounded (kcocwlRModel s n) := wfKcocwlRModel s n hw
  intro work
  induction work using wf.induction with
  | h work ih =>
    cases work with
    | nil => simp [occursWorkPartial.eq_1, Flapjack.HOL.tailRecPartial.eq_1, kcocwlCodeModel]
    | cons head rest =>
      cases head with
      | nil =>
        rw [occursWorkPartial.eq_2, Flapjack.HOL.tailRecPartial.eq_1]
        simp only [kcocwlCodeModel]
        apply ih rest
        exact kcocwlEnsuresDecreaseModel s n _ _ ⟨hw, rfl⟩
      | cons i xs =>
        have walk := walkExecutableCorrect s hw i
        rw [tcwalkCorrectModel s i hw] at walk
        rw [occursWorkPartial.eq_3, walk, Flapjack.HOL.tailRecPartial.eq_1]
        cases found : tcwalkModel s i with
        | varDb k =>
          simp only [kcocwlCodeModel, found]
          apply ih (xs :: rest)
          exact kcocwlEnsuresDecreaseModel s n _ _ ⟨hw, by simp [kcocwlCodeModel, found]⟩
        | app args name =>
          simp only [kcocwlCodeModel, found]
          apply ih (args :: xs :: rest)
          exact kcocwlEnsuresDecreaseModel s n _ _ ⟨hw, by simp [kcocwlCodeModel, found]⟩
        | uvar v =>
          by_cases eq : n = v
          · simp [kcocwlCodeModel, found, eq]
          · have decrease := kcocwlEnsuresDecreaseModel s n ((i :: xs) :: rest) (xs :: rest)
              ⟨hw, by simp [kcocwlCodeModel, found, eq]⟩
            simpa [kcocwlCodeModel, found, eq] using ih (xs :: rest) decrease

/-- The complete source list-occurrence result on the original cwfs guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcocwl_correct"]
theorem tcocwlCorrectModel (s : Spt InferT) (ts : List InferT) (n : Nat) (hw : cwfs s) :
    coclModel s ts n ↔ tcocwlModel s n [ts] = true := by
  obtain ⟨b, run, agreement⟩ := occursWorkListCoclCorrect s ts n hw
  have htail : Flapjack.HOL.tailRecPartial (kcocwlCodeModel s n) [ts] = some b := by
    rw [← occursWorkPartialEqTail s n hw]
    exact run
  have result : tcocwlModel s n [ts] = b :=
    Flapjack.HOL.tailRecModelOfSome _ _ _ htail
  rw [result]
  exact agreement

end Flapjack.Compiler.Inference.Unify
