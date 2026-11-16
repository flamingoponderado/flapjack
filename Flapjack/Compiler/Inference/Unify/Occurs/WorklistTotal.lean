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

/-- A flattened model of the source continuation's disjunction across all
    worklist entries. It is not tagged as the continuation-passing definition. -/
noncomputable def kcocwlModel (s : Spt InferT) (n : Nat) (work : List (List InferT)) : Bool := by
  classical
  exact if coclModel s work.flatten n then true else false

private theorem coclAppend (s : Spt InferT) (xs ys : List InferT) (n : Nat) :
    coclModel s (xs ++ ys) n ↔ coclModel s xs n ∨ coclModel s ys n := by
  simp [coclExists, List.mem_append, or_and_right, exists_or]

/-- The complete guarded tail-call equation for the source worklist model. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcocwl_tcallish"]
theorem kcocwlTcallishModel (s : Spt InferT) (n : Nat) : ∀ x,
    (fun _ : List (List InferT) => cwfs s) x →
      kcocwlModel s n x = Flapjack.HOL.tailCall (kcocwlCodeModel s n) (kcocwlModel s n) x := by
  classical
  intro x hw
  cases x with
  | nil => simp [kcocwlModel, coclModel, kcocwlCodeModel, Flapjack.HOL.tailCall]
  | cons head rest =>
    cases head with
    | nil => simp [kcocwlModel, kcocwlCodeModel, Flapjack.HOL.tailCall]
    | cons i xs =>
      have hc := cocThm s i n hw
      rw [tcwalkCorrectModel s i hw] at hc
      cases found : tcwalkModel s i with
      | varDb k =>
        simp [found] at hc
        simp [kcocwlModel, kcocwlCodeModel, Flapjack.HOL.tailCall, coclModel, hc, found]
      | app args name =>
        simp only [found] at hc
        simp only [← coclExists] at hc
        simp [kcocwlModel, kcocwlCodeModel, Flapjack.HOL.tailCall, coclModel, coclAppend, hc, found]
      | uvar v =>
        simp only [found] at hc
        by_cases eq : n = v
        · subst n
          have yes : cocModel s i v := hc.mpr rfl
          simp [kcocwlModel, kcocwlCodeModel, Flapjack.HOL.tailCall, coclModel, yes, found]
        · simp [kcocwlModel, kcocwlCodeModel, Flapjack.HOL.tailCall, coclModel, hc, found, eq]

/-- The original guarded continuation agrees with the selected total
    tail-recursive solution for every worklist. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcocwl_cleaned"]
theorem kcocwlCleanedModel (s : Spt InferT) (n : Nat) : ∀ x,
    (fun _ : List (List InferT) => cwfs s) x →
      kcocwlModel s n x = Flapjack.HOL.tailRecModel (kcocwlCodeModel s n) x := by
  intro x hw
  have wf : WellFounded (kcocwlRModel s n) := wfKcocwlRModel s n hw
  induction x using wf.induction with
  | h x ih =>
    rw [kcocwlTcallishModel s n x hw, Flapjack.HOL.tailRecModelEq]
    cases step : kcocwlCodeModel s n x with
    | inl y =>
      simp only [Flapjack.HOL.tailCall, step]
      exact ih y (kcocwlEnsuresDecreaseModel s n x y ⟨hw, step⟩)
    | inr result => simp [Flapjack.HOL.tailCall, step]

/-- The named total worklist operation agrees with the source continuation
    on every worklist under the original guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcocwl_correct0"]
theorem tcocwlCorrect0Model (s : Spt InferT) (n : Nat) : ∀ x,
    cwfs s → kcocwlModel s n x = tcocwlModel s n x := by
  intro x hw
  exact kcocwlCleanedModel s n x hw

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
