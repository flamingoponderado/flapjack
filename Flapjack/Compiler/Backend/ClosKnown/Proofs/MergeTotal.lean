import Flapjack.Compiler.Backend.ClosKnown.Compile
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Structural sufficiency for known-closure approximation merging. These
are Flapjack infrastructure lemmas, not HOL correctness theorem ports. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

private theorem member_budget_lt (xs : List ValApprox) (a : ValApprox) (h : a ∈ xs) :
    approxBudget a < approxListBudget xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [approxListBudget]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

private theorem zip_fst_mem {α β : Type} (xs : List α) (ys : List β) (p : α × β)
    (h : p ∈ xs.zip ys) : p.1 ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with same | h
      · cases same; simp
      · exact List.mem_cons_of_mem _ (ih ys h)

/-- Approximation merging succeeds when fuel exceeds the first input's
structural budget, independently of the second input. -/
theorem mergeFuel_succeeds (fuel : Nat) (a b : ValApprox) (bound : approxBudget a < fuel) :
    ∃ result, mergeFuel fuel a b = some result := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
    cases a with
    | tuple tag xs =>
      cases b with
      | tuple tag' ys =>
        have bx : approxListBudget xs < fuel := by simp_all [approxBudget] <;> omega
        obtain ⟨merged, hm⟩ := mapM_succeeds (xs.zip ys) (fun p => mergeFuel fuel p.1 p.2) (by
          intro p hp
          have member := zip_fst_mem xs ys p hp
          have small := member_budget_lt xs p.1 member
          exact ih p.1 p.2 (by omega))
        simp only [mergeFuel]
        split
        · exact ⟨_, rfl⟩
        · refine ⟨.tuple tag merged, ?_⟩
          change ((xs.zip ys).mapM (fun p => mergeFuel fuel p.1 p.2)).bind
            (fun result => some (ValApprox.tuple tag result)) = _
          rw [hm]
          rfl
      | _ => exact ⟨_, rfl⟩
    | _ => cases b <;> simp only [mergeFuel] <;> (try split) <;> exact ⟨_, rfl⟩

/-- The executable merge retry cannot exhaust traversal fuel. -/
theorem mergeBounded_succeeds (fuel : Nat) (a b : ValApprox) :
    ∃ result, mergeBounded fuel a b = some result := by
  cases h : mergeFuel fuel a b with
  | some result => exact ⟨result, by simp [mergeBounded, h]⟩
  | none =>
    have bound : approxBudget a < max fuel (approxBudget a + 1) := by omega
    obtain ⟨result, done⟩ := mergeFuel_succeeds (max fuel (approxBudget a + 1)) a b bound
    exact ⟨result, by simp [mergeBounded, h, done]⟩

/-- Retrying preserves every previously successful merge result. -/
theorem mergeBounded_eq_of_success (fuel : Nat) (a b result : ValApprox)
    (success : mergeFuel fuel a b = some result) : mergeBounded fuel a b = some result := by
  simp [mergeBounded, success]

end Flapjack.Compiler.Backend.ClosKnown
