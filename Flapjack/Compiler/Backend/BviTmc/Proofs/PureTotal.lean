import Flapjack.Compiler.Backend.BviTmc

/-! Structural sufficiency for the TMC purity traversal. These results are
Flapjack infrastructure; HOL correspondence remains a separate obligation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

private theorem member_budget_lt (xs : List Exp) (e : Exp) (h : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [listBudget]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

private theorem foldPure_succeeds {α : Type} (xs : List α) (f : α → Option Bool)
    (init : Bool) (h : ∀ x ∈ xs, ∃ result, f x = some result) :
    ∃ result, xs.foldlM (fun yes x => if yes then f x else pure false) init = some result := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    cases init with
    | false =>
      obtain ⟨result, hr⟩ := ih false (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa using hr⟩
    | true =>
      obtain ⟨value, hv⟩ := h x (by simp)
      obtain ⟨result, hr⟩ := ih value (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa [hv] using hr⟩

/-- The purity test succeeds whenever fuel exceeds the structural budget. -/
theorem pureFuel_succeeds (fuel n : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, pureFuel fuel n e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, hr⟩ := ih body bb
      obtain ⟨all, ha⟩ := foldPure_succeeds xs (pureFuel fuel n) true (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases result <;> simp_all [pureFuel] <;> exact ⟨_, rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨all, ha⟩ := foldPure_succeeds xs (pureFuel fuel n) true (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases h : pureOp op xs <;> simp_all [pureFuel] <;> exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩

/-- The executable purity wrapper cannot fail from insufficient fuel. -/
theorem pureBounded_succeeds (fuel n : Nat) (e : Exp) :
    ∃ result, pureBounded fuel n e = some result := by
  cases h : pureFuel fuel n e with
  | some result => exact ⟨result, by simp [pureBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := pureFuel_succeeds (max fuel (expBudget e + 1)) n e bound
    exact ⟨result, by simp [pureBounded, h, done]⟩

/-- Retrying preserves every successful result from the original budget. -/
theorem pureBounded_eq_of_success (fuel n : Nat) (e : Exp) (result : Bool)
    (success : pureFuel fuel n e = some result) : pureBounded fuel n e = some result := by
  simp [pureBounded, success]

end Flapjack.Compiler.Backend.BviTmc
