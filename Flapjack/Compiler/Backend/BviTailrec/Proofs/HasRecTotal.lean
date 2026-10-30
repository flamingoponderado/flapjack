import Flapjack.Compiler.Backend.BviTailrec

/-! Structural sufficiency for tail-recursion detection. These lemmas are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BviTailrec
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

private theorem foldRec_succeeds {α : Type} (xs : List α) (f : α → Option Bool)
    (init : Bool) (h : ∀ x ∈ xs, ∃ result, f x = some result) :
    ∃ result, xs.foldlM (fun found x => if found then pure true else f x) init = some result := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    cases init with
    | true =>
      obtain ⟨result, hr⟩ := ih true (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa using hr⟩
    | false =>
      obtain ⟨value, hv⟩ := h x (by simp)
      obtain ⟨result, hr⟩ := ih value (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa [hv] using hr⟩

/-- Recursion detection succeeds for every expression under its structural
fuel bound. -/
theorem hasRecFuel_succeeds (fuel loc : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, hasRecFuel fuel loc e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨y, hy⟩ := ih yes by'
      obtain ⟨z, hz⟩ := ih no bn
      cases y <;> exact ⟨_, by simp [hasRecFuel, hy, hz]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih body bb
      exact ⟨_, by simp [hasRecFuel, h]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [hasRecFuel, h]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds xs (hasRecFuel fuel loc) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases found : xs.any (isRec loc) with
      | false => exact ⟨result, by simpa [hasRecFuel, found] using h⟩
      | true => exact ⟨true, by simp [hasRecFuel, found]⟩
    | _ => exact ⟨_, rfl⟩

/-- The executable recursion analysis cannot fail from fuel exhaustion. -/
theorem hasRecBounded_succeeds (fuel loc : Nat) (e : Exp) :
    ∃ result, hasRecBounded fuel loc e = some result := by
  cases h : hasRecFuel fuel loc e with
  | some result => exact ⟨result, by simp [hasRecBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := hasRecFuel_succeeds (max fuel (expBudget e + 1)) loc e bound
    exact ⟨result, by simp [hasRecBounded, h, done]⟩

/-- The retry leaves every previously successful recursion result unchanged. -/
theorem hasRecBounded_eq_of_success (fuel loc : Nat) (e : Exp) (result : Bool)
    (success : hasRecFuel fuel loc e = some result) : hasRecBounded fuel loc e = some result := by
  simp [hasRecBounded, success]

end Flapjack.Compiler.Backend.BviTailrec
