import Flapjack.Compiler.Backend.BvlConst

/-! Structural sufficiency for BVL constant propagation. These are Flapjack
infrastructure lemmas, not HOL correctness theorem ports. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl BvlToBvi

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

private theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Constant propagation succeeds under a structural traversal bound. -/
theorem compileFuel_succeeds (fuel : Nat) (env : List (Option Exp)) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, compileFuel fuel env e = some result := by
  induction fuel generalizing env e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => simp only [compileFuel]; repeat' split <;> exact ⟨_, rfl⟩
    | force loc v => simp only [compileFuel]; repeat' split <;> exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env x bx
      obtain ⟨y', hy⟩ := ih env y by'
      obtain ⟨z', hz⟩ := ih env z bz
      simp [compileFuel, hx, hy, hz]
      split <;> simp_all
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih (extractList ys ++ env) body bb
      exact ⟨_, by simp [compileFuel, hy, hb]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env x bx
      obtain ⟨y', hy⟩ := ih (none :: env) y by'
      exact ⟨_, by simp [compileFuel, hx, hy]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih env x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (compileFuel fuel env) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩

/-- The executable constant-folding retry cannot exhaust traversal fuel. -/
theorem compileBounded_succeeds (fuel : Nat) (env : List (Option Exp)) (e : Exp) :
    ∃ result, compileBounded fuel env e = some result := by
  cases h : compileFuel fuel env e with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds (max fuel (expBudget e + 1)) env e bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

/-- Retrying preserves every previously successful constant-folding result. -/
theorem compileBounded_eq_of_success (fuel : Nat) (env : List (Option Exp)) (e result : Exp)
    (success : compileFuel fuel env e = some result) : compileBounded fuel env e = some result := by
  simp [compileBounded, success]

end Flapjack.Compiler.Backend.BvlConst
