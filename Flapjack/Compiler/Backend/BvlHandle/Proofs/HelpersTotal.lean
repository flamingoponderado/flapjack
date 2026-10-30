import Flapjack.Compiler.Backend.BvlHandle

/-! Structural sufficiency of handler helper traversals. These lemmas are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlHandle
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

private theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Raise detection succeeds under a structural traversal bound. -/
theorem canRaiseFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, canRaiseFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds [x, y, z] (canRaiseFuel fuel) false (by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> first | exact ih _ bx | exact ih _ by' | exact ih _ bz)
      exact ⟨result, by simpa [canRaiseFuel] using h⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds (body :: xs) (canRaiseFuel fuel) false (by
        intro e he; simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact ih _ bb
        · apply ih; have := member_budget_lt xs e he; omega)
      exact ⟨result, by simpa [canRaiseFuel] using h⟩
    | handle x y =>
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih y by'
      exact ⟨_, by simp [canRaiseFuel, h]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := ih x bx
      exact ⟨_, by simp [canRaiseFuel, h]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := foldRec_succeeds xs (canRaiseFuel fuel) false (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases op with
      | thunkOp thunk => cases thunk <;> simp_all [canRaiseFuel]
      | _ => exact ⟨result, by simpa [canRaiseFuel] using h⟩
    | _ => exact ⟨_, rfl⟩

/-- Variable adjustment succeeds under a structural traversal bound. -/
theorem adjustVarsFuel_succeeds (fuel depth shift : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, adjustVarsFuel fuel depth shift e = some result := by
  induction fuel generalizing depth e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      obtain ⟨y', hy⟩ := ih depth y by'
      obtain ⟨z', hz⟩ := ih depth z bz
      exact ⟨_, by simp [adjustVarsFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (adjustVarsFuel fuel depth shift) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih (depth + xs.length) body bb
      exact ⟨_, by simp [adjustVarsFuel, hy, hb]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      obtain ⟨y', hy⟩ := ih (depth + 1) y by'
      exact ⟨_, by simp [adjustVarsFuel, hx, hy]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      exact ⟨_, by simp [adjustVarsFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih depth x bx
      exact ⟨_, by simp [adjustVarsFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (adjustVarsFuel fuel depth shift) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [adjustVarsFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (adjustVarsFuel fuel depth shift) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [adjustVarsFuel, hy]; rfl⟩

/-- The raise-test retry cannot exhaust traversal fuel. -/
theorem canRaiseBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, canRaiseBounded fuel e = some result := by
  cases h : canRaiseFuel fuel e with
  | some result => exact ⟨result, by simp [canRaiseBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := canRaiseFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [canRaiseBounded, h, done]⟩

/-- The variable-adjustment retry cannot exhaust traversal fuel. -/
theorem adjustVarsBounded_succeeds (fuel depth shift : Nat) (e : Exp) :
    ∃ result, adjustVarsBounded fuel depth shift e = some result := by
  cases h : adjustVarsFuel fuel depth shift e with
  | some result => exact ⟨result, by simp [adjustVarsBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := adjustVarsFuel_succeeds (max fuel (expBudget e + 1)) depth shift e bound
    exact ⟨result, by simp [adjustVarsBounded, h, done]⟩

/-- Raise-test retries preserve previously successful results. -/
theorem canRaiseBounded_eq_of_success (fuel : Nat) (e : Exp) (result : Bool)
    (success : canRaiseFuel fuel e = some result) : canRaiseBounded fuel e = some result := by
  simp [canRaiseBounded, success]

/-- Variable-adjustment retries preserve previously successful results. -/
theorem adjustVarsBounded_eq_of_success (fuel depth shift : Nat) (e result : Exp)
    (success : adjustVarsFuel fuel depth shift e = some result) :
    adjustVarsBounded fuel depth shift e = some result := by
  simp [adjustVarsBounded, success]

end Flapjack.Compiler.Backend.BvlHandle
