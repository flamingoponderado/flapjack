import Flapjack.Compiler.Backend.BvlInline

/-! Structural sufficiency for BVL expression traversals. These lemmas are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlInline
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

/-- Inlining succeeds under a structural bound, for arbitrary caches. -/
theorem inlineExpFuel_succeeds (fuel : Nat) (cache : Spt (Nat × Exp)) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, inlineExpFuel fuel cache e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [inlineExpFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [inlineExpFuel, hy, hb]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [inlineExpFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [inlineExpFuel, hx]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [inlineExpFuel, hx, hy]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [inlineExpFuel, hy]; rfl⟩
    | call ticks target xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (inlineExpFuel fuel cache) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      cases target with
      | none => exact ⟨_, by simp [inlineExpFuel, hy]; rfl⟩
      | some name =>
        cases h : sptLookup name cache with
        | none => exact ⟨_, by simp [inlineExpFuel, hy, h]; rfl⟩
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          exact ⟨_, by simp [inlineExpFuel, hy, h]; rfl⟩

/-- The executable inliner cannot fail from traversal fuel. -/
theorem inlineExpBounded_succeeds (fuel : Nat) (cache : Spt (Nat × Exp)) (e : Exp) :
    ∃ result, inlineExpBounded fuel cache e = some result := by
  cases h : inlineExpFuel fuel cache e with
  | some result => exact ⟨result, by simp [inlineExpBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := inlineExpFuel_succeeds (max fuel (expBudget e + 1)) cache e bound
    exact ⟨result, by simp [inlineExpBounded, h, done]⟩

/-- Every previously successful inlining result is preserved. -/
theorem inlineExpBounded_eq_of_success (fuel : Nat) (cache : Spt (Nat × Exp)) (e result : Exp)
    (success : inlineExpFuel fuel cache e = some result) :
    inlineExpBounded fuel cache e = some result := by
  simp [inlineExpBounded, success]

/-- Tick removal succeeds under a structural fuel bound. -/
theorem removeTicksFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, removeTicksFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [removeTicksFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih body bb
      exact ⟨_, by simp [removeTicksFuel, hy, hb]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [removeTicksFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [removeTicksFuel, hx]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [removeTicksFuel, hx, hy]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [removeTicksFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (removeTicksFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [removeTicksFuel, hy]; rfl⟩

/-- Let-operation reduction succeeds under a structural fuel bound. -/
theorem letOpFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, letOpFuel fuel e = some result := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      obtain ⟨z', hz⟩ := ih z bz
      exact ⟨_, by simp [letOpFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (letOpFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := ih body bb
      cases body' <;> simp [letOpFuel, hy, hb] <;> repeat' (first | split | exact ⟨_, rfl⟩)
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [letOpFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      exact ⟨_, by simp [letOpFuel, hx]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨x', hx⟩ := ih x bx
      obtain ⟨y', hy⟩ := ih y by'
      exact ⟨_, by simp [letOpFuel, hx, hy]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (letOpFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [letOpFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (letOpFuel fuel) (by
        intro x hx; apply ih; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [letOpFuel, hy]; rfl⟩

/-- The tick-removal retry is total and preserves successful results. -/
theorem removeTicksBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, removeTicksBounded fuel e = some result := by
  cases h : removeTicksFuel fuel e with
  | some result => exact ⟨result, by simp [removeTicksBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := removeTicksFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [removeTicksBounded, h, done]⟩

theorem removeTicksBounded_eq_of_success (fuel : Nat) (e result : Exp)
    (success : removeTicksFuel fuel e = some result) : removeTicksBounded fuel e = some result := by
  simp [removeTicksBounded, success]

/-- The let-operation retry is total and preserves successful results. -/
theorem letOpBounded_succeeds (fuel : Nat) (e : Exp) :
    ∃ result, letOpBounded fuel e = some result := by
  cases h : letOpFuel fuel e with
  | some result => exact ⟨result, by simp [letOpBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := letOpFuel_succeeds (max fuel (expBudget e + 1)) e bound
    exact ⟨result, by simp [letOpBounded, h, done]⟩

theorem letOpBounded_eq_of_success (fuel : Nat) (e result : Exp)
    (success : letOpFuel fuel e = some result) : letOpBounded fuel e = some result := by
  simp [letOpBounded, success]

end Flapjack.Compiler.Backend.BvlInline
