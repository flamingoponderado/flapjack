import Flapjack.Compiler.Backend.BvlInline

/-! Structural sufficiency for the BVL inliner's size analysis. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl BvlToBvi

mutual
/-- Expression-size analysis succeeds under a structural traversal bound. -/
theorem smallExpFuel_succeeds (fuel n : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, smallExpFuel fuel n e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := smallExpFuel_succeeds fuel n x bx
      exact ⟨_, by simp [smallExpFuel, h]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := smallExpFuel_succeeds fuel (n - 1) x bx
      by_cases zero : n - 1 = 0 <;> exact ⟨_, by simp [smallExpFuel, zero, h]; rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨nx, hx⟩ := smallExpFuel_succeeds fuel (n - 1) x bx
      obtain ⟨ny, hy⟩ := smallExpFuel_succeeds fuel nx y by'
      obtain ⟨nz, hz⟩ := smallExpFuel_succeeds fuel ny z bz
      by_cases h0 : n - 1 = 0 <;> by_cases h1 : nx = 0 <;> by_cases h2 : ny = 0 <;>
        exact ⟨_, by simp [smallExpFuel, h0, h1, h2, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨nx, hx⟩ := smallListFuel_succeeds fuel (n - 1) xs bx
      obtain ⟨nb, hb⟩ := smallExpFuel_succeeds fuel nx body bb
      by_cases h0 : n - 1 = 0 <;> by_cases h1 : nx = 0 <;>
        exact ⟨_, by simp [smallExpFuel, h0, h1, hx, hb]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨nx, hx⟩ := smallExpFuel_succeeds fuel (n - 1) x bx
      obtain ⟨ny, hy⟩ := smallExpFuel_succeeds fuel nx y by'
      by_cases h0 : n - 1 = 0 <;> by_cases h1 : nx = 0 <;>
        exact ⟨_, by simp [smallExpFuel, h0, h1, hx, hy]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := smallListFuel_succeeds fuel (n - 1) xs bx
      by_cases zero : n - 1 = 0 <;> exact ⟨_, by simp [smallExpFuel, zero, h]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨result, h⟩ := smallListFuel_succeeds fuel (n - 1) xs bx
      by_cases zero : n - 1 = 0 <;> exact ⟨_, by simp [smallExpFuel, zero, h]; rfl⟩
termination_by fuel

/-- List-size analysis succeeds under its structural traversal bound. -/
theorem smallListFuel_succeeds (fuel n : Nat) (xs : List Exp) (bound : listBudget xs < fuel) :
    ∃ result, smallListFuel fuel n xs = some result := by
  cases xs with
  | nil => cases fuel <;> exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨nx, hx⟩ := smallExpFuel_succeeds fuel n x bx
      obtain ⟨rest, hr⟩ := smallListFuel_succeeds fuel nx xs bxs
      by_cases h0 : n = 0 <;> by_cases h1 : nx = 0 <;>
        exact ⟨_, by simp [smallListFuel, h0, h1, hx, hr]; rfl⟩
termination_by fuel
end

/-- The executable retry cannot fail from size-analysis fuel. -/
theorem smallExpBounded_succeeds (fuel limit : Nat) (e : Exp) :
    ∃ result, smallExpBounded fuel limit e = some result := by
  cases h : smallExpFuel fuel limit e with
  | some result => exact ⟨result, by simp [smallExpBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := smallExpFuel_succeeds (max fuel (expBudget e + 1)) limit e bound
    exact ⟨result, by simp [smallExpBounded, h, done]⟩

/-- Retrying preserves every successful original size result. -/
theorem smallExpBounded_eq_of_success (fuel limit : Nat) (e : Exp) (result : Nat)
    (success : smallExpFuel fuel limit e = some result) : smallExpBounded fuel limit e = some result := by
  simp [smallExpBounded, success]

end Flapjack.Compiler.Backend.BvlInline
