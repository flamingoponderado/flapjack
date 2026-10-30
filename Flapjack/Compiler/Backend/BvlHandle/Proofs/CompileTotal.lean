import Flapjack.Compiler.Backend.BvlHandle

/-! Structural sufficiency for BVL handler live-variable compilation. These
are Flapjack infrastructure lemmas, not HOL correctness theorem ports. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi DbVars

mutual
/-- Live-variable compilation succeeds under a structural fuel bound. -/
theorem compileFuel_succeeds (fuel limit env : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, compileFuel fuel limit env e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var v => simp only [compileFuel]; split <;> exact ⟨_, rfl⟩
    | force loc v => simp only [compileFuel]; split <;> exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', lx, sx, nx⟩, hx⟩ := compileFuel_succeeds fuel limit env x bx
      obtain ⟨⟨y', ly, sy, ny⟩, hy⟩ := compileFuel_succeeds fuel limit env y by'
      obtain ⟨⟨z', lz, sz, nz⟩, hz⟩ := compileFuel_succeeds fuel limit env z bz
      exact ⟨_, by simp [compileFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      cases xs with
      | nil =>
        obtain ⟨result, h⟩ := compileFuel_succeeds fuel limit env body bb
        exact ⟨_, by simpa [compileFuel] using h⟩
      | cons x xs =>
        obtain ⟨⟨ys, lx, sx, nx⟩, hy⟩ := compileListFuel_succeeds fuel limit env (x :: xs) bx
        obtain ⟨⟨body', ly, sy, ny⟩, hb⟩ := compileFuel_succeeds fuel limit (env + (x :: xs).length) body bb
        simp only [List.length_cons] at hb
        exact ⟨_, by simp [compileFuel, hy, hb]; rfl⟩
    | handle x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', lx, sx, nx⟩, hx⟩ := compileFuel_succeeds fuel limit env x bx
      obtain ⟨⟨y', ly, sy, ny⟩, hy⟩ := compileFuel_succeeds fuel limit (env + 1) y by'
      cases nx <;> exact ⟨_, by simp [compileFuel, hx, hy]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', lx, sx, nx⟩, hx⟩ := compileFuel_succeeds fuel limit env x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', lx, sx, nx⟩, hx⟩ := compileFuel_succeeds fuel limit env x bx
      exact ⟨_, by simp [compileFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, ly, sy, ny⟩, hy⟩ := compileListFuel_succeeds fuel limit env xs bx
      simp only [compileFuel, hy]
      split <;> exact ⟨_, rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, ly, sy, ny⟩, hy⟩ := compileListFuel_succeeds fuel limit env xs bx
      exact ⟨_, by simp [compileFuel, hy]; rfl⟩
termination_by fuel

/-- Operand-list compilation succeeds under its structural fuel bound. -/
theorem compileListFuel_succeeds (fuel limit env : Nat) (xs : List Exp)
    (bound : listBudget xs < fuel) : ∃ result, compileListFuel fuel limit env xs = some result := by
  cases xs with
  | nil => cases fuel <;> exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨x', lx, sx, nx⟩, hx⟩ := compileFuel_succeeds fuel limit env x bx
      obtain ⟨⟨xs', ly, sy, ny⟩, hy⟩ := compileListFuel_succeeds fuel limit env xs bxs
      exact ⟨_, by simp [compileListFuel, hx, hy]; rfl⟩
termination_by fuel
end

/-- The executable retry cannot exhaust live-variable compilation fuel. -/
theorem compileBounded_succeeds (fuel limit env : Nat) (e : Exp) :
    ∃ result, compileBounded fuel limit env e = some result := by
  cases h : compileFuel fuel limit env e with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds (max fuel (expBudget e + 1)) limit env e bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

/-- Retrying preserves every previously successful live-variable result. -/
theorem compileBounded_eq_of_success (fuel limit env : Nat) (e : Exp)
    (result : Exp × DbVarSet × Nat × Bool) (success : compileFuel fuel limit env e = some result) :
    compileBounded fuel limit env e = some result := by
  simp [compileBounded, success]

end Flapjack.Compiler.Backend.BvlHandle
