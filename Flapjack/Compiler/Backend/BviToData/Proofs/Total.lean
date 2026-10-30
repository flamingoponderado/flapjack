import Flapjack.Compiler.Backend.BviToData.Compile

/-! Structural bounds for the checked BVI-to-data traversal. These results
are Flapjack infrastructure, not a port of a HOL correctness theorem. -/
namespace Flapjack.Compiler.Backend.BviToData
open Bvi

mutual
theorem compileFuel_succeeds (fuel n : Nat) (env : List Nat) (tail : Bool)
    (live : List Nat) (exp : Bvi.Exp) (bound : expBudget exp < fuel) :
    ∃ result, compileFuel fuel n env tail live exp = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases exp with
    | var v =>
      simp only [compileFuel]
      split <;> exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have byBound : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨cx, vx, n1⟩, hx⟩ := compileFuel_succeeds fuel n env false live x bx
      obtain ⟨⟨cy, vy, n2⟩, hy⟩ := compileFuel_succeeds fuel n1 env tail live y byBound
      obtain ⟨⟨cz, vz, n3⟩, hz⟩ := compileFuel_succeeds fuel n2 env tail live z bz
      exact ⟨_, by simp [compileFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bxs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bxs
      obtain ⟨⟨body', v, n2⟩, hb⟩ := compileFuel_succeeds fuel n1 (vs ++ env) tail live body bb
      exact ⟨_, by simp [compileFuel, hc, hb]; rfl⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env false live x bx
      exact ⟨_, by simp [compileFuel, hc]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env tail live x bx
      exact ⟨_, by simp [compileFuel, hc]; rfl⟩
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      exact ⟨_, by simp [compileFuel, hc]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      exact ⟨_, by simp [compileFuel, hc]; rfl⟩
    | call ticks dest xs handler =>
      cases handler with
      | none =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
        exact ⟨_, by simp [compileFuel, hc]; rfl⟩
      | some h =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
        have bh : expBudget h < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨h', v, n2⟩, hh⟩ := compileFuel_succeeds fuel (n1 + 1) (n1 :: env) false live h bh
        exact ⟨_, by simp [compileFuel, hc, hh]; rfl⟩
    | letCall rets ticks dest xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      obtain ⟨⟨body', v, n2⟩, hb⟩ := compileFuel_succeeds fuel (n1 + rets)
        ((List.range rets).map (n1 + ·) ++ env) tail live body bb
      simp only [compileFuel, hc]
      split <;> simp [hb]
termination_by fuel

theorem compileListFuel_succeeds (fuel n : Nat) (env live : List Nat)
    (xs : List Bvi.Exp) (bound : listBudget xs < fuel) :
    ∃ result, compileListFuel fuel n env live xs = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases xs with
    | nil => exact ⟨_, rfl⟩
    | cons x xs =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env false live x bx
      cases xs with
      | nil => exact ⟨_, by simp [compileListFuel, hc]; rfl⟩
      | cons y ys =>
        obtain ⟨⟨rest, vs, n2⟩, hr⟩ := compileListFuel_succeeds fuel n1 env (v :: live) (y :: ys) bxs
        exact ⟨_, by simp [compileListFuel, hc, hr]; rfl⟩
termination_by fuel
end

/-- The production expression-lowering wrapper cannot fail from insufficient
fuel, independently of the caller's budget. -/
theorem compileExpBounded_succeeds (fuel argc : Nat) (exp : Bvi.Exp) :
    ∃ result, compileExpBounded fuel argc exp = some result := by
  cases h : compileExpFuel fuel argc exp with
  | some result => exact ⟨result, by simp [compileExpBounded, h]⟩
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    obtain ⟨⟨prog, _, _⟩, done⟩ :=
      compileFuel_succeeds (max fuel (expBudget exp + 1)) argc (List.range argc) true [] exp bound
    refine ⟨optimise prog, ?_⟩
    simp only [compileExpBounded, h]
    simp [compileExpFuel, done]

/-- Every previously successful result is unchanged by the retry wrapper. -/
theorem compileExpBounded_eq_of_success (fuel argc : Nat) (exp : Bvi.Exp)
    (result : DataLang.Prog) (success : compileExpFuel fuel argc exp = some result) :
    compileExpBounded fuel argc exp = some result := by
  simp [compileExpBounded, success]

end Flapjack.Compiler.Backend.BviToData
