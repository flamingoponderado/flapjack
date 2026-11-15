module

public import Flapjack.Misc.Option.MapM
public import Flapjack.Compiler.Backend.BvlHandle
public import Flapjack.Compiler.Backend.ListFoldTotal

@[expose] public section

/-! Structural sufficiency of handler helper traversals. These lemmas are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

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

end Flapjack.Compiler.Backend.BvlHandle
