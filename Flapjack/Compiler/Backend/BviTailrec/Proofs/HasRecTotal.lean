module

public import Flapjack.Compiler.Backend.BviTailrec
public import Flapjack.Compiler.Backend.ListFoldTotal

@[expose] public section

/-! Structural sufficiency for tail-recursion detection. These lemmas are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

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

end Flapjack.Compiler.Backend.BviTailrec
