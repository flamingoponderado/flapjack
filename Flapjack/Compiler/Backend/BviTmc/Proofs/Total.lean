module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractCorrespondence

@[expose] public section

/-! Structural sufficiency for executable TMC rewriting. These proofs do not
establish correspondence with the HOL pass or its correctness theorem. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- Wrapper rewriting succeeds under a structural fuel bound. -/
theorem rewriteWrapperFuel_succeeds (fuel loc next n : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, rewriteWrapperFuel fuel loc next n e = some result := by
  induction fuel generalizing n e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨y, hy⟩ := ih n yes by'
      obtain ⟨z, hz⟩ := ih n no bn
      cases y <;> cases z <;> exact ⟨_, by simp [rewriteWrapperFuel, hy, hz]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨out, h⟩ := ih (n + xs.length) body bb
      exact ⟨_, by simp [rewriteWrapperFuel, h]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨out, h⟩ := ih n x bx
      exact ⟨_, by simp [rewriteWrapperFuel, h]; rfl⟩
    | op op xs =>
      have h := toBlockFuel_eq_source fuel n loc (.op op xs)
      cases out : toBlockSource n loc (.op op xs) with
      | none => exact ⟨_, by simp [rewriteWrapperFuel, h, out]; rfl⟩
      | some item =>
        obtain ⟨bs, cb⟩ := item
        cases cb <;> exact ⟨_, by simp [rewriteWrapperFuel, h, out]; rfl⟩
    | _ => exact ⟨_, rfl⟩

/-- Worker rewriting succeeds under a structural fuel bound. -/
theorem rewriteWorkerFuel_succeeds (fuel loc next ptr idx n : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, rewriteWorkerFuel fuel loc next ptr idx n e = some result := by
  induction fuel generalizing ptr idx n e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨y, hy⟩ := ih ptr idx n yes by'
      obtain ⟨z, hz⟩ := ih ptr idx n no bn
      exact ⟨_, by simp [rewriteWorkerFuel, hy, hz]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨out, h⟩ := ih (ptr + xs.length) (idx + xs.length) (n + xs.length) body bb
      exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨out, h⟩ := ih ptr idx n x bx
      exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
    | op op xs =>
      have h := toBlockFuel_eq_source fuel n loc (.op op xs)
      cases out : toBlockSource n loc (.op op xs) with
      | none => exact ⟨_, by simp [rewriteWorkerFuel, h, out]; rfl⟩
      | some item => obtain ⟨bs, cb⟩ := item; exact ⟨_, by simp [rewriteWorkerFuel, h, out]; rfl⟩
    | call ticks dest xs handler =>
      have h := toBlockFuel_eq_source fuel n loc (.call ticks dest xs handler)
      cases out : toBlockSource n loc (.call ticks dest xs handler) with
      | none => exact ⟨_, by simp [rewriteWorkerFuel, h, out]; rfl⟩
      | some item => obtain ⟨bs, cb⟩ := item; exact ⟨_, by simp [rewriteWorkerFuel, h, out]; rfl⟩
    | _ => exact ⟨_, rfl⟩

/-- A structurally sufficient budget makes both wrapper and worker rewriting
succeed. The inner `none` is the ordinary decision not to optimize. -/
theorem compileExpFuel_succeeds (fuel loc next arity : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, compileExpFuel fuel loc next arity e = some result := by
  obtain ⟨wrapper, hw⟩ := rewriteWrapperFuel_succeeds fuel loc next arity e bound
  cases wrapper with
  | none => exact ⟨_, by simp [compileExpFuel, hw]; rfl⟩
  | some w =>
    obtain ⟨worker, hs⟩ := rewriteWorkerFuel_succeeds fuel loc next arity (arity + 1) arity e bound
    exact ⟨_, by simp [compileExpFuel, hw, hs]; rfl⟩

end Flapjack.Compiler.Backend.BviTmc
