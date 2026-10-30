import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractTotal

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
      obtain ⟨out, h⟩ := toBlockFuel_succeeds fuel n loc (.op op xs)
      cases out with
      | none => exact ⟨_, by simp [rewriteWrapperFuel, h]; rfl⟩
      | some item =>
        obtain ⟨bs, cb⟩ := item
        cases cb <;> exact ⟨_, by simp [rewriteWrapperFuel, h]; rfl⟩
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
      obtain ⟨out, h⟩ := toBlockFuel_succeeds fuel n loc (.op op xs)
      cases out with
      | none => exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
      | some item => obtain ⟨bs, cb⟩ := item; exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
    | call ticks dest xs handler =>
      obtain ⟨out, h⟩ := toBlockFuel_succeeds fuel n loc (.call ticks dest xs handler)
      cases out with
      | none => exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
      | some item => obtain ⟨bs, cb⟩ := item; exact ⟨_, by simp [rewriteWorkerFuel, h]; rfl⟩
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

/-- The executable retry never fails due to TMC traversal fuel. -/
theorem compileExpBounded_succeeds (fuel loc next arity : Nat) (e : Exp) :
    ∃ result, compileExpBounded fuel loc next arity e = some result := by
  cases h : compileExpFuel fuel loc next arity e with
  | some result => exact ⟨result, by simp [compileExpBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileExpFuel_succeeds (max fuel (expBudget e + 1)) loc next arity e bound
    exact ⟨result, by simp [compileExpBounded, h, done]⟩

/-- The retry preserves any previously successful TMC conversion result. -/
theorem compileExpBounded_eq_of_success (fuel loc next arity : Nat) (e : Exp)
    (result : Option (Exp × Exp)) (success : compileExpFuel fuel loc next arity e = some result) :
    compileExpBounded fuel loc next arity e = some result := by
  simp [compileExpBounded, success]

/-- Processing a program cannot fail due to TMC traversal fuel. -/
theorem compileEachFuel_succeeds (fuel next : Nat) (code : List (Nat × Nat × Exp)) :
    ∃ result, compileEachFuel fuel next code = some result := by
  induction code generalizing next with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨loc, arity, body⟩ := p
    obtain ⟨decision, hd⟩ := compileExpBounded_succeeds fuel loc next arity body
    cases decision with
    | none =>
      obtain ⟨⟨next', rest⟩, hr⟩ := ih next
      exact ⟨_, by simp [compileEachFuel, hd, hr]; rfl⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      obtain ⟨⟨next', rest⟩, hr⟩ := ih (next + Flapjack.bvlToBviNamespaces)
      exact ⟨_, by simp [compileEachFuel, hd, hr]; rfl⟩

/-- Whole-program TMC cannot fail because of its traversal bounds. This is
not the HOL pass-correctness theorem. -/
theorem compileProgFuel_succeeds (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) :
    ∃ result, compileProgFuel fuel enabled next code = some result := by
  cases enabled with
  | false => exact ⟨_, rfl⟩
  | true =>
    obtain ⟨result, h⟩ := compileEachFuel_succeeds fuel next code
    exact ⟨result, by simpa [compileProgFuel] using h⟩

end Flapjack.Compiler.Backend.BviTmc
