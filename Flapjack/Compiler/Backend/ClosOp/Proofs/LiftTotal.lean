import Flapjack.Compiler.Backend.ClosOp
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Fuel sufficiency for the executable smart-operation lifting helper. This
is Flapjack infrastructure, rather than a port of a HOL theorem. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

private theorem cons_budget (x : Exp) (tag : Nat) (ys : List Exp)
    (h : cons x = some (tag, ys)) : listBudget ys < expBudget x := by
  cases x <;> simp [cons] at h
  case op t op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag' =>
        rcases h with ⟨rfl, rfl⟩
        simp [expBudget]

/-- A structural budget suffices for lifting arbitrary nested constructors. -/
theorem liftFuel_succeeds (fuel : Nat) (xs : List Exp) (n : Nat) (binds : List Exp)
    (bound : listBudget xs < fuel) :
    ∃ result, liftFuel fuel xs n binds = some result := by
  induction fuel generalizing xs n binds with
  | zero => omega
  | succ fuel ih =>
    cases xs with
    | nil => exact ⟨_, rfl⟩
    | cons x xs =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      cases hd : dontLift x with
      | true =>
        obtain ⟨⟨xs', n', binds'⟩, ht⟩ := ih xs n binds bs
        exact ⟨_, by simp [liftFuel, hd, ht]; rfl⟩
      | false =>
        cases hc : cons x with
        | none =>
          obtain ⟨⟨xs', n', binds'⟩, ht⟩ := ih xs (n + 1) (binds ++ [x]) bs
          exact ⟨_, by simp [liftFuel, hd, hc, ht]; rfl⟩
        | some p =>
          obtain ⟨tag, ys⟩ := p
          have bys : listBudget ys < fuel := by have := cons_budget x tag ys hc; omega
          obtain ⟨⟨ys', n', binds'⟩, hy⟩ := ih ys n binds bys
          obtain ⟨⟨xs', n'', binds''⟩, ht⟩ := ih xs n' binds' bs
          exact ⟨_, by simp [liftFuel, hd, hc, hy, ht]; rfl⟩

/-- Retried lifting cannot exhaust fuel. -/
theorem liftBounded_succeeds (fuel : Nat) (xs : List Exp) (n : Nat) (binds : List Exp) :
    ∃ result, liftBounded fuel xs n binds = some result := by
  cases h : liftFuel fuel xs n binds with
  | some result => exact ⟨result, by simp [liftBounded, h]⟩
  | none =>
    have bound : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, done⟩ := liftFuel_succeeds (max fuel (listBudget xs + 1)) xs n binds bound
    exact ⟨result, by simp [liftBounded, h, done]⟩

/-- Retrying preserves every successful result of the original traversal. -/
theorem liftBounded_eq_of_success (fuel : Nat) (xs : List Exp) (n : Nat) (binds : List Exp)
    (result : List Exp × Nat × List Exp) (h : liftFuel fuel xs n binds = some result) :
    liftBounded fuel xs n binds = some result := by
  simp [liftBounded, h]

end Flapjack.Compiler.Backend.ClosOp
