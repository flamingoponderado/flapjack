import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyTotal
import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileTotal
import Flapjack.Compiler.Backend.BvlConst.Proofs.Total

/-! Structural sufficiency of the executable BVL handler pipeline. These
proofs do not establish HOL correspondence or pass correctness. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

/-- Handler simplification and live-variable compilation succeed for every
input, independently of the caller's initial fuel. -/
theorem compileExpWithoutConstantsFuel_succeeds (fuel limit arity : Nat) (e : Exp) :
    ∃ result, compileExpWithoutConstantsFuel fuel limit arity e = some result := by
  obtain ⟨e', hs⟩ := simplifyBounded_succeeds fuel e
  obtain ⟨⟨out, live, size, safe⟩, hc⟩ := compileBounded_succeeds fuel limit arity e'
  exact ⟨out, by simp [compileExpWithoutConstantsFuel, hs, hc]⟩

/-- Constant propagation followed by handler compilation cannot exhaust
traversal fuel. -/
theorem compileExpFuel_succeeds (fuel limit arity : Nat) (e : Exp) :
    ∃ result, compileExpFuel fuel limit arity e = some result := by
  obtain ⟨e', hc⟩ := BvlConst.compileBounded_succeeds fuel [] e
  obtain ⟨out, hh⟩ := compileExpWithoutConstantsFuel_succeeds fuel limit arity e'
  exact ⟨out, by simp [compileExpFuel, hc, hh]⟩

/-- Sequence splitting succeeds with a structural bound on its input. -/
theorem compileSeqsFuel_succeeds (fuel limit : Nat) (e : Exp) (acc : Option Exp)
    (bound : expBudget e < fuel) : ∃ result, compileSeqsFuel fuel limit e acc = some result := by
  induction fuel generalizing e acc with
  | zero => omega
  | succ fuel ih =>
    by_cases shape : ∃ x y, e = Exp.let [x, y] (Exp.var 1)
    · obtain ⟨x, y, rfl⟩ := shape
      have bx : expBudget x < fuel := by simp_all [expBudget, listBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget, listBudget] <;> omega
      obtain ⟨rest, hr⟩ := ih y acc by'
      obtain ⟨result, hx⟩ := ih x (some rest) bx
      exact ⟨result, by simp [compileSeqsFuel.eq_2, hr, hx]⟩
    · have notShape : ∀ x y, e = Exp.let [x, y] (Exp.var 1) → False := by
        intro x y h; exact shape ⟨x, y, h⟩
      obtain ⟨result, h⟩ := compileExpFuel_succeeds fuel limit 0 e
      rw [compileSeqsFuel.eq_3 limit e acc fuel notShape]
      cases acc <;> exact ⟨_, by simp [h]; rfl⟩

/-- The executable sequence retry cannot exhaust traversal fuel. -/
theorem compileSeqsBounded_succeeds (fuel limit : Nat) (e : Exp) (acc : Option Exp) :
    ∃ result, compileSeqsBounded fuel limit e acc = some result := by
  cases h : compileSeqsFuel fuel limit e acc with
  | some result => exact ⟨result, by simp [compileSeqsBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileSeqsFuel_succeeds (max fuel (expBudget e + 1)) limit e acc bound
    exact ⟨result, by simp [compileSeqsBounded, h, done]⟩

/-- Sequence retries preserve any successful original result. -/
theorem compileSeqsBounded_eq_of_success (fuel limit : Nat) (e : Exp) (acc : Option Exp)
    (result : Exp) (success : compileSeqsFuel fuel limit e acc = some result) :
    compileSeqsBounded fuel limit e acc = some result := by
  simp [compileSeqsBounded, success]

/-- The full executable handler stage cannot fail from traversal fuel. This
is not the original HOL pass-correctness theorem. -/
theorem compileAnyFuel_succeeds (fuel : Nat) (splitSeq : Bool) (limit arity : Nat) (e : Exp) :
    ∃ result, compileAnyFuel fuel splitSeq limit arity e = some result := by
  unfold compileAnyFuel
  split
  · exact compileSeqsBounded_succeeds fuel limit e none
  · exact compileExpFuel_succeeds fuel limit arity e

end Flapjack.Compiler.Backend.BvlHandle
