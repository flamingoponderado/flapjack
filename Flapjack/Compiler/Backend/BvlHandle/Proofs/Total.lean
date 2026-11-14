module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyProduction
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileProduction
public import Flapjack.Compiler.Backend.BvlConst.Proofs.Total
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.SequenceRecognition

@[expose] public section

/-! Structural sufficiency of the executable BVL handler pipeline. These
proofs do not establish HOL correspondence or pass correctness. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

/-- Handler simplification and live-variable compilation succeed for every
input, independently of the caller's initial fuel. -/
theorem compileExpWithoutConstantsFuel_succeeds (fuel limit arity : Nat) (e : Exp) :
    ∃ result, compileExpWithoutConstantsFuel fuel limit arity e = some result := by
  simp [compileExpWithoutConstantsFuel, simplifyBounded_eq, compileBounded_eq]

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
      have bx : expBudget x < fuel := by simp_all [expBudget, listBudget]; omega
      have by' : expBudget y < fuel := by simp_all [expBudget, listBudget]; omega
      obtain ⟨rest, hr⟩ := ih y acc by'
      obtain ⟨result, hx⟩ := ih x (some rest) bx
      exact ⟨result, by simp [compileSeqsFuel, destSeq, hr, hx]⟩
    · have notSeq : destSeq e = none := by
        cases found : destSeq e with
        | none => rfl
        | some pair =>
          obtain ⟨x, y⟩ := pair
          exact False.elim (shape ⟨x, y, (destSeq_iff x y e).1 found⟩)
      obtain ⟨result, h⟩ := compileExpFuel_succeeds fuel limit 0 e
      cases acc <;> exact ⟨_, by simp [compileSeqsFuel, notSeq, h]; rfl⟩

end Flapjack.Compiler.Backend.BvlHandle
