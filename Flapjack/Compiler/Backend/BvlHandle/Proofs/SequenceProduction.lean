import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileProduction
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyProduction
import Flapjack.Compiler.Backend.BvlHandle.Proofs.Total

/-! Composition and sequence-splitting infrastructure. These declarations
are Flapjack-specific: the sequence traversal abstracts over the still
unproved constant-folding correspondence. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

/-- Once constant folding has returned, the executed handler stages return
the first component of the source-shaped singleton compiler. -/
theorem compileExpWithoutConstantsFuel_eq (fuel limit arity : Nat) (e : Exp) :
    compileExpWithoutConstantsFuel fuel limit arity e =
      some (compileSing limit arity (handleSimp e)).1 := by
  simp [compileExpWithoutConstantsFuel, simplifyBounded_eq, compileBounded_eq]

/-- The executable expression pipeline factors through constant folding and
the source-shaped handler compiler. -/
theorem compileExpFuel_eq (fuel limit arity : Nat) (e : Exp) :
    compileExpFuel fuel limit arity e =
      (BvlConst.compileBounded fuel [] e).map
        (fun folded => (compileSing limit arity (handleSimp folded)).1) := by
  cases h : BvlConst.compileBounded fuel [] e <;>
    simp [compileExpFuel, h, compileExpWithoutConstantsFuel_eq]

/-- Sequence splitting with an abstract total expression compiler. The
parameter isolates the outstanding constant-folding correspondence. -/
def compileSeqsWith (compileExp : Nat → Exp → Exp) (limit : Nat) : Exp → Option Exp → Exp
  | .let [x, y] (.var 1), acc =>
      compileSeqsWith compileExp limit x (some (compileSeqsWith compileExp limit y acc))
  | e, acc =>
      let e := compileExp limit e
      match acc with
      | none => e
      | some rest => .let [e] (.let [] (.let [] rest))
termination_by e _ => sizeOf e

/-- Successful sequence runs agree with the total traversal whenever the
expression compiler is independent of fuel and computes the supplied result. -/
theorem compileSeqsFuel_eq_of (compileExp : Nat → Exp → Exp)
    (expressionEq : ∀ fuel limit e, compileExpFuel fuel limit 0 e = some (compileExp limit e))
    (fuel limit : Nat) (e : Exp) (acc : Option Exp) (result : Exp)
    (run : compileSeqsFuel fuel limit e acc = some result) :
    result = compileSeqsWith compileExp limit e acc := by
  induction fuel generalizing e acc result with
  | zero => simp [compileSeqsFuel] at run
  | succ fuel ih =>
    by_cases shape : ∃ x y, e = Exp.let [x, y] (Exp.var 1)
    · obtain ⟨x, y, rfl⟩ := shape
      cases h : compileSeqsFuel fuel limit y acc with
      | none => simp [compileSeqsFuel, h] at run
      | some rest =>
        have erest := ih y acc rest h
        have erun := ih x (some rest) result (by simpa [compileSeqsFuel, h] using run)
        simpa [compileSeqsWith, ← erest] using erun
    · have notShape : ∀ x y, e = Exp.let [x, y] (Exp.var 1) → False := by
        intro x y h; exact shape ⟨x, y, h⟩
      rw [compileSeqsFuel.eq_3 limit e acc fuel notShape] at run
      rw [expressionEq fuel limit e] at run
      cases acc with
      | none =>
        rw [compileSeqsWith.eq_2 compileExp limit e notShape]
        simpa using run.symm
      | some rest =>
        rw [compileSeqsWith.eq_3 compileExp limit e rest notShape]
        simpa using run.symm

/-- The executable sequence retry has the same total result under the
expression-compiler correspondence. -/
theorem compileSeqsBounded_eq_of (compileExp : Nat → Exp → Exp)
    (expressionEq : ∀ fuel limit e, compileExpFuel fuel limit 0 e = some (compileExp limit e))
    (fuel limit : Nat) (e : Exp) (acc : Option Exp) :
    compileSeqsBounded fuel limit e acc = some (compileSeqsWith compileExp limit e acc) := by
  obtain ⟨result, run⟩ := compileSeqsBounded_succeeds fuel limit e acc
  have correct : result = compileSeqsWith compileExp limit e acc := by
    cases first : compileSeqsFuel fuel limit e acc with
    | some initial =>
      have h : initial = result := by simpa [compileSeqsBounded, first] using run
      subst result
      exact compileSeqsFuel_eq_of compileExp expressionEq fuel limit e acc initial first
    | none =>
      have second : compileSeqsFuel (max fuel (expBudget e + 1)) limit e acc = some result := by
        simpa [compileSeqsBounded, first] using run
      exact compileSeqsFuel_eq_of compileExp expressionEq _ limit e acc result second
  simpa [correct] using run

/-- The complete executable stage agrees with the abstract source-shaped
pipeline once constant folding supplies the expression correspondence. -/
theorem compileAnyFuel_eq_of (compileExp : Nat → Nat → Exp → Exp)
    (expressionEq : ∀ fuel limit arity e,
      compileExpFuel fuel limit arity e = some (compileExp limit arity e))
    (fuel : Nat) (splitSeq : Bool) (limit arity : Nat) (e : Exp) :
    compileAnyFuel fuel splitSeq limit arity e =
      some (if arity == 0 && splitSeq then
        compileSeqsWith (fun limit e => compileExp limit 0 e) limit e none
      else compileExp limit arity e) := by
  unfold compileAnyFuel
  split
  · exact compileSeqsBounded_eq_of (fun limit e => compileExp limit 0 e)
      (fun fuel limit e => expressionEq fuel limit 0 e) fuel limit e none
  · exact expressionEq fuel limit arity e

end Flapjack.Compiler.Backend.BvlHandle
