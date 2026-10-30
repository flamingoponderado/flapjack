import Flapjack.Compiler.Backend.BvlConst.Proofs.CompileProduction
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SequenceProduction

/-! Compose constant propagation with the handler traversal and sequence
splitting. These are Flapjack-specific executable correspondence theorems. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl

/-- Total expression pipeline using the source-shaped constant and handler
traversals. -/
def compileExpression (limit arity : Nat) (e : Exp) : Exp :=
  (compileSing limit arity (handleSimp (BvlConst.compileSing [] e))).1

/-- The executed expression pipeline returns the total composition. -/
theorem compileExpFuel_eq_source (fuel limit arity : Nat) (e : Exp) :
    compileExpFuel fuel limit arity e = some (compileExpression limit arity e) := by
  simp [compileExpFuel_eq, compileExpression, BvlConst.compileBounded_eq]

/-- The executed handler stage agrees with the total composition, including
sequence splitting and retrying. -/
theorem compileAnyFuel_eq_source (fuel : Nat) (splitSeq : Bool)
    (limit arity : Nat) (e : Exp) :
    compileAnyFuel fuel splitSeq limit arity e =
      some (if arity == 0 && splitSeq then
        compileSeqsWith (fun limit e => compileExpression limit 0 e) limit e none
      else compileExpression limit arity e) :=
  compileAnyFuel_eq_of compileExpression compileExpFuel_eq_source fuel splitSeq limit arity e

end Flapjack.Compiler.Backend.BvlHandle
