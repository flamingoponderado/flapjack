import Flapjack.Compiler.Backend.Semantics.ClosSem.GeneratedSize
import Flapjack.HolRef

/-! Generated closure-value sizes used by known-function correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem

/-- Generated value-list sizes add across concatenation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v1_size_append"]
theorem valueListSizeAppend (xs ys : List Value) :
    valueListSizeHOL (xs ++ ys) = valueListSizeHOL xs + valueListSizeHOL ys := by
  induction xs with
  | nil => simp [valueListSizeHOL]
  | cons x xs ih => simp [valueListSizeHOL, ih, Nat.add_assoc]

end Flapjack.Compiler.Backend.ClosKnown
