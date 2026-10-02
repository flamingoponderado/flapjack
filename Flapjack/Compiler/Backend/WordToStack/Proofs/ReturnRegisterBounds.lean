import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.StackProps.RegisterBounds

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- Full original stack movement bound implication, retaining the temporary
register bound and arbitrary continuation, offsets and number of moves. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_reg_bound" (words_as_type_indexed_bitvec)]
theorem stackMoveRegBound {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) (bound : Nat)
    (register : i < bound) (continuation : regBound p bound) :
    regBound (stackMoveNative n start offset i p) bound := by
  induction n generalizing start with
  | zero => exact continuation
  | succ n ih =>
      simpa only [stackMoveNative, regBound] using
        And.intro (ih (start + 1)) (And.intro register register)

/-- Full original descending return-copy bound, without a count, offset,
frame-size or word-width lower bound beyond HOL's positive word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_aux_reg_bound" (words_as_type_indexed_bitvec)]
theorem copyRetAuxRegBound {width : Nat} [NeZero width] (k f n : Nat) :
    regBound (copyRetAuxNative k f n : HolProg width) (k + 2) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simp only [copyRetAuxNative, listSeq, regBound]
      exact ⟨by omega, by omega, ih⟩

/-- Full original return-copy/free wrapper implication. Both Boolean modes
and independent return-value and unused frame-tail carriers are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_reg_bound" (words_as_type_indexed_bitvec)]
theorem copyRetRegBound {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (k f : Nat) (tail : γ) (vs : List β)
    (kont : HolProg width) (continuation : regBound kont (k + 2)) :
    regBound (copyRetNative perf isHandle (k,f,tail) vs kont) (k + 2) := by
  simp only [copyRetNative]
  split
  · exact continuation
  · refine ⟨copyRetAuxRegBound _ _ _, ?_⟩
    simp only [seqStackFreeNative]
    split
    · exact continuation
    · exact ⟨trivial, continuation⟩

end Flapjack.WordToStackProofs
