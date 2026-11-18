module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! Word-expression evaluation for assignment offsets. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace OffsetPort

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end OffsetPort

/-- The compiled offset expression evaluates to the original offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_real_offset_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getRealOffset_lemma {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (state : WordSemStateFiniteExact width C F) (input output : BitVec width)
    (conf : Config)
    (premises : WordSemStateFiniteExact.getVar v state = some (.word input) ∧
      goodDimindex width ∧ getRealOffset input = some output) :
    WordSemStateFiniteExact.wordExp state (realOffset conf v) = some (.word output) := by
  obtain ⟨read, good, offset⟩ := premises
  rcases good with h | h <;> subst width <;>
    simp [realOffset, getRealOffset, StackRemove.bytesInWord, wordSemBytesInWord,
      WordSemStateFiniteExact.wordExp, shiftN, theWords, wordOpHOL, wordShiftHOL, read] at offset ⊢ <;>
    subst output <;> simp [wordOp, BitVec.add_comm]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
