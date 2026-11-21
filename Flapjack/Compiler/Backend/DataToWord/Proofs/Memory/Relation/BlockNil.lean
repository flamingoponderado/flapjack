module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit

@[expose] public section

/-! The low-bit identity for nullary constructor encodings. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- The immediate encoding of a nullary constructor has its low bit clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "BlockNil_and_lemma"
  (words_as_type_indexed_bitvec)]
theorem blockNil_and_lemma {width : Nat} [NeZero width] (tag : BitVec width) (good : goodDimindex width) :
    (-2 : BitVec width) &&& (16 * tag + 2) = 16 * tag + 2 := by
  have low : (16 * tag + 2).getLsbD 0 = false := by
    rcases good with h | h <;> subst width <;> rw [bitLowToNat] <;>
      simp [BitVec.toNat_add, BitVec.toNat_mul] <;> omega
  have mask : (-2 : BitVec width) = ~~~(1 : BitVec width) := by
    rw [BitVec.not_eq_neg_add]
    rw [← BitVec.neg_add]
    congr 1
    exact BitVec.ofNat_add 1 1
  rw [mask, BitVec.and_comm, bitAndNotOneEq _ low]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
