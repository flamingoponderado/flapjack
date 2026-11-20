module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordShift64
@[expose] public section

/-! Word64 binary-operation prerequisites for the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The HOL 32-bit header conditions make the two-word header encodable. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_encode_header_NOT_NONE"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader32NotNone {width : Nat} [NeZero width] (conf : Config)
    (h : width = 32 ∧ 1 < conf.lenSize ∧ 1 < 30 - conf.lenSize) :
    encodeHeader conf 3 2 ≠ (none : Option (BitVec width)) := by
  obtain ⟨rfl, lenLower, lenUpper⟩ := h
  have lenBound : 2 < 2 ^ conf.lenSize := by
    have p : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have tagBound : 3 < 2 ^ (32 - conf.lenSize - 2) := by
    have p : 2 ^ 2 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simp [encodeHeader, lenBound, tagBound]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
