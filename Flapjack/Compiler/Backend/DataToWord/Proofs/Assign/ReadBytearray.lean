module

public import Flapjack.Pancake.Semantics.LoopSem

@[expose] public section

/-! Pointwise reads determine the original polymorphic byte-array reader. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack

/-- The bounded list-index witness records the range already implied by the
original length equality and pointwise premise. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_read_bytearray_GENLIST"
  (words_as_type_indexed_bitvec)]
theorem imp_readBytearray_genList {width : Nat} [NeZero width] {α : Type} (values : List α) (len : Nat)
    (address : BitVec width) (reader : BitVec width → Option α) :
    len = values.length ∧
      (∀ i, i < len → ∃ (h : i < values.length), reader (address + BitVec.ofNat width i) = some values[i]) →
    readBytearrayGenericHOL address len reader = some values := by
  rintro ⟨rfl, reads⟩
  induction values generalizing address with
  | nil => rfl
  | cons head tail ih =>
    have first := reads 0 (by simp)
    have headRead : reader address = some head := by simpa using first
    have tailReads : ∀ i, i < tail.length → ∃ (h : i < tail.length),
        reader (address + 1 + BitVec.ofNat width i) = some tail[i] := by
      intro i hi
      obtain ⟨_, value⟩ := reads (i + 1) (by simp; omega)
      refine ⟨hi, ?_⟩
      have addrEq : address + 1 + BitVec.ofNat width i = address + BitVec.ofNat width (i + 1) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
        ac_rfl
      simpa only [List.getElem_cons_succ, ← addrEq] using value
    simp only [List.length_cons, readBytearrayGenericHOL, headRead]
    rw [ih (address + 1) tailReads]
    rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
