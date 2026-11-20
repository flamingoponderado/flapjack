module

public import Flapjack.Compiler.Backend.Semantics.WordSem
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! The original byte-array write decomposition and word preservation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytearray_isWord"
  (words_as_type_indexed_bitvec)]
theorem writeBytearray_isWord {width : Nat} [NeZero width] (bytes : List (BitVec 8)) (address point : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (be : Bool) :
    wordSemIsWordLoc (memory point) = true →
      wordSemIsWordLoc (writeBytearrayExact address bytes memory domain be point) = true := by
  intro original
  induction bytes generalizing address with
  | nil => simpa [writeBytearrayExact] using original
  | cons byte bytes ih =>
    have tail := ih (address + 1)
    simp only [writeBytearrayExact]
    cases h : writeBytearrayExact (address + 1) bytes memory domain be (riscvByteAlignHOL address) with
    | loc n m =>
      simp only [BitVec.ofNat_eq_ofNat] at h
      simp [memStoreByteAuxExact, h, original, BitVec.ofNat_eq_ofNat]
    | word value =>
      simp only [BitVec.ofNat_eq_ofNat] at h tail
      by_cases inside : domain (riscvByteAlignHOL address) = true
      · simp only [memStoreByteAuxExact, BitVec.ofNat_eq_ofNat, h, inside, ite_true]
        by_cases eq : point = riscvByteAlignHOL address
        · simp [eq, wordSemIsWordLoc]
        · simpa [eq, BitVec.ofNat_eq_ofNat] using tail
      · simp [memStoreByteAuxExact, h, inside, original, BitVec.ofNat_eq_ofNat]

@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytearray_append"
  (words_as_type_indexed_bitvec)]
theorem writeBytearray_append {width : Nat} [NeZero width] (xs ys : List (BitVec 8)) (address : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (be : Bool) :
    (∀ i, i < xs.length + ys.length → ∃ b, memLoadByteAuxExact memory domain be (address + BitVec.ofNat width i) = some b) →
    writeBytearrayExact address (xs ++ ys) memory domain be =
      writeBytearrayExact address xs (writeBytearrayExact (address + BitVec.ofNat width xs.length) ys memory domain be) domain be := by
  induction xs generalizing address with
  | nil => simp [writeBytearrayExact]
  | cons byte xs ih =>
    intro valid
    have headRead : ∃ b, memLoadByteAuxExact memory domain be address = some b := by simpa using valid 0 (by simp; omega)
    have tailValid : ∀ i, i < xs.length + ys.length → ∃ b,
        memLoadByteAuxExact memory domain be (address + 1 + BitVec.ofNat width i) = some b := by
      intro i hi
      have h := valid (i + 1) (by simp; omega)
      have addrEq : address + 1 + BitVec.ofNat width i = address + BitVec.ofNat width (i + 1) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
        ac_rfl
      simpa only [← addrEq] using h
    have tailEq := ih (address + 1) tailValid
    simp only [List.cons_append, List.length_cons, writeBytearrayExact]
    rw [tailEq]
    have nextEq : address + 1 + BitVec.ofNat width xs.length = address + BitVec.ofNat width (xs.length + 1) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      ac_rfl
    rw [nextEq]
    obtain ⟨headByte, loaded⟩ := headRead
    cases old : memory (riscvByteAlignHOL address) with
    | loc n m => simp [memLoadByteAuxExact, old] at loaded
    | word value =>
      by_cases inside : domain (riscvByteAlignHOL address) = true
      · have original : wordSemIsWordLoc (memory (riscvByteAlignHOL address)) = true := by simp [old, wordSemIsWordLoc]
        have afterY := writeBytearray_isWord ys (address + BitVec.ofNat width (xs.length + 1))
          (riscvByteAlignHOL address) memory domain be original
        have afterX := writeBytearray_isWord xs (address + 1) (riscvByteAlignHOL address)
          (writeBytearrayExact (address + BitVec.ofNat width (xs.length + 1)) ys memory domain be) domain be afterY
        cases now : writeBytearrayExact (address + 1) xs
            (writeBytearrayExact (address + BitVec.ofNat width (xs.length + 1)) ys memory domain be) domain be (riscvByteAlignHOL address) with
        | loc n m =>
          simp only [BitVec.ofNat_eq_ofNat] at now afterX
          simp [now, wordSemIsWordLoc] at afterX
        | word value =>
          simp only [BitVec.ofNat_eq_ofNat] at now
          simp [memStoreByteAuxExact, BitVec.ofNat_eq_ofNat, now, inside]
      · simp [memLoadByteAuxExact, old, inside] at loaded

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
