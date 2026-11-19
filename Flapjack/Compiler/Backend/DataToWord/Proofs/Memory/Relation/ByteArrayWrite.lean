module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WriteBytearray
public import Flapjack.Misc.Sptree.InsertUnchanged

@[expose] public section

/-! Multi-byte writes preserve the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte
open Flapjack.Compiler.Backend.LabToTarget
noncomputable section

private theorem singletonWrite {width : Nat} [NeZero width] (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (be : Bool) (address : BitVec width) (byte old : BitVec 8)
    (good : goodDimindex width) (loaded : memLoadByteAuxExact memory domain be address = some old) :
    writeBytearrayExact address [byte] memory domain be =
      (fun key => if key = holByteAlign address then
        .word (setByte address byte (wordSemTheWord (memory (holByteAlign address))) be) else memory key) := by
  cases value : memory (holByteAlign address) with
  | loc a b => simp [memLoadByteAuxExact, riscvByteAlignHOL_eq good, value] at loaded
  | word value =>
    have inside : domain (holByteAlign address) = true := by
      by_cases h : domain (holByteAlign address) = true
      · exact h
      · simp [memLoadByteAuxExact, riscvByteAlignHOL_eq good, value, h] at loaded
    simp [writeBytearrayExact, memStoreByteAuxExact, riscvByteAlignHOL_eq good, value, inside,
      wordSemTheWord, setByteHOL8_eq]

@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_write_bytearray"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_writeBytearray {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (bit : Bool) (ptr : Nat) (w address : BitVec width)
    (vars : List (DataSem.Value × WordLocW width))
    (bytes old : List (BitVec 8)) (memory : BitVec width → WordLocW width)
    (refs : Spt (BvlSem.Ref DataSem.Value)) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word w) :: vars) ∧
    sptLookup ptr refs = some (.byteArray false old) ∧ bytes.length = old.length ∧
    getRealSimpleAddr conf store w = some address ∧ goodDimindex width →
    memoryRel conf be next (sptInsert ptr (.byteArray false bytes) refs) space store
      (writeBytearrayExact (address + StackRemove.bytesInWord width) bytes memory domain be)
      domain ((.refPtr bit ptr, .word w) :: vars) := by
  intro valid
  have aux : ∀ rest bytes old (memory : BitVec width → WordLocW width) (refs : Spt (BvlSem.Ref DataSem.Value)),
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word w) :: vars) ∧
    sptLookup ptr refs = some (.byteArray false (old ++ rest)) ∧ bytes.length = old.length ∧
    getRealSimpleAddr conf store w = some address ∧ goodDimindex width →
    memoryRel conf be next (sptInsert ptr (.byteArray false (bytes ++ rest)) refs) space store
      (writeBytearrayExact (address + StackRemove.bytesInWord width) bytes memory domain be)
      domain ((.refPtr bit ptr, .word w) :: vars) := by
    intro rest bytes
    induction bytes using List.reverseRecOn generalizing rest with
    | nil =>
      intro old memory refs ⟨related, found, equal, real, good⟩
      have oldNil : old = [] := by cases old <;> simp_all
      subst old
      simp only [List.nil_append] at found ⊢
      rw [sptInsertUnchanged refs ptr (.byteArray false rest) found]
      simpa [writeBytearrayExact] using related
    | append_singleton bytes byte ih =>
      intro old memory refs ⟨related, found, equal, real, good⟩
      induction old using List.reverseRecOn with
      | nil => simp at equal
      | append_singleton old oldByte =>
        have lengths : bytes.length = old.length := by simpa using equal
        have info := memoryRel_byteArrayImp (β := Unit) conf be next refs space store memory domain bit false ptr (old ++ [oldByte] ++ rest)
          (.word w) vars ⟨related, by simpa [List.append_assoc] using found, good⟩
        obtain ⟨w0, a0, header, _, loc, _, _, _, _, _, simple, _, _, _, loads, updates, _⟩ := info
        have wEq : w0 = w := by simpa using (WordLocW.word.inj loc).symm
        subst w0
        have aEq : a0 = address := Option.some.inj (simple.symm.trans real)
        subst a0
        have idxBound : old.length < (old ++ [oldByte] ++ rest).length := by simp
        have setEq : (old ++ [oldByte] ++ rest).set old.length byte = old ++ byte :: rest := by
          simp [List.set_append_right]
        have updated := updates old.length byte idxBound
        dsimp only at updated
        rw [setEq] at updated
        have loaded := loads old.length idxBound
        let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width old.length
        change memLoadByteAuxExact memory domain be ad = some _ at loaded
        have single := singletonWrite memory domain be ad byte _ good loaded
        rw [← single] at updated
        have afterLookup : sptLookup ptr (sptInsert ptr (.byteArray false (old ++ byte :: rest)) refs) =
            some (.byteArray false (old ++ byte :: rest)) := sptLookup_sptInsert_same _ _ _
        have nextRel := ih (byte :: rest) old (writeBytearrayExact ad [byte] memory domain be)
          (sptInsert ptr (.byteArray false (old ++ byte :: rest)) refs)
          ⟨updated, afterLookup, lengths, real, good⟩
        have allReads : ∀ i, i < bytes.length + [byte].length → ∃ b,
            memLoadByteAuxExact memory domain be ((address + StackRemove.bytesInWord width) + BitVec.ofNat width i) = some b := by
          intro i hi
          have bound : i < (old ++ [oldByte] ++ rest).length := by simp at *; omega
          exact ⟨_, loads i bound⟩
        have app := writeBytearray_append bytes [byte] (address + StackRemove.bytesInWord width) memory domain be allReads
        rw [lengths] at app
        rw [app]
        simpa [ad, sptInsert_insert_shadow, List.append_assoc] using nextRel
  simpa using aux [] bytes old memory refs (by simpa using valid)

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
