module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeapUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.ByteArray

@[expose] public section

/-! The original byte-array memory relation, including reads and updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte
open Flapjack.Compiler.Backend.LabToTarget
noncomputable section

private theorem byteRelUpdate {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (bit flag : Bool) (ptr : Nat) (bytes : List (BitVec 8))
    (w address : BitVec width) (vars : List (DataSem.Value × WordLocW width)) (i : Nat) (byte : BitVec 8)
    (related : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word w) :: vars))
    (found : sptLookup ptr refs = some (.byteArray flag bytes)) (good : goodDimindex width)
    (real : getRealAddr conf store w = some address) (bound : i < bytes.length)
    (loaded : memLoadByteAuxExact memory domain be (address + StackRemove.bytesInWord width + BitVec.ofNat width i) = some bytes[i]) :
    let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width i
    memoryRel conf be next (sptInsert ptr (.byteArray flag (bytes.set i byte)) refs) space store
      (fun key => if key = holByteAlign ad then .word (setByte ad byte (wordSemTheWord (memory (holByteAlign ad))) be) else memory key)
      domain ((.refPtr bit ptr, .word w) :: vars) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, sizeBound, spaceBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  obtain ⟨tail, pre, post, words, rootsEq, heapEq, wordsEq, absUpdated⟩ :=
    updateByteRef conf bit ptr (vars.map Prod.fst) refs roots heap be a sp sp1 gens limit next flag bytes (bytes.set i byte)
      ⟨by simpa using absInv, found, by simp⟩
  subst heap
  rw [rootsEq] at rootWords
  cases rootWords with
  | cons rootWord restWords =>
    have wordEq : w = getAddr conf (heapLength pre) (.word 0) := by
      simpa [wordAddr] using (WordLocW.word.inj rootWord).symm
    obtain ⟨curr, other, _, _, currStore, _, _, _, _, _, _, _, _⟩ := heapMem.2.2.2.2.2.2.2
    have target := (getRealAddr_getAddr conf store _ (heapLength pre) (bytesRep be flag bytes words) curr (.word 0)
      ⟨heapMem.1, heapLookup_byteHeap_here pre post be flag bytes words, currStore, good⟩).2
    rw [wordEq] at real
    have addressEq : address = curr + BitVec.ofNat width (heapLength pre) * StackRemove.bytesInWord width :=
      Option.some.inj (real.symm.trans target)
    let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width i
    change memLoadByteAuxExact memory domain be ad = some bytes[i] at loaded
    have readExists : ∃ old, memory (holByteAlign ad) = .word old := by
      cases read : memory (holByteAlign ad) with
      | loc n m =>
        simp [memLoadByteAuxExact, riscvByteAlignHOL_eq good, read] at loaded
      | word old => exact ⟨old, rfl⟩
    obtain ⟨old, read⟩ := readExists
    have adEq : ad = curr + StackRemove.bytesInWord width + BitVec.ofNat width i +
        StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) := by
      dsimp [ad]
      rw [addressEq]
      simp only [BitVec.mul_comm]
      ac_rfl
    have heapNew := heapInMemoryStore_updateByte _ pre post a sp sp1 gens conf store memory domain limit be flag bytes words i ad curr old byte
      ⟨heapMem, rfl, bound, adEq, currStore, read, good⟩
    refine ⟨pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post, limit, a, sp, sp1, gens, ?_, ?_, sizeBound, spaceBound⟩
    · simpa [ad, read, wordSemTheWord] using heapNew
    · refine ⟨.pointer (heapLength pre) (.word 0) :: tail, ?_, ?_⟩
      · simpa [rootsEq] using absUpdated
      · exact .cons rootWord restWords

private theorem byteRelRead {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (bit flag : Bool) (ptr : Nat) (bytes : List (BitVec 8))
    (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width))
    (related : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, location) :: vars))
    (found : sptLookup ptr refs = some (.byteArray flag bytes)) (good : goodDimindex width) :
    ∃ w address, location = .word w ∧ getRealAddr conf store w = some address ∧
      ∀ i (bound : i < bytes.length), memLoadByteAuxExact memory domain be
        (address + StackRemove.bytesInWord width + BitVec.ofNat width i) = some bytes[i] := by
  obtain ⟨w, address, locEq, _, real, _, _, _, _, _⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain bit flag ptr bytes location vars related found good
  have relatedWord : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word w) :: vars) := by simpa [locEq] using related
  have wordInfo := memoryRel_byteArrayWordsImp conf be next refs space store memory domain bit flag ptr bytes w address vars
    ⟨relatedWord, found, good, real⟩
  obtain ⟨header, frame, _, payload, _, decoded⟩ := wordInfo
  rw [decoded] at payload
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  obtain ⟨tail, pre, post, words, rootsEq, heapEq, _, _⟩ :=
    updateByteRef conf bit ptr (vars.map Prod.fst) refs roots heap be a sp sp1 gens limit next flag bytes bytes
      ⟨by simpa using absInv, found, rfl⟩
  subst heap
  rw [rootsEq] at rootWords
  cases rootWords with
  | cons rootWord restWords =>
    have wordEq : w = getAddr conf (heapLength pre) (.word 0) := by
      rw [locEq] at rootWord
      simpa [wordAddr] using (WordLocW.word.inj rootWord).symm
    obtain ⟨curr, other, currAligned, _, currStore, _, _, _, _, _, _, _, _⟩ := heapMem.2.2.2.2.2.2.2
    have target := (getRealAddr_getAddr conf store _ (heapLength pre) (bytesRep be flag bytes words) curr (.word 0)
      ⟨heapMem.1, heapLookup_byteHeap_here pre post be flag bytes words, currStore, good⟩).2
    have real2 := real
    rw [wordEq] at real2
    have addressEq : address = curr + BitVec.ofNat width (heapLength pre) * StackRemove.bytesInWord width :=
      Option.some.inj (real2.symm.trans target)
    have currMod := (Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.byteAligned_iff_divisible curr good).mp currAligned
    have baseMod : (address + StackRemove.bytesInWord width).toNat % (width / 8) = 0 := by
      rw [addressEq]
      rcases good with h | h <;> subst width <;>
        norm_num [StackRemove.bytesInWord, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_ofNat, Nat.mod_mod_of_dvd, Nat.add_mod, Nat.mul_mod] at * <;> assumption
    have capacity : bytes.length ≤ (List.replicate (bytes.length / (width / 8) + 1) (0 : BitVec width)).length * (width / 8) := by
      rcases good with h | h <;> subst width <;> simp <;> omega
    refine ⟨w, address, locEq, real, ?_⟩
    intro i bound
    exact wordList_packedByteRead bytes (List.replicate (bytes.length / (width / 8) + 1) 0) be i good capacity bound
      (address + StackRemove.bytesInWord width) baseMod memory domain frame payload


private theorem headerShift {width : Nat} [NeZero width] (conf : DataToWord.Config) (flag : Bool) (len : Nat)
    (good : goodDimindex width) (config : conf.lenSize + 7 < width)
    (valid : len + 2 ^ (if width = 32 then 2 else 3) < 2 ^ (conf.lenSize + (if width = 32 then 2 else 3))) :
    (makeByteHeader conf flag len : BitVec width) >>> (width - (if width = 32 then 2 else 3) - conf.lenSize) =
      BitVec.ofNat width (len + 2 ^ (if width = 32 then 2 else 3)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases small : i < conf.lenSize + (if width = 32 then 2 else 3)
  · rw [Nat.add_comm]
    exact byteHeaderLengthBit conf flag len i good config small
  · have high : width ≤ width - (if width = 32 then 2 else 3) - conf.lenSize + i := by
      rcases good with h | h <;> subst width <;> simp at * <;> omega
    have pow : 2 ^ (conf.lenSize + (if width = 32 then 2 else 3)) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have zero : (len + 2 ^ (if width = 32 then 2 else 3)).testBit i = false := Nat.testBit_lt_two_pow (by omega)
    rw [BitVec.getLsbD_of_ge _ _ high, zero]

/-- Byte-array representation and update facts, retaining HOL's independent
unused existential witness. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ByteArray_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)
  (hol_unused_existential_inhabitants := [β._unused])]
theorem memoryRel_byteArrayImp {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (bit flag : Bool) (ptr : Nat) (bytes : List (BitVec 8))
    (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, location) :: vars) ∧
    sptLookup ptr refs = some (.byteArray flag bytes) ∧ goodDimindex width →
    ∃ w address header, ∃ (_unused : β), location = .word w ∧ w.getLsbD 0 = true ∧
      makeByteHeader conf flag bytes.length = header ∧
      header.getLsbD 3 = false ∧ (header.getLsbD 4 = true ↔ flag = false) ∧ header.getLsbD 2 = true ∧
      getRealSimpleAddr conf store w = some address ∧ getRealAddr conf store w = some address ∧
      memory address = .word header ∧ domain address = true ∧
      (∀ i (h : i < bytes.length), memLoadByteAuxExact memory domain be
        (address + StackRemove.bytesInWord width + BitVec.ofNat width i) = some bytes[i]) ∧
      (∀ i (byte : BitVec 8), i < bytes.length →
        let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width i
        memoryRel conf be next (sptInsert ptr (.byteArray flag (bytes.set i byte)) refs) space store
          (fun key => if key = holByteAlign ad then .word (setByte ad byte (wordSemTheWord (memory (holByteAlign ad))) be) else memory key)
          domain ((.refPtr bit ptr, location) :: vars)) ∧
      if width = 32 then
        bytes.length + 4 < 2 ^ (width - 3) ∧
        header >>> (width - conf.lenSize - 2) = BitVec.ofNat width (bytes.length + 4)
      else
        bytes.length + 8 < 2 ^ (width - 3) ∧
        header >>> (width - conf.lenSize - 3) = BitVec.ofNat width (bytes.length + 8) := by
  rintro ⟨related, found, good⟩
  obtain ⟨w, address, locEq, bit0, real, simple, mem, member, config, valid⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain bit flag ptr bytes location vars related found good
  obtain ⟨w2, address2, loc2, real2, reads⟩ := byteRelRead conf be next refs space store memory domain bit flag ptr bytes location vars related found good
  have wEq : w2 = w := WordLocW.word.inj (loc2.symm.trans locEq)
  subst w2
  have addressEq : address2 = address := Option.some.inj (real2.symm.trans real)
  subst address2
  have bits := byteHeaderBits conf bytes.length flag good config
  refine ⟨w, address, makeByteHeader conf flag bytes.length, Classical.choice inferInstance,
    locEq, bit0, rfl, bits.1, ?_, bits.2, simple, real, mem, member, reads, ?_, ?_⟩
  · rcases good with hw | hw <;> subst width
    · have h : ¬ (4 : Nat) ≥ 32 - 2 - conf.lenSize := by omega
      cases flag <;> simp [makeByteHeader, h]
    · have h : ¬ (4 : Nat) ≥ 64 - 3 - conf.lenSize := by omega
      cases flag <;> simp [makeByteHeader, h]
  · intro i byte bound
    have relatedWord : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word w) :: vars) := by simpa [locEq] using related
    simpa [locEq] using byteRelUpdate conf be next refs space store memory domain bit flag ptr bytes w address vars i byte relatedWord found good real bound (reads i bound)
  · rcases good with hw | hw <;> subst width
    · have bound : bytes.length + 4 < 2 ^ (conf.lenSize + 2) := by simpa using valid
      have power : 2 ^ (conf.lenSize + 2) ≤ 2 ^ (32 - 3) := Nat.pow_le_pow_right (by decide) (by omega)
      refine ⟨by omega, ?_⟩
      have e : 32 - conf.lenSize - 2 = 32 - 2 - conf.lenSize := by omega
      rw [e]
      simpa using headerShift conf flag bytes.length (Or.inl rfl) config valid
    · simp only [show 64 ≠ 32 by decide, ↓reduceIte]
      have bound : bytes.length + 8 < 2 ^ (conf.lenSize + 3) := by simpa using valid
      have power : 2 ^ (conf.lenSize + 3) ≤ 2 ^ (64 - 3) := Nat.pow_le_pow_right (by decide) (by omega)
      refine ⟨by omega, ?_⟩
      have e : 64 - conf.lenSize - 3 = 64 - 3 - conf.lenSize := by omega
      rw [e]
      simpa using headerShift conf flag bytes.length (Or.inr rfl) config valid

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
