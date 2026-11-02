import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefEquality

/-! Concrete byte-array words from the abstract memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend
open Classical
noncomputable section

/-- Rearrange separated heap assertions without changing their frame (Flapjack helper). -/
private theorem extractStar {α : Type} (p q r s t f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star p (SetSep.star (SetSep.star (SetSep.star q r) s) t)) f =
      SetSep.star q (SetSep.star r (SetSep.star p (SetSep.star s (SetSep.star t f)))) := by
  have : Std.Associative (SetSep.star (α := α)) := ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
  have : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩
  ac_rfl

/-- Byte packing preserves the number of input words (Flapjack helper). -/
private theorem writeBytes_length {width : Nat} [NeZero width] (bytes : List (BitVec 8))
    (words : List (BitVec width)) (be : Bool) :
    (DataToWord.writeBytes bytes words be).length = words.length := by
  induction words generalizing bytes with
  | nil => rfl
  | cons x xs ih => simp [DataToWord.writeBytes, ih]

/-- Extract a byte cell and its full frame from a word heap (Flapjack helper). -/
private theorem byteHeap {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (heap : ValueHeap width) (index : Nat) (bytes : List (BitVec 8))
    (words : List (BitVec width)) (be flag : Bool) (curr : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (bytesRep be flag bytes words))
    (assertion : SetSep.star (wordHeap curr heap conf) frame whole) :
    ∃ (rest : ((BitVec width × WordLocW width) → Prop) → Prop),
      SetSep.star (SetSep.one (curr + StackRemove.bytesInWord width * BitVec.ofNat width index,
          WordLocW.word (DataToWord.makeByteHeader conf flag bytes.length)))
        (SetSep.star (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
          StackRemove.bytesInWord width) ((DataToWord.writeBytes bytes words be).map WordLocW.word)) rest) whole ∧
      words.length < 2 ^ (width - 4) ∧
      WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader conf flag bytes.length) =
        BitVec.ofNat width words.length := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (bytesRep be flag bytes words) found
  subst heap
  subst index
  rw [wordHeapAppend] at assertion
  simp only [wordHeap, wordEl, bytesRep, wordPayload, List.isEmpty_nil, Bool.true_and,
    List.length_map, Misc.wordList, writeBytes_length] at assertion
  have facts := assertion
  obtain ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, _, _, pure⟩, _⟩⟩, _⟩ := facts
  have bounds := pure.2
  rw [extractStar] at assertion
  exact ⟨_, assertion, bounds.1, bounds.2.1⟩

/-- A related byte-array reference exposes its concrete packed word payload. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ByteArray_words_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_byteArrayWordsImp {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit flag : Bool) (index : Nat) (bytes : List (BitVec 8)) (w address : BitVec width)
    (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit index, .word w) :: vars) ∧
      sptLookup index refs = some (.byteArray flag bytes) ∧ goodDimindex width ∧
      getRealAddr conf store w = some address →
    ∃ header frame, memory address = .word header ∧
      SetSep.star (Misc.wordList (address + StackRemove.bytesInWord width)
        ((DataToWord.writeBytes bytes
          (List.replicate ((WordGcFunctions.decodeLength conf header).toNat) 0) be).map WordLocW.word)) frame
        (SetSep.fun2Set (memory, fun a => domain a = true)) ∧
      (WordGcFunctions.decodeLength conf header).toNat < 2 ^ width ∧
      (WordGcFunctions.decodeLength conf header).toNat = bytes.length / (width / 8) + 1 := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, found, good, addr⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, referenceInv⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have rootEq := valueInv_byteRefAddress conf bit index refs root f tf heap flag bytes found related
        have domainF : mapDomain f index := by
          rcases (valueInv_refPtr conf bit index refs root f tf heap).mp related with ordinary | thunk | inlined
          · exact ordinary.1
          · obtain ⟨_, _, _, eq, _⟩ := thunk
            rw [found] at eq
            cases eq
          · obtain ⟨_, eq, _⟩ := inlined
            rw [found] at eq
            cases eq
        obtain ⟨ptr, ffound⟩ := domainF
        have reachable : reachableRefs ((DataSem.Value.refPtr bit index) :: vars.map Prod.fst) refs index := by
          refine ⟨.refPtr bit index, index, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
        have cellInv := referenceInv index ⟨reachable, ⟨ptr, ffound⟩⟩
        have cell : heapLookup ptr heap = some
            (bytesRep be flag bytes (List.replicate (bytes.length / (width / 8) + 1) 0)) := by
          simpa [bcRefInv, ffound, found] using cellInv
        rw [holFapply_of_lookup ffound] at rootEq
        rw [rootEq] at projected
        have weq : w = getAddr conf ptr (.word 0) := by
          simpa [wordAddr] using (WordLocW.word.inj projected).symm
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        have addrCalc := (getRealAddr_getAddr conf store heap ptr _ curr (.word 0)
          ⟨heapMem.1, cell, stored, good⟩).2
        rw [weq] at addr
        have addressEq : address = curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr := by
          have eq := Option.some.inj (addr.symm.trans addrCalc)
          simpa [BitVec.mul_comm] using eq
        subst address
        obtain ⟨frame, split, bound, decoded⟩ := byteHeap conf heap ptr bytes
          (List.replicate (bytes.length / (width / 8) + 1) 0) be flag curr _ _ cell heapAssertion
        simp only [List.length_replicate] at bound decoded
        have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
        have countBound : bytes.length / (width / 8) + 1 < 2 ^ width := by omega
        have decodedNat : (WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader (width := width) conf flag bytes.length)).toNat =
            bytes.length / (width / 8) + 1 := by
          rw [decoded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
        refine ⟨DataToWord.makeByteHeader conf flag bytes.length,
          SetSep.star frame (SetSep.one (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
            WordLocW.word (DataToWord.makeByteHeader conf flag bytes.length))), ?_, ?_, ?_, decodedNat⟩
        · obtain ⟨left, right, partition, singleton, _⟩ := split
          have member : left (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
              .word (DataToWord.makeByteHeader conf flag bytes.length)) := by rw [singleton]
          have graph : SetSep.fun2Set (memory, fun a => domain a = true)
              (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
                .word (DataToWord.makeByteHeader conf flag bytes.length)) := by
            rw [← partition.1]
            exact Or.inl member
          exact ((SetSep.fun2SetThm memory _ _ _).mp graph).1
        · rw [decodedNat]
          rw [SetSep.starComm (SetSep.one _) _] at split
          rw [← SetSep.starAssoc] at split
          exact split
        · rw [decodedNat]
          exact countBound

/-- Header facts for a related byte array. This is Flapjack infrastructure
for the source reference-header classification theorem. -/
theorem memoryRel_byteArrayHeader {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit flag : Bool) (index : Nat) (bytes : List (BitVec 8)) (location : WordLocW width)
    (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.refPtr bit index, location) :: vars))
    (found : sptLookup index refs = some (.byteArray flag bytes)) (good : goodDimindex width) :
    ∃ w address, location = .word w ∧ w.getLsbD 0 = true ∧
      getRealAddr conf store w = some address ∧ getRealSimpleAddr conf store w = some address ∧
      memory address = .word (DataToWord.makeByteHeader conf flag bytes.length) ∧ domain address = true ∧
      conf.lenSize + 7 < width := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := rel
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, referenceInv⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have rootEq := valueInv_byteRefAddress conf bit index refs root f tf heap flag bytes found related
        have domainF : mapDomain f index := by
          rcases (valueInv_refPtr conf bit index refs root f tf heap).mp related with ordinary | thunk | inlined
          · exact ordinary.1
          · obtain ⟨_, _, _, eq, _⟩ := thunk
            rw [found] at eq
            cases eq
          · obtain ⟨_, eq, _⟩ := inlined
            rw [found] at eq
            cases eq
        obtain ⟨ptr, ffound⟩ := domainF
        have reachable : reachableRefs ((DataSem.Value.refPtr bit index) :: vars.map Prod.fst) refs index := by
          exact ⟨.refPtr bit index, index, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
        have cellInv := referenceInv index ⟨reachable, ⟨ptr, ffound⟩⟩
        have cell : heapLookup ptr heap = some
            (bytesRep be flag bytes (List.replicate (bytes.length / (width / 8) + 1) 0)) := by
          simpa [bcRefInv, ffound, found] using cellInv
        rw [holFapply_of_lookup ffound] at rootEq
        rw [rootEq] at projected
        have locEq : location = .word (getAddr conf ptr (.word 0)) := by simpa [wordAddr] using projected.symm
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        have addrCalc := getRealAddr_getAddr conf store heap ptr _ curr (.word 0)
          ⟨heapMem.1, cell, stored, good⟩
        obtain ⟨frame, split, _, _⟩ := byteHeap conf heap ptr bytes
          (List.replicate (bytes.length / (width / 8) + 1) 0) be flag curr _ _ cell heapAssertion
        obtain ⟨left, right, partition, singleton, _⟩ := split
        have member : left (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
            .word (DataToWord.makeByteHeader conf flag bytes.length)) := by rw [singleton]
        have graph : SetSep.fun2Set (memory, fun a => domain a = true)
            (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
              .word (DataToWord.makeByteHeader conf flag bytes.length)) := by
          rw [← partition.1]
          exact Or.inl member
        obtain ⟨memEq, inDomain⟩ := (SetSep.fun2SetThm memory _ _ _).mp graph
        refine ⟨getAddr conf ptr (.word 0), curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          locEq, getAddr_lowBit conf ptr _, ?_, ?_, memEq, inDomain, heapMem.2.2.2.2.1⟩
        · simpa [BitVec.mul_comm] using addrCalc.2
        · simpa [BitVec.mul_comm] using addrCalc.1

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
