import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapReads

namespace Flapjack.Compiler.Backend.StackRemove.StoreHeapWrites
open Flapjack

/-- Full original local heap regrouping, on arbitrary predicate heaps. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "assoc_lem"]
theorem assocLem {α : Type} (A B C : (α → Prop) → Prop) :
    SetSep.star (SetSep.star A B) C = SetSep.star (SetSep.star B C) A := by
  rw [← SetSep.starAssoc, SetSep.starComm A (SetSep.star B C)]

/-- Flapjack structural proof factoring: expose one reverse-list slot and
retain the exact same surrounding heap assertion for every replacement value.
No separate named HOL theorem is claimed. -/
theorem wordListRevSlotSurgery {width : Nat} [NeZero width] {β : Type}
    (base : BitVec width) (values : List β) (index : Nat)
    (bound : index < values.length) :
    ∃ frame,
      wordListRev base values =
        SetSep.star (SetSep.one (base - bytesInWord width * BitVec.ofNat width (index + 1), values[index])) frame ∧
      ∀ value, wordListRev base (values.set index value) =
        SetSep.star (SetSep.one (base - bytesInWord width * BitVec.ofNat width (index + 1), value)) frame := by
  induction values generalizing base index with
  | nil => simp at bound
  | cons head values ih =>
    cases index with
    | zero =>
      refine ⟨wordListRev (base - bytesInWord width) values, ?_, ?_⟩
      · simp [wordListRev]
      · intro value
        simp [wordListRev]
    | succ index =>
      have smaller : index < values.length := by simpa using bound
      obtain ⟨frame, original, replacements⟩ := ih (base - bytesInWord width) index smaller
      have addressEq : base - bytesInWord width - bytesInWord width * BitVec.ofNat width (index + 1) =
          base - bytesInWord width * BitVec.ofNat width (index + 1 + 1) := by
        simp [BitVec.sub_sub, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_comm]
      rw [addressEq] at original replacements
      refine ⟨SetSep.star (SetSep.one (base - bytesInWord width, head)) frame, ?_, ?_⟩
      · simp only [wordListRev, List.getElem_cons_succ, original]
        rw [SetSep.starAssoc, SetSep.starComm (SetSep.one (base - bytesInWord width, head)), ← SetSep.starAssoc]
      · intro value
        simp only [List.set_cons_succ, wordListRev, replacements]
        rw [SetSep.starAssoc, SetSep.starComm (SetSep.one (base - bytesInWord width, head)), ← SetSep.starAssoc]

open Flapjack.Compiler.Backend.StackLang
/-- Flapjack proof factoring: the concrete original 48-slot layout has no
repeated store key. No independent named HOL declaration is claimed. -/
theorem storeListNodup : storeList.Nodup := by decide

/-- Flapjack proof factoring of one canonical store update as the exact single
ordered slot replacement. Equality is constructor and fixed-five-bit equality;
no Boolean equality-law premise is added. -/
theorem storeUpdateSlots {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (name : StoreName) (value : WordLocW width) (index : Nat)
    (bound : index < storeList.length) (slotEq : storeList[index] = name) :
    (storeList.map fun slot =>
      ((store.updateEq (StackSemRegisterTransfers.storeOfSyntax name, value)).lookup
        (StackSemRegisterTransfers.storeOfSyntax slot)).getD (.word 0)) =
    (storeList.map fun slot =>
      (store.lookup (StackSemRegisterTransfers.storeOfSyntax slot)).getD (.word 0)).set index value := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_set]
  · intro query leftBound rightBound
    have queryBound : query < storeList.length := by simpa only [List.length_map] using leftBound
    have codecEq : StackSemRegisterTransfers.storeOfSyntax storeList[query] =
        StackSemRegisterTransfers.storeOfSyntax name ↔ query = index := by
      constructor
      · intro equal
        have names := congrArg StackSemRegisterTransfers.storeToSyntax equal
        simp only [StackSemRegisterTransfers.storeToSyntax_storeOfSyntax] at names
        rw [← slotEq] at names
        exact (List.getElem_inj (h₀ := queryBound) (h₁ := bound) storeListNodup).mp names
      · intro equal
        subst query
        rw [slotEq]
    simp only [List.getElem_map, List.getElem_set, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, codecEq]
    by_cases same : query = index
    · simp [same]
    · simp [same, Ne.symm same]

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

open Classical in
/-- Full original store write: every original heap factor is retained and the
canonical store update is reflected by the exact target memory point update.
The written address and unaffected frame are derived, with no supplied domain,
frame-preservation, target execution or store-value premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "store_write_lemma"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem storeWriteLemma {width : Nat} [NeZero width] {C F : Type}
    (name : StoreName) (source : StackSemStateFiniteExact width C F)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (value : WordLocW width)
    (base : BitVec width)
    (hypothesis : name ∈ storeList ∧
      SetSep.star
        (SetSep.star
          (SetSep.star
            (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
              (Misc.wordList
                (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
                ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
            (Misc.wordListExists
              ((theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) +
                bytesInWord width * BitVec.ofNat width (source.dataBuffer.buffer.length + source.bitmaps.length))
              source.dataBuffer.spaceLeft))
          (wordStoreHOL base source.store))
        (Misc.wordList base source.stack)
        (SetSep.fun2Set (memory, domain))) :
    SetSep.star
        (SetSep.star
          (SetSep.star
            (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
              (Misc.wordList
                (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
                ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
            (Misc.wordListExists
              ((theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) +
                bytesInWord width * BitVec.ofNat width (source.dataBuffer.buffer.length + source.bitmaps.length))
              source.dataBuffer.spaceLeft))
          (wordStoreHOL base (source.store.updateEq (StackSemRegisterTransfers.storeOfSyntax name, value))))
        (Misc.wordList base source.stack)
        (SetSep.fun2Set ((fun key => if key = base + storeOffset name then value else memory key), domain)) := by
  rcases hypothesis with ⟨membership, heaps⟩
  obtain ⟨index, bound, nameEq, positionEq⟩ := StoreHeapReads.storeSlot name membership
  let values := storeList.map fun slot =>
    (source.store.lookup (StackSemRegisterTransfers.storeOfSyntax slot)).getD (.word 0)
  have mappedBound : index < values.length := by simpa [values] using bound
  obtain ⟨frame, original, replacements⟩ := wordListRevSlotSurgery base values index mappedBound
  have addressEq : base - bytesInWord width * BitVec.ofNat width (index + 1) =
      base + storeOffset name := by
    simp [storeOffset, wordOffset, positionEq, bytesInWord, BitVec.ofNat_mul,
      BitVec.sub_eq_add_neg]
  rw [addressEq] at original replacements
  have oldStoreEq : wordStoreHOL base source.store =
      SetSep.star (SetSep.one (base + storeOffset name, values[index])) frame := original
  have newStoreEq : wordStoreHOL base
      (source.store.updateEq (StackSemRegisterTransfers.storeOfSyntax name, value)) =
      SetSep.star (SetSep.one (base + storeOffset name, value)) frame := by
    rw [wordStoreHOL, storeUpdateSlots source.store name value index bound nameEq]
    exact replacements value
  have regroup (p q r : ((BitVec width × WordLocW width) → Prop) → Prop) :
      SetSep.star (SetSep.star p q) r = SetSep.star q (SetSep.star p r) := by
    rw [SetSep.starComm p q, ← SetSep.starAssoc]
  rw [regroup, oldStoreEq, ← SetSep.starAssoc] at heaps
  rw [regroup, newStoreEq, ← SetSep.starAssoc]
  have written := SetSep.writeFun2Set value (base + storeOffset name) values[index] _ memory domain heaps
  rw [SetSep.starComm] at written
  have functionEq : (fun key => if key = base + storeOffset name then value else memory key) =
      (fun key => @ite (WordLocW width) (key = base + storeOffset name)
        (Classical.propDecidable _) value (memory key)) := by
    funext key
    by_cases same : key = base + storeOffset name <;> simp only [same, ite_true, ite_false]
  rw [← functionEq] at written
  exact written

end Flapjack.Compiler.Backend.StackRemove.StoreHeapWrites
