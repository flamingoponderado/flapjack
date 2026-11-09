module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefArrayElement
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference

@[expose] public section

/-! Updating the global-pointer store entries. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- A related immutable reference gives both its encoded pointer and its
simple machine address. This is Flapjack infrastructure for globals. -/
theorem memoryRel_refPtrTrueAddress {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (ptr : Nat) (location : WordLocW width)
    (vars : List (DataSem.Value × WordLocW width)) (good : goodDimindex width)
    (related : memoryRel conf be next refs space store memory domain ((.refPtr true ptr, location) :: vars)) :
    ∃ word addr, location = .word word ∧ getRealAddr conf store word = some addr ∧
      getRealSimpleAddr conf store word = some addr := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := absInv
  obtain ⟨f, tf, injF, _, _, _, _, _, _, stackRel, _⟩ := stackInv
  cases roots with
  | nil => cases stackRel
  | cons root rest =>
    cases stackRel with
    | cons first tail =>
      cases rootWords with
      | cons wordEq words =>
        obtain ⟨⟨pos, posLookup⟩, _, _, rootEq⟩ :=
          (valueInv_refPtr_true conf ptr refs root f tf heap).mp first
        have cell : isSomeDataElement (heapLookup pos heap) := by
          simpa [holFapply_of_lookup posLookup] using injF.1 ptr ⟨pos, posLookup⟩
        obtain ⟨pointers, size, data, cell⟩ := cell
        obtain ⟨curr, other, currAligned, otherAligned, currStore, restStore⟩ := heapMem.2.2.2.2.2.2.2
        have address := getRealAddr_getAddr conf store heap pos (.dataElement pointers size data) curr (.word 0)
          ⟨heapMem.1, cell, currStore, good⟩
        refine ⟨getAddr conf pos (.word 0), curr + BitVec.ofNat width pos * StackRemove.bytesInWord width, ?_, address.2, address.1⟩
        rw [holFapply_of_lookup posLookup] at rootEq
        simpa [rootEq, wordAddr] using wordEq.symm

/-- Updating only the globals and cached-address keys preserves heap/store
assertions and the source-to-word memory relation. -/
theorem memoryRel_setGlobals {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (vars : List (DataSem.Value × WordLocW width)) (word addr : BitVec width)
    (simple : getRealSimpleAddr conf store word = some addr)
    (related : memoryRel conf be next refs space store memory domain vars) :
    memoryRel conf be next refs space
      ((store.updateEq (.globals, .word word)).updateEq (.globReal, .word addr)) memory domain vars := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := related
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  have address : addr = curr + ((word >>> shiftLength conf) <<< wordShiftAmount width) := by
    simpa [getRealSimpleAddr, currStore] using simple.symm
  refine ⟨heap, limit, a, sp, sp1, gens, ?_, wordInv, limitBound, spaceBound⟩
  refine ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, ?_, curr, other, currAligned, otherAligned,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, separated⟩
  · simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using currStore
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using otherStore
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using nextStore
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using triggerStore
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using endStore
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using lengthStore
  · refine ⟨word, ?_, ?_⟩ <;> simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, address]
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using genInv

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
