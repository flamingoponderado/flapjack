module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.DataToWord.Bytes
@[expose] public section

/-! Original HOL observations for pointer-tag and heap representation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack
open Flapjack.HolByte

set_option maxRecDepth 8192 in
example : setByte (3 : BitVec 32) (255 : BitVec 8)
    (bytesToWord 4 0 [17, 34, 51, 68] (0xAABBCCDD : BitVec 32) false) false = 0xFF332211 := by decide
set_option maxRecDepth 8192 in
example : setByte (3 : BitVec 32) (255 : BitVec 8)
    (bytesToWord 4 0 [17, 34, 51, 68] (0xAABBCCDD : BitVec 32) true) true = 0x112233FF := by decide
set_option maxRecDepth 8192 in
example : setByte (7 : BitVec 64) (255 : BitVec 8)
    (bytesToWord 8 0 [1, 2, 3, 4, 5, 6, 7, 8] (0 : BitVec 64) false) false = 0xFF07060504030201 := by decide
set_option maxRecDepth 8192 in
example : setByte (7 : BitVec 64) (255 : BitVec 8)
    (bytesToWord 8 0 [1, 2, 3, 4, 5, 6, 7, 8] (0 : BitVec 64) true) true = 0x01020304050607FF := by decide

private def config : Config := ⟨1, 2, 0, 4, false, false, false, false, false, false, .none⟩

example : getLowerBits config (.word (255 : BitVec 8)) = 15 := by decide

example : getLowerBits { config with lenBits := 20 } (.word (254 : BitVec 8)) = 255 := by decide

example : wordAddr config (.data (.loc 7 9) : HeapAddress (WordLocW 8)) = .loc 7 0 := by rfl

example : wordAddr config (.data (.word (255 : BitVec 8))) = .word 254 := by decide

example : wordAddr config (.pointer 2 (.word (255 : BitVec 8))) = .word 79 := by decide

example : (blockNil 2 : BitVec 8) = 34 := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [.data (.word 3)] 1 (.blockTag 1) [] config).2.2 = true := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [.data (.word 3)] 0 .refTag [] config).2.2 = false := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [.data (.word 3)] 1 (.thunkTag .evaluated) [] config).2.2 = true := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [] 1 .word64Tag [.word 5] config).2.2 = true := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [] 1 (.numTag true) [.word 5] config).2.2 = true := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [] 0 (.bytesTag true 59) [] config).2.2 = true := by decide

example : (wordPayload (headerWidth := 32) (payloadWidth := 64)
    [] 0 (.bytesTag true 60) [] config).2.2 = false := by decide

example : genStartsInStore (width := 32) { config with gcKind := .generational [10, 20] }
    (.genState 0 [2, 4]) (some (.word 8)) := by
  simp [genStartsInStore, StackRemove.bytesInWord]

example : ¬ genStartsInStore (width := 32) config (.genState 0 []) (some (.loc 1 0)) := by
  simp [genStartsInStore]

example : genStartsInStore (width := 32) config (.genState 0 [7]) (some (.word 0)) := by
  simp [genStartsInStore, config]

private def abstractHeap : List (HeapElement Nat (HeapTag × Nat)) :=
  [.dataElement [] 1 (.refTag, 7), .unused 1]

example : heapLookup 1 abstractHeap = none := by rfl

example : heapLookup 2 abstractHeap = some (.unused 1) := by rfl

example : heapSplit 1 abstractHeap = none := by rfl

example : heapSplit 2 abstractHeap = some ([.dataElement [] 1 (.refTag, 7)], [.unused 1]) := by rfl

example : rootsOk ([] : List (HeapAddress Bool)) abstractHeap := by
  simp [rootsOk]

example : isRef (.dataElement [] 1 (.refTag, 7) : HeapElement Nat (HeapTag × Nat)) := by
  simp [isRef, isMutTag]

example : gcKindInv config 0 0 0 (.genState 0 []) abstractHeap := by
  simp [gcKindInv, config]

example : word64Rep (width := 32) (α := Bool) 0x1122334455667788 =
    .dataElement [] 2 (.word64Tag, [.word 0x11223344, .word 0x55667788]) := by rfl

example : word64Rep (width := 64) (α := Bool) 0x1122334455667788 =
    .dataElement [] 1 (.word64Tag, [.word 0x1122334455667788]) := by rfl

example : getRefs (.block 3 0 [.refPtr true 4, .block 5 1 [.refPtr false 8]]) = [4, 8] := by
  simp [getRefs]

example : valueTimestamps (.block 3 0 [.refPtr true 4, .block 5 1 []]) = [3, 5] := by
  simp [valueTimestamps]

example : reachableRefs [.refPtr true 7] .ln 7 := by
  refine ⟨.refPtr true 7, 7, by simp, ?_, Relation.ReflTransGen.refl⟩
  simp [getRefs]

example : Misc.Multiword.n2mw (width := 8) 0x12345 = [0x45, 0x23, 0x01] := by
  simp [Misc.Multiword.n2mw]

example : smallnum (width := 32) (-2) = 0xFFFFFFF8 := by decide

example : allOnes (width := 8) 8 4 = 0xF0 := by decide

example : refPtrAnnot (width := 8) config
    (some (.mutBlock 1 false [42] 9 []) : Option (BvlSem.Ref Nat)) = .word 12 := by decide

#guard writeBytes (width := 32) [0x11, 0x22, 0x33] [0xAABBCCDD, 0x11223344] false =
    [0xAA332211, 0x11223344]

#guard writeBytes (width := 32) [0x11, 0x22, 0x33] [0xAABBCCDD, 0x11223344] true =
    [0x112233DD, 0x11223344]

#guard writeBytes (width := 64) [1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 0] false =
    [0x0807060504030201, 9]

example : ClockValueInv (width := 32) 0 config (.number (-2)) .ln
    (.data (.word (smallnum (-2))), HolFiniteMapExact.empty, HolFiniteMapExact.empty, []) := by
  exact .numberSmall 0 config (-2) .ln _ _ [] (by simp [smallInt])

example : ClockValueInv (width := 32) 0 config (.block 0 2 []) .ln
    (.data (.word (blockNil 2)), HolFiniteMapExact.empty, HolFiniteMapExact.empty, []) := by
  exact .blockNil 0 config 0 2 [] .ln _ _ [] rfl (by decide) rfl

example : valueInv (width := 32) config (.number (-2)) .ln
    (.data (.word (smallnum (-2))), HolFiniteMapExact.empty, HolFiniteMapExact.empty, []) := by
  apply (valueInv_number config (-2) .ln _ _ _ _).2
  simp [smallInt]

example : valueInv (width := 32) config (.block 0 2 []) .ln
    (.data (.word (blockNil 2)), HolFiniteMapExact.empty, HolFiniteMapExact.empty, []) := by
  exact (valueInv_emptyBlock config 0 2 .ln _ _ _ _).2 ⟨rfl, by decide, rfl⟩

private def timestampMap : HolFiniteMapExact Nat Nat := HolFiniteMapExact.empty.updateEq (3, 0)
private def blockAddress : HeapAddress (WordLocW 32) := .data (.word (smallnum 2))
private def blockHeap : ValueHeap 32 := [blockRep 1 [blockAddress]]

example : valueInv (width := 32) config (.block 3 1 [.number 2]) .ln
    (.pointer 0 (.word (ptrBits config 1 1)), HolFiniteMapExact.empty, timestampMap, blockHeap) := by
  apply (valueInv_block config 3 1 [.number 2] .ln _ _ _ _).2
  simp only [List.cons_ne_nil, ↓reduceIte]
  refine ⟨0, [blockAddress], ?_, ?_, rfl, ?_⟩
  · apply List.Forall₂.cons
    · apply (valueInv_number config 2 .ln _ _ _ _).2
      simp [smallInt, blockAddress]
    · exact .nil
  · rfl
  · rfl

private def referenceMap : HolFiniteMapExact Nat Nat := HolFiniteMapExact.empty.updateEq (4, 7)

example : valueInv (width := 32) config (.refPtr true 4) .ln
    (.pointer (holFapply referenceMap 4) (.word 0), referenceMap, HolFiniteMapExact.empty, []) := by
  apply (valueInv_refPtr_true config 4 .ln _ _ _ _).2
  refine ⟨⟨7, rfl⟩, ?_, ?_, rfl⟩ <;> simp

private def evaluatedRefs : Spt (BvlSem.Ref DataSem.Value) :=
  sptInsert 4 (.thunk .evaluated (.number 2)) .ln

example : valueInv (width := 32) config (.refPtr false 4) evaluatedRefs
    (.data (.word (smallnum 2)), HolFiniteMapExact.empty, HolFiniteMapExact.empty, []) := by
  apply (valueInv_refPtr config false 4 evaluatedRefs _ _ _ _).2
  right; right
  refine ⟨.number 2, ?_, rfl, rfl, ?_⟩
  · exact sptLookup_sptInsert_same 4 _ _
  · apply (valueInv_number config 2 evaluatedRefs _ _ _ _).2
    simp [smallInt]

example : ¬ bcRefInv (width := 32) config 0 .ln
    (HolFiniteMapExact.empty, HolFiniteMapExact.empty, [], false) := by
  simp [bcRefInv, HolFiniteMapExact.empty]

example : absMlInv (width := 32) config [] .ln ([], [], false, 0, 0, 0, .genState 0 []) 0 0 := by
  simp only [absMlInv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [rootsOk]
  · simp [heapOk, heapLength]
  · simp [gcKindInv, config]
  · simp [unusedSpaceInv, heapLength, dataUpTo, heapSplit]
  · refine ⟨HolFiniteMapExact.empty, HolFiniteMapExact.empty, ?_⟩
    simp [mapInjInto, mapDomain, HolFiniteMapExact.empty, beOk, config, blocksUnique, allValues, valueListValues]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
