import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

/-! Original HOL observations for pointer-tag and heap representation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

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

example : writeBytes (width := 32) [0x11, 0x22, 0x33] [0xAABBCCDD, 0x11223344] false =
    [0xAA332211, 0x11223344] := by native_decide

example : writeBytes (width := 32) [0x11, 0x22, 0x33] [0xAABBCCDD, 0x11223344] true =
    [0x112233DD, 0x11223344] := by native_decide

example : writeBytes (width := 64) [1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 0] false =
    [0x0807060504030201, 9] := by native_decide

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
