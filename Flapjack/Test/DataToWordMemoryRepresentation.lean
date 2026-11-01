import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
