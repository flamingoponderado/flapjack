import Flapjack.Compiler.Backend.StackRemove.InitMemory
import Flapjack.Compiler.Backend.StackRemove.StoreInit
import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Complete original heap/store/stack initializer. The maximum heap check
uses the unsigned byte-stride word before constructing its word-sized limit.
All register aliases, natural register indices, and word dimensions remain
unrestricted apart from the standard positive-width word translation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def initCode {width : Nat} [NeZero width] (generateGc : Bool)
    (maximumHeap pointer : Nat) : HolProg width :=
  let maximumHeapWord :=
    if maximumHeap * (bytesInWord width).toNat < 2 ^ width then
      BitVec.ofNat width maximumHeap * bytesInWord width
    else (0 : BitVec width) - 1
  listSeqHOL [
    moveHOL 0 4, subInst 0 2,
    rightShiftInst 0 (1 + wordShiftAmount width),
    leftShiftInst 0 (wordShiftAmount width), addInst 0 2,
    constInst 5 (BitVec.ofNat width maxStackAlloc * bytesInWord width),
    addInst 2 5, subInst 4 5,
    .ite .lower 3 (.reg 2) (moveHOL 3 0)
      (.ite .lower 4 (.reg 3) (moveHOL 3 0) .skip),
    constInst 0 (BitVec.ofNat width maxStackAlloc * bytesInWord width),
    subInst 2 0, addInst 4 0, moveHOL 0 3, subInst 0 2,
    constInst 5 maximumHeapWord,
    .ite .lower 5 (.reg 0) (.seq (moveHOL 3 2) (addInst 3 5)) .skip,
    subInst 3 2, rightShiftInst 3 (wordShiftAmount width + 1),
    leftShiftInst 3 (wordShiftAmount width + 1), addInst 3 2,
    moveHOL 5 3, subInst 5 2, rightShiftInst 5 1,
    moveHOL (pointer + 2) 2, addInst 2 5,
    moveHOL pointer 4, moveHOL (pointer + 1) 3,
    loadInst 3 (pointer + 2), rightShiftInst 3 (wordShiftAmount width),
    moveHOL 0 (pointer + 2), addBytesInWordInst 0,
    loadInst 4 0, addBytesInWordInst 0, loadInst 6 0,
    addBytesInWordInst 0, loadInst 7 0, addBytesInWordInst 0,
    loadInst 1 0,
    initMemory pointer (storeList.reverse.map (storeInit generateGc pointer)),
    .locValue 0 1 0]

end Flapjack.Compiler.Backend.StackRemove
