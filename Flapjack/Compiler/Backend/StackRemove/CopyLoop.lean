import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Backend.StackLang.InstBuilders

/-! Literal stack_removeScript.sml:139–159 StoreConsts copy builders.
The default Pancake and assembly modes initializedRuntimeLab? executes these native
definitions through StackRemove.compileHOL. hex and sections modes retain the legacy
route; upstream StackAlloc replacement is a separate obligation.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Full original per-bitmap-word copy loop with exact register positions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyEach {width : Nat} [NeZero width] (temporary bitmap : Nat) : HolProg width :=
  whileProg .notEqual 1 (.imm 1)
    (listSeqHOL [loadInst temporary bitmap,
      addBytesInWordInst bitmap,
      .ite .test 1 (.imm 1) .skip (addInst temporary 3),
      rightShiftInst 1 1,
      storeInst temporary 2,
      addBytesInWordInst 2])

/-- Complete outer copy loop, retaining signed Less against zero and both
per-word copy calls; no memory, successful-run or output premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def copyLoop {width : Nat} [NeZero width] (temporary bitmap : Nat) : HolProg width :=
  listSeqHOL [loadInst 1 bitmap,
    addBytesInWordInst bitmap,
    whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap,
        loadInst 1 bitmap, addBytesInWordInst bitmap]),
    copyEach temporary bitmap]

end Flapjack.Compiler.Backend.StackRemove
