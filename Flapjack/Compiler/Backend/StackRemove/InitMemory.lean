import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Backend.StackRemove.StoreListCode

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Literal five-instruction-list initializer from HOL. The stack pointer is
decremented by one word, the terminal stack slot is zeroed, then all initial
stores are emitted through the original list compiler. Register aliases and
arbitrary natural register indices are retained without extra premises. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "init_memory_def"
  (words_as_type_indexed_bitvec)]
def initMemory {width : Nat} [NeZero width] (pointer : Nat)
    (values : List (Sum (BitVec width) Nat)) : HolProg width :=
  listSeqHOL [constInst 0 (bytesInWord width), subInst pointer 0,
    constInst 0 0, storeInst 0 pointer, storeListCode (pointer + 1) 0 values]

end Flapjack.Compiler.Backend.StackRemove
