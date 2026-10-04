import Flapjack.Compiler.Backend.StackRemove.InitCode

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Original three initialization sections, including the tail call and both
word-sized halt results. This definition does not specialize the source start
label, heap bound, register indices, or positive word width. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def initStubs {width : Nat} [NeZero width] (generateGc : Bool)
    (maximumHeap pointer start : Nat) : List (Nat × HolProg width) :=
  [(0, .seq (initCode generateGc maximumHeap pointer) (.call none (.inl start) none)),
   (1, haltInst 0), (2, haltInst 2)]

end Flapjack.Compiler.Backend.StackRemove
