import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang

/-- Literal original reverse-ordered stack stores. The recursive continuation
executes before the head store. Source review found no production use in
word_to_stackScript beyond this definition; original wRegWrite1/wRegWrite2
retain their direct StackStore clauses. This native helper supports the full
original proof-side store/register continuation laws. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wStackStoreNative {width : Nat} [NeZero width] :
    List (Nat × Nat) → HolProg width → HolProg width
  | [], continuation => continuation
  | (register,slot) :: tail, continuation =>
      .seq (wStackStoreNative tail continuation) (.stackStore register slot)

end Flapjack.Compiler.Backend.WordToStack.Native
