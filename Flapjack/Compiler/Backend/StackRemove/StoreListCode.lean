import Flapjack.Compiler.Backend.StackLang.Overloads

/-! Literal stack_removeScript.sml:231–241 initialization list compiler.
The full original initialization/compile route remains tracked on
flapjack-pxn.18.5.15.6.6; this definition alone does not replace that route. -/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Compile each word or register store initializer in its original order.
HOL's sum and list carriers remain Lean Sum and List, with no bounds premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def storeListCode {width : Nat} [NeZero width] (address temporary : Nat) :
    List (Sum (BitVec width) Nat) → HolProg width
  | [] => .skip
  | .inl value :: rest =>
      .seq (listSeqHOL [.inst (.const temporary value),
        .inst (.mem .store temporary (.addr address 0)), addBytesInWordInst address])
        (storeListCode address temporary rest)
  | .inr register :: rest =>
      .seq (listSeqHOL [.inst (.mem .store register (.addr address 0)),
        addBytesInWordInst address]) (storeListCode address temporary rest)

end Flapjack.Compiler.Backend.StackRemove
