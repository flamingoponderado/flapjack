import Flapjack.Compiler.Backend.StackLang
import Flapjack.HolRef

/-! Literal stack_remove store_init_def. Its twelve updates have distinct
monomorphic store-name keys; pattern matching is their extensional function
interpretation. Full initializer/compile routing remains on .18.5.15.6.6. -/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Original default zero-word function with its twelve store updates.
Temp keeps HOL's fixed five-bit carrier; only the output word is width-indexed. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "store_init_def"
  (words_as_type_indexed_bitvec)]
def storeInit {width : Nat} [NeZero width] (generateGc : Bool) (pointer : Nat) :
    StoreName → Sum (BitVec width) Nat
  | .currHeap | .globReal | .nextFree => .inr (pointer + 2)
  | .triggerGC => .inr (if generateGc then pointer + 2 else 2)
  | .endOfHeap | .otherHeap => .inr 2
  | .heapLength => .inr 5
  | .bitmapBase => .inr 3
  | .bitmapBuffer => .inr 4
  | .bitmapBufferEnd => .inr 6
  | .codeBuffer => .inr 7
  | .codeBufferEnd => .inr 1
  | _ => .inl 0

end Flapjack.Compiler.Backend.StackRemove
