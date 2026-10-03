import Flapjack.Compiler.Backend.StackRemove
import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimitsDouble

/-- Complete original numeric stack/heap limit calculation. HOL natural
subtraction is left-associated and truncated; division by two is total.
The actual reviewed store list supplies the reserved-word count. This proof
initializer helper has no word-valued argument or dimension assumption. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit''_def"]
def getStackHeapLimitDouble (h2 h3 h4 : Nat) : Nat × Nat :=
  (h4 - h3 - storeList.length, (h3 - h2) / 2)

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimitsDouble
