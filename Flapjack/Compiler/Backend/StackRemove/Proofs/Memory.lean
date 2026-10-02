import Flapjack.Misc.SetSep

/-! Full generic heap assertion from stack_removeProofScript.sml.
Address and stored-value types are independent, as in the original declaration;
sets are predicates and no finite-domain or machine-word restriction is added.
-/

namespace Flapjack.Compiler.Backend.StackRemove

/-- The supplied heap is exactly the function graph restricted to its domain.
This is a whole-heap equality, not just inclusion or pointwise read agreement. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_def"]
def memoryHOL {α β : Type} (memory : α → β) (domain : α → Prop) :
    ((α × β) → Prop) → Prop :=
  fun heap => heap = Flapjack.SetSep.fun2Set (memory, domain)

end Flapjack.Compiler.Backend.StackRemove
