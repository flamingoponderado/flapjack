import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapReads

namespace Flapjack.Compiler.Backend.StackRemove.StoreHeapWrites
open Flapjack

/-- Full original local heap regrouping, on arbitrary predicate heaps. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "assoc_lem"]
theorem assocLem {α : Type} (A B C : (α → Prop) → Prop) :
    SetSep.star (SetSep.star A B) C = SetSep.star (SetSep.star B C) A := by
  rw [← SetSep.starAssoc, SetSep.starComm A (SetSep.star B C)]

end Flapjack.Compiler.Backend.StackRemove.StoreHeapWrites
