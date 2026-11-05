import Flapjack.Compiler.Backend.GcShared.Reachability

/-! Abstract collector reachability conditions. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Every data element in a heap is reachable from its roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_reachable_from_roots_def"]
def allReachableFromRoots {α β γ : Type} (roots : List (HeapAddress α)) (heap : List (HeapElement β γ)) : Prop :=
  ∀ ptr children len payload, heapLookup ptr heap = some (.dataElement children len payload) →
    reachableAddresses roots heap ptr

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
