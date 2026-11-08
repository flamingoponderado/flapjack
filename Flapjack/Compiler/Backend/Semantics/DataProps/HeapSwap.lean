import Flapjack.Compiler.Backend.Semantics.DataSem.Heap

/-! Heap-size invariance for resource-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack.Compiler.Backend.DataSem

/-- Updating the safety flag does not change the measured heap size. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_heap_with_safe"]
theorem sizeOfHeap_with_safe {C F : Type} (state : State C F) (safe : Bool) :
    sizeOfHeap { state with safeForSpace := safe } = sizeOfHeap state := by
  rfl

end Flapjack.Compiler.Backend.DataProps
