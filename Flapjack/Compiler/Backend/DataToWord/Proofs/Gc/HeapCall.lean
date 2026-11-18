module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Heap roots across the temporary source call environment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A call with no arguments keeps the heap roots of the saved environment. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_heap_call_push_env"]
theorem sizeOfHeapCallPushEnv {C F : Type} (names : NumSet) (source : DataSem.State C F)
    (env : Spt DataSem.Value) (size : Option Nat)
    (_cut : DataSem.cutEnv names source.locals = some env) :
    DataSem.sizeOfHeap (DataSem.callEnv [] size (DataSem.pushEnv env false source)) =
      DataSem.sizeOfHeap { source with locals := env } := by
  simp [DataSem.sizeOfHeap, DataSem.stackToValues, DataSem.callEnv, DataSem.pushEnv,
    DataSem.extractStack, sptToList, sptToListA, sptFromList]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
