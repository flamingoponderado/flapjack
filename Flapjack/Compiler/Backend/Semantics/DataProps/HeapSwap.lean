import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

/-! Heap-size invariance for resource-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Updating the safety flag does not change the measured heap size. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_heap_with_safe"]
theorem sizeOfHeap_with_safe {C F : Type} (state : State C F) (safe : Bool) :
    sizeOfHeap { state with safeForSpace := safe } = sizeOfHeap state := by
  rfl

/-- A failed space reservation remains failed when only the safety and peak
observations change. This supports the HOL primitive error-swap proof. -/
theorem doSpace_none_safePeak {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat)
    (run : doSpace op values state = none) :
    doSpace op values { state with safeForSpace := safe, peakHeapLength := peak } = none := by
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length <;>
        simp_all [doSpace, consumeSpace]
  · simp [doSpace, reset] at run

/-- Installation errors are independent of safety and peak observations.
This is an auxiliary case for the HOL primitive error-swap theorem. -/
theorem doInstall_error_safePeak {C F R : Type} (values : List DataSem.Value)
    (state : State C F) (safe : Bool) (peak : Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult R)
    (run : doInstall (R := R) values state = .err error) :
    doInstall (R := R) values { state with safeForSpace := safe, peakHeapLength := peak } = .err error := by
  simp only [doInstall] at run ⊢
  repeat' (split at run <;> simp_all)
  all_goals repeat' (split <;> simp_all)

end Flapjack.Compiler.Backend.DataProps
