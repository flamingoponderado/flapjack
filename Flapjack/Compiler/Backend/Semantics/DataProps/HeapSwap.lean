import Aesop
import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

/-! Heap-size invariance for resource-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Updating the safety flag does not change the measured heap size. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_heap_with_safe"]
theorem sizeOfHeap_with_safe {C F : Type} (state : State C F) (safe : Bool) :
    sizeOfHeap { state with safeForSpace := safe } = sizeOfHeap state := by
  rfl

/-- The operation-space estimate ignores the resource observation fields. -/
theorem spaceConsumed_resource {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat) :
    spaceConsumed { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } op values =
      spaceConsumed state op values := by
  rfl

/-- Heap roots and limits ignore resource observation fields. -/
theorem sizeOfHeapArgs_resource {C F : Type} (values : List DataSem.Value)
    (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat) :
    sizeOfHeapArgs values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } =
      sizeOfHeapArgs values state := by
  rfl

/-- A failed space reservation remains failed when the three resource
observations change. This supports the HOL primitive error-swap proof. -/
theorem doSpace_none_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (run : doSpace op values state = none) :
    doSpace op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } = none := by
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length <;>
        simp_all [doSpace, consumeSpace]
  · simp [doSpace, reset] at run

/-- Successful space accounting changes only resource observations when the
input differs only in those observations. This supports the HOL swap proof. -/
theorem doSpace_some_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state next : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (run : doSpace op values state = some next) :
    ∃ safe' peak' mx',
      doSpace op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } =
        some { next with safeForSpace := safe', peakHeapLength := peak', stackMax := mx' } := by
  classical
  cases reset : DataLang.opSpaceReset op
  · by_cases zero : DataSpace.opSpaceReq op values.length = 0
    · simp [doSpace, reset, zero] at run
      subst next
      exact ⟨safe, peak, mx, by simp [doSpace, reset, zero]⟩
    · by_cases low : state.space < DataSpace.opSpaceReq op values.length
      · simp [doSpace, reset, zero, consumeSpace, low] at run
      · simp [doSpace, reset, zero, consumeSpace, low] at run
        subst next
        exact ⟨safe, peak, mx, by simp [doSpace, reset, zero, consumeSpace, low]⟩
  · simp [doSpace, reset] at run
    subst next
    refine ⟨safe && decide (noThunksInRefs state.refs ∧
      sizeOfHeapArgs values state + spaceConsumed state op values ≤ state.limits.heapLimit),
      max peak (sizeOfHeapArgs values state + spaceConsumed state op values), mx, ?_⟩
    simp [doSpace, reset, sizeOfHeapArgs_resource, spaceConsumed_resource]

/-- Limit and stack accounting preserve equality of all other state fields.
This supports the HOL primitive error-swap proof. -/
theorem doStack_doLimSafe_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat) :
    ∃ safe' peak' mx',
      doStack op values (doLimSafe { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } op values) =
        { doStack op values (doLimSafe state op values) with
          safeForSpace := safe', peakHeapLength := peak', stackMax := mx' } := by
  let result := doStack op values (doLimSafe { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } op values)
  refine ⟨result.safeForSpace, result.peakHeapLength, result.stackMax, ?_⟩
  rfl

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

/-- Non-FFI operation failure depends on neither safety, peak, nor stack
accounting. This supports the HOL primitive error-swap proof. -/
theorem applyNonFfi_none_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (run : applyNonFfi op values state = none) :
    applyNonFfi op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } = none := by
  simp only [applyNonFfi] at run ⊢
  all_goals repeat' (split <;> simp_all [withFreshTimestamp])
  all_goals aesop

/-- Auxiliary primitive errors are independent of the three resource
observations. This supports the HOL primitive error-swap proof. -/
theorem doAppAux_error_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doAppAux op values state = .err error) :
    doAppAux op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } = .err error := by
  simp only [doAppAux] at run ⊢
  all_goals repeat' (split <;> simp_all)
  all_goals cases original : applyNonFfi op values state <;> simp_all
  all_goals have changed := applyNonFfi_none_resource op values state safe peak mx original; simp_all

/-- The space-and-auxiliary path preserves errors under resource updates.
This assembles the corresponding cases of the HOL primitive swap proof. -/
theorem doApp_space_error_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : (match doSpace op values state with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next => doAppAux op values (doStack op values (doLimSafe next op values))) = .err error) :
    (match doSpace op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } with
      | none => Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError)
      | some next => doAppAux op values (doStack op values (doLimSafe next op values))) = .err error := by
  cases source : doSpace op values state with
  | none =>
    have target := doSpace_none_resource op values state safe peak mx source
    simpa [source, target] using run
  | some next =>
    have appRun : doAppAux op values (doStack op values (doLimSafe next op values)) = .err error := by
      simpa [source] using run
    obtain ⟨safe', peak', mx', target⟩ := doSpace_some_resource op values state next safe peak mx source
    obtain ⟨safe'', peak'', mx'', account⟩ := doStack_doLimSafe_resource op values next safe' peak' mx'
    have result := doAppAux_error_resource op values (doStack op values (doLimSafe next op values))
      safe'' peak'' mx'' error appRun
    simpa only [target, account] using result

/-- Primitive errors remain unchanged when resource observations change.
This strengthens the two HOL error-swap theorems for their shared proof. -/
theorem doApp_error_resource {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (safe : Bool) (peak : Nat) (mx : Option Nat)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (run : doApp op values state = .err error) :
    doApp op values { state with safeForSpace := safe, peakHeapLength := peak, stackMax := mx } = .err error := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    exact doInstall_error_safePeak values { state with stackMax := none, stackFrameSizes := .ln } safe peak error run
  | intOp intop =>
    have normal := doApp_space_error_resource (.intOp intop) values state safe peak mx error
    cases intop <;> simp only [doApp] at run ⊢
    all_goals first | exact normal run | exact run
  | label label =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.label label) values state safe peak mx error run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.ffi name) values state safe peak mx error run
  | wordOp wordop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.wordOp wordop) values state safe peak mx error run
  | blockOp blockop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.blockOp blockop) values state safe peak mx error run
  | globOp globop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.globOp globop) values state safe peak mx error run
  | memOp memop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.memOp memop) values state safe peak mx error run
  | thunkOp thunkop =>
    simp only [doApp] at run ⊢
    exact doApp_space_error_resource (.thunkOp thunkop) values state safe peak mx error run

/-- Updating safety and peak observations preserves primitive errors. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err_safe_peak_swap"]
theorem doApp_err_safePeakSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (safe : Bool) (peak : Nat) (run : doApp op values state = .err error) :
    doApp op values { state with safeForSpace := safe, peakHeapLength := peak } = .err error := by
  simpa using doApp_error_resource op values state safe peak state.stackMax error run

/-- Updating stack, safety and peak observations preserves primitive errors. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err_sm_safe_peak_swap"]
theorem doApp_err_stackSafePeakSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (mx : Option Nat) (safe : Bool) (peak : Nat) (run : doApp op values state = .err error) :
    doApp op values { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } = .err error :=
  doApp_error_resource op values state safe peak mx error run

end Flapjack.Compiler.Backend.DataProps
