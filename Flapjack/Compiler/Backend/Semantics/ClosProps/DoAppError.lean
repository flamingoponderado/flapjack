module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyMemory
public import Flapjack.HolRef

@[expose] public section

/-! Error shapes of the closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL
open Flapjack.HolRef

namespace DoAppErrorPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DoAppErrorPort

/-- Only the FFI operation can report an FFI error. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_ffi_error_IMP"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_ffiError_imp {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (event : HolFinalEvent)
    (run : ClosSem.doApp op args state = .err (.abort (.ffiError event))) :
    ∃ i, op = .ffi i := by
  cases op with
  | ffi name => exact ⟨name, rfl⟩
  | _ =>
    simp only [ClosSem.doApp] at run
    repeat' split at run
    all_goals simp_all

/-- An abort error is an abort error. -/
private theorem abort_of_err {C F : Type} (error : ErrorResult ClosSem.Value) (reason : Abort)
    (run : (.err (.abort reason) : Result (ClosSem.Value × ClosSem.State C F) ClosSem.Value) =
      .err error) :
    ∃ a : Abort, error = .abort a := by
  injection run with same
  exact ⟨reason, same.symm⟩

/-- Every primitive failure other than the equality block test is an abort. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_err"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_err {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp op args state = .err error)
    (notEqual : op ≠ .blockOp .equal) :
    ∃ a : Abort, error = .abort a := by
  simp only [ClosSem.doApp] at run
  repeat' split at run
  all_goals
    try exact abort_of_err (C := C) (F := F) error _ run
  all_goals simp_all

end Flapjack.Compiler.Backend.ClosProps
