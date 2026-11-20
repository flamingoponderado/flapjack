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

/-- A type error is never an FFI error. -/
private theorem typeError_ne_ffiError {C F : Type} (event : HolFinalEvent) :
    (.err (.abort .typeError) : Result (ClosSem.Value × ClosSem.State C F) ClosSem.Value) ≠
      .err (.abort (.ffiError event)) := by
  intro h
  cases h

/-- Only the FFI operation can report an FFI error. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_ffi_error_IMP"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_ffiError_imp {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (event : HolFinalEvent)
    (run : ClosSem.doApp op args state = .err (.abort (.ffiError event))) :
    ∃ i, op = .ffi i := by
  cases op with
  | ffi name => exact ⟨name, rfl⟩
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair => simp [ClosSem.doApp, h] at run
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair => simp [ClosSem.doApp, h] at run
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair => simp [ClosSem.doApp, h] at run
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair => simp [ClosSem.doApp, h] at run
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair => simp [ClosSem.doApp, h] at run
  | thunkOp operation =>
    cases operation with
    | forceThunk => simp [ClosSem.doApp] at run
    | allocThunk mode =>
      cases args with
      | nil => simp [ClosSem.doApp] at run
      | cons value rest =>
        cases rest with
        | nil =>
          simp only [ClosSem.doApp] at run
          split at run
          · exact absurd run (typeError_ne_ffiError event)
          · simp_all
        | cons other more => simp [ClosSem.doApp] at run
    | updateThunk mode =>
      cases args with
      | nil => simp [ClosSem.doApp] at run
      | cons first rest =>
        cases rest with
        | nil => simp [ClosSem.doApp] at run
        | cons second more =>
          cases first with
          | refPtr flag index =>
            cases flag with
            | false =>
              simp only [ClosSem.doApp] at run
              repeat' split at run
              all_goals first
                | exact absurd run (typeError_ne_ffiError event)
                | simp_all
            | true => simp [ClosSem.doApp] at run
          | number value => simp [ClosSem.doApp] at run
          | word64 word => simp [ClosSem.doApp] at run
          | block tag fields => simp [ClosSem.doApp] at run
          | byteVector bytes => simp [ClosSem.doApp] at run
          | closure location supplied env arity body => simp [ClosSem.doApp] at run
          | recclosure location supplied env functions index => simp [ClosSem.doApp] at run
  | label index => simp [ClosSem.doApp] at run
  | install => simp [ClosSem.doApp] at run

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
  cases op with
  | blockOp operation =>
    by_cases isEqual : operation = .equal
    · rw [isEqual] at notEqual
      exact absurd rfl notEqual
    · cases h : applyBlock operation args state with
      | none =>
        exact abort_of_err (C := C) (F := F) error .typeError
          (by simpa [ClosSem.doApp, h] using run)
      | some pair =>
        obtain ⟨value, next⟩ := pair
        simp [ClosSem.doApp, h] at run
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none =>
      exact abort_of_err (C := C) (F := F) error .typeError
        (by simpa [ClosSem.doApp, h] using run)
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, h] at run
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none =>
      exact abort_of_err (C := C) (F := F) error .typeError
        (by simpa [ClosSem.doApp, h] using run)
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, h] at run
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none =>
      exact abort_of_err (C := C) (F := F) error .typeError
        (by simpa [ClosSem.doApp, h] using run)
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, h] at run
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none =>
      exact abort_of_err (C := C) (F := F) error .typeError
        (by simpa [ClosSem.doApp, h] using run)
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, h] at run
  | ffi name =>
    unfold ClosSem.doApp at run
    repeat' split at run
    all_goals
      try exact abort_of_err (C := C) (F := F) error _ run
    all_goals simp_all
  | thunkOp operation =>
    unfold ClosSem.doApp at run
    repeat' split at run
    all_goals
      try exact abort_of_err (C := C) (F := F) error _ run
    all_goals simp_all
  | label index =>
    exact abort_of_err (C := C) (F := F) error .typeError
      (by simpa [ClosSem.doApp] using run)
  | install =>
    exact abort_of_err (C := C) (F := F) error .typeError
      (by simpa [ClosSem.doApp] using run)

end Flapjack.Compiler.Backend.ClosProps
