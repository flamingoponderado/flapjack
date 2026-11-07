import Flapjack.Compiler.Backend.Semantics.DataProps.MemResources

/-! Resource observations of source thunk operations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Successful thunk auxiliary operations preserve resource observations. -/
theorem doAppAux_thunk_resource_frame {C F : Type} (op : AstHOL.ThunkOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.thunkOp op) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases op with
  | forceThunk => cases args <;> simp [doAppAux, applyNonFfi] at run
  | allocThunk mode =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        by_cases bad : badThunkUpdate mode first state.refs
        · simp [doAppAux, applyNonFfi, bad] at run
        · simp [doAppAux, applyNonFfi, bad] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [BackendProps.optionLe_refl]
  | updateThunk mode =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> simp [doAppAux, applyNonFfi] at run
          case refPtr flag ptr =>
            cases flag with
            | true => simp at run
            | false =>
              by_cases bad : badThunkUpdate mode second state.refs
              · simp [bad] at run
              · simp [bad] at run
                cases found : sptLookup ptr state.refs with
                | none => simp [found] at run
                | some entry =>
                  cases entry <;> simp [found] at run
                  case thunk oldMode oldValue =>
                    cases oldMode <;> simp at run
                    obtain ⟨rfl, rfl⟩ := run
                    simp [BackendProps.optionLe_refl]

/-- Thunk operations satisfy resource monotonicity through the production dispatcher. -/
theorem doApp_thunk_resource_frame {C F : Type} (op : AstHOL.ThunkOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.thunkOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.thunkOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact accounted_resource_frame _ args state accounted next value space run
      (fun before after v h => doAppAux_thunk_resource_frame op args before after v h)

end Flapjack.Compiler.Backend.DataSem
