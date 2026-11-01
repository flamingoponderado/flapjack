import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

/-! Local and control frames for thunk primitive application. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Successful thunk auxiliary operations preserve locals and control. This
is Flapjack infrastructure for the BVI-to-data simulation. -/
theorem doAppAux_thunk_frame {C F : Type} (op : AstHOL.ThunkOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.thunkOp op) args state = .val (value, next)) : SameLocalControl state next := by
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
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
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
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Thunk primitive dispatch preserves the same fields through its resource
bookkeeping. -/
theorem doApp_thunk_frame {C F : Type} (op : AstHOL.ThunkOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.thunkOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.thunkOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := doSpace_frame (.thunkOp op) args state accounted space
    have second := doAppAux_thunk_frame op args _ next value run
    have second' : SameLocalControl accounted next := by
      simpa [SameLocalControl, doStack, doLimSafe] using second
    exact first.trans second'

end Flapjack.Compiler.Backend.DataSem
