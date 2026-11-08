import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields

/-! HOL field-commutation properties of auxiliary primitive application. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Successful auxiliary application preserves the source control and compiler fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_const"]
theorem doAppAux_const {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (run : doAppAux op values state = .val (value, next)) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.locals = state.locals ∧
      next.clock = state.clock ∧ next.compile = state.compile := by
  obtain ⟨stack, _, _, _, locals, _, handler, clock, _, compiler⟩ :=
    doAppAux_fieldFrame op values state next value run
  exact ⟨stack, handler, locals, clock, compiler⟩

/-- Auxiliary application commutes with replacing locals. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_with_locals"]
theorem doAppAux_withLocals {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (locals : Spt DataSem.Value) :
    doAppAux op values { state with locals := locals } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (value, next) => (value, { next with locals := locals })) id (doAppAux op values state) := by
  have changed := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength locals state.space state.handler state.clock state.stackFrameSizes state.compile
  cases run : doAppAux op values state with
  | err error => simpa [run, Flapjack.SemanticPrimitivesProps.mapResult,
      Flapjack.SemanticPrimitivesProps.mapErrorResult] using changed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doAppAux_fieldFrame op values state next value run
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
      frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.2.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1,
      frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using changed

/-- Auxiliary application commutes with replacing reserved space. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_with_space"]
theorem doAppAux_withSpace {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux op values { state with space := space } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (value, next) => (value, { next with space := space })) id (doAppAux op values state) := by
  have changed := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength state.locals space state.handler state.clock state.stackFrameSizes state.compile
  cases run : doAppAux op values state with
  | err error => simpa [run, Flapjack.SemanticPrimitivesProps.mapResult,
      Flapjack.SemanticPrimitivesProps.mapErrorResult] using changed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doAppAux_fieldFrame op values state next value run
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
      frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1,
      frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using changed

end Flapjack.Compiler.Backend.DataProps
