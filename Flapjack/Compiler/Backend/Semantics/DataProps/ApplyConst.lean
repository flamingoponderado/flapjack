module

public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveLocals

@[expose] public section
/-! Compiler-field preservation for data primitive applications. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL
/-- Successful space accounting preserves the compiler callback. -/
private theorem spaceCompile {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (run : doSpace op values state = some next) : next.compile = state.compile := by
  simp only [doSpace] at run
  repeat' (split at run <;> simp_all [consumeSpace])
  all_goals first | (cases run; rfl) | (obtain ⟨_, rfl⟩ := run; rfl)

/-- Successful primitive application preserves the source control and compiler fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_const"]
theorem doApp_const {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (run : doApp op values state = .val (value, next)) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.locals = state.locals ∧
      next.clock = state.clock ∧ next.compile = state.compile := by
  have control := doApp_control op values state next value run
  refine ⟨control.2.1, control.2.2.1, control.1, control.2.2.2.2, ?_⟩
  simp only [doApp] at run
  repeat' (split at run <;> try simp_all)
  all_goals try (have aux := doAppAux_const _ _ _ _ _ run; have space := spaceCompile _ _ _ _ (by assumption); simpa [doStack, doLimSafe] using aux.2.2.2.2.trans space)
  all_goals try (simp only [doInstall] at run)
  all_goals repeat' (split at run <;> try simp_all)
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals rfl
end Flapjack.Compiler.Backend.DataProps
