module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

@[expose] public section

/-! Error classification for data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL
/-- An auxiliary primitive error is a type error or an FFI final event. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_err"]
theorem doAppAux_err {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : ErrorResult DataSem.Value)
    (run : doAppAux op values state = .err error) :
    error = .abort .typeError ∨ ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  simp only [doAppAux] at run
  repeat' (split at run <;> try simp_all)
  all_goals right
  all_goals cases run
  all_goals exact ⟨_, rfl⟩
/-- A primitive error is a type error or an FFI final event. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_err"]
theorem doApp_err {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (error : ErrorResult DataSem.Value)
    (run : doApp op values state = .err error) :
    error = .abort .typeError ∨ ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  simp only [doApp] at run
  repeat' (split at run <;> try simp_all)
  all_goals try (have h := doAppAux_err _ _ _ _ run; simpa only [exists_and_left, exists_and_right] using h)
  all_goals try (simp only [doInstall] at run)
  all_goals repeat' (split at run <;> try simp_all)
end Flapjack.Compiler.Backend.DataProps
