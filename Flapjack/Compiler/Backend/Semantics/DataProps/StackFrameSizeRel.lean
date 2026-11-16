module

public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame
public import Batteries.Data.List.Basic

@[expose] public section

/-! Stack-frame size agreement across primitive applications. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Two stack frames agree up to their frame size: the environment map must be
equal, and an exception frame's handler must be equal too; the frame-size field
itself is ignored. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "stack_frame_size_rel_def"]
def stackFrameSizeRel : Stack → Stack → Prop
  | .env _ locals, .env _ otherLocals => locals = otherLocals
  | .exc _ locals handler, .exc _ otherLocals otherHandler =>
      locals = otherLocals ∧ handler = otherHandler
  | _, _ => False

/-- A successful primitive application leaves the stack untouched. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_stack_eq"]
theorem doApp_stack_eq {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    next.stack = state.stack := by
  have frame := (doApp_controlFrame op args state next value run).2.1
  simpa using frame

/-- Frame-size agreement with a fixed frame list survives a primitive application. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_stack_frame_size_rel"]
theorem doApp_stackFrameSizeRel {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (frames : List Stack)
    (premises : doApp op args state = .val (value, next) ∧
      List.Forall₂ stackFrameSizeRel state.stack frames) :
    List.Forall₂ stackFrameSizeRel next.stack frames := by
  obtain ⟨run, related⟩ := premises
  rw [doApp_stack_eq op args state next value run]
  exact related

end Flapjack.Compiler.Backend.DataSem
