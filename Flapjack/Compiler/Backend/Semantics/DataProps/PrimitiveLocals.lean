import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyClock

/-! Local-environment preservation for data primitives. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Installation preserves local and control fields, including the frame
size and clock. This auxiliary theorem has no direct HOL declaration. -/
theorem doInstall_localControl {C F R : Type} (args : List Value) (state next : State C F) (value : Value)
    (run : doInstall (R := R) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doInstall] at run
  repeat' (split at run <;> try simp_all)
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All successful primitive operations preserve locals, stack, handler,
local frame size and clock. Installation intentionally resets frame-size
metadata, so this theorem excludes that field. -/
theorem doApp_control {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    next.locals = state.locals ∧ next.stack = state.stack ∧ next.handler = state.handler ∧
      next.localsSize = state.localsSize ∧ next.clock = state.clock := by
  have frame : SameLocalControl { state with stackFrameSizes := (if op == .install then .ln else state.stackFrameSizes) } next := by
    cases op with
    | label label => exact doApp_label_frame label args state next value run
    | ffi name => exact doApp_ffi_frame name args state next value run
    | intOp op => exact doApp_int_frame op args state next value run
    | wordOp op => exact doApp_word_frame op args state next value run
    | blockOp op => exact doApp_block_frame op args state next value run
    | globOp op => exact doApp_global_frame op args state next value run
    | memOp op => exact doApp_mem_frame op args state next value run
    | thunkOp op => exact doApp_thunk_frame op args state next value run
    | install => exact doInstall_localControl args { state with stackMax := none, stackFrameSizes := .ln } next value run
  exact ⟨frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.2⟩

end Flapjack.Compiler.Backend.DataSem
