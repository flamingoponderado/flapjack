import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyClock

/-! Local-environment preservation for data primitives. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Successful installation preserves the local environment. This helper
has no direct HOL counterpart. -/
theorem doInstall_locals {C F R : Type} (args : List Value) (state next : State C F) (value : Value)
    (run : doInstall (R := R) args state = .val (value, next)) : next.locals = state.locals := by
  simp only [doInstall] at run
  repeat' (split at run <;> try simp_all)
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals rfl

/-- Every successful primitive application preserves the local environment,
including installation. This is untagged auxiliary infrastructure. -/
theorem doApp_locals {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) : next.locals = state.locals := by
  cases op with
  | label label => exact (doApp_label_frame label args state next value run).1
  | ffi name => exact (doApp_ffi_frame name args state next value run).1
  | intOp op => exact (doApp_int_frame op args state next value run).1
  | wordOp op => exact (doApp_word_frame op args state next value run).1
  | blockOp op => exact (doApp_block_frame op args state next value run).1
  | globOp op => exact (doApp_global_frame op args state next value run).1
  | memOp op => exact (doApp_mem_frame op args state next value run).1
  | thunkOp op => exact (doApp_thunk_frame op args state next value run).1
  | install => exact doInstall_locals args { state with stackMax := none, stackFrameSizes := .ln } next value run

end Flapjack.Compiler.Backend.DataSem
