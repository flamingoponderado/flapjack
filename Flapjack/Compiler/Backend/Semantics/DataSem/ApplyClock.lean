import Flapjack.Compiler.Backend.Semantics.DataSem.BlockFrame
import Flapjack.Compiler.Backend.Semantics.DataSem.ThunkFrame
import Flapjack.Compiler.Backend.Semantics.DataSem.MemFrame

/-! Clock preservation for data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Successful code installation preserves the clock. This is Flapjack
infrastructure for the data evaluator's clock bound. -/
theorem doInstall_clock {C F R : Type} (args : List Value) (state next : State C F) (value : Value)
    (run : doInstall (R := R) args state = .val (value, next)) : next.clock = state.clock := by
  simp only [doInstall] at run
  repeat' (split at run <;> try simp_all)
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals rfl

/-- Successful primitive application preserves the clock exactly. This stronger
Flapjack lemma supports HOL's clock bound. -/
theorem doApp_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) : next.clock = state.clock := by
  cases op with
  | label label => exact (doApp_label_frame label args state next value run).2.2.2.2.2
  | ffi name => exact (doApp_ffi_frame name args state next value run).2.2.2.2.2
  | intOp op => exact (doApp_int_frame op args state next value run).2.2.2.2.2
  | wordOp op => exact (doApp_word_frame op args state next value run).2.2.2.2.2
  | blockOp op => exact (doApp_block_frame op args state next value run).2.2.2.2.2
  | globOp op => exact (doApp_global_frame op args state next value run).2.2.2.2.2
  | memOp op => exact (doApp_mem_frame op args state next value run).2.2.2.2.2
  | thunkOp op => exact (doApp_thunk_frame op args state next value run).2.2.2.2.2
  | install =>
    have aux := doInstall_clock args { state with stackMax := none, stackFrameSizes := .ln } next value run
    exact aux

/-- A successful primitive application cannot increase the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_app_clock"]
theorem doApp_clock_le {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) : next.clock ≤ state.clock :=
  Nat.le_of_eq (doApp_clock op args state next value run)

end Flapjack.Compiler.Backend.DataSem
