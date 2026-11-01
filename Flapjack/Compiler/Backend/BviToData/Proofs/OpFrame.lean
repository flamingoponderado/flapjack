import Flapjack.Compiler.Backend.BviToData.Assign
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame
import Mathlib.Tactic.CasesM

/-! Assignment local/control frames for the BVI-to-data operation proof. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Integer lowering emits a single assignment, including its two operand
reversal cases. -/
theorem iAssign_int_shape (op : ClosLang.IntOp) (dest : Nat) (operands live corr : List Nat) :
    ∃ actualOp actualOperands actualLive,
      iAssign dest (.intOp op) operands live corr = .assign dest (.intOp actualOp) actualOperands actualLive := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Successful generated integer assignments expose the actual operation,
operand read, live cut and primitive state; the primitive leaves the cut
environment, stack, handler and clock unchanged. -/
theorem evaluate_iAssign_int_frame {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∃ actualOp actualOperands actualLive args prepared applied value,
      iAssign dest (.intOp op) operands live corr = .assign dest (.intOp actualOp) actualOperands actualLive ∧
      DataSem.getVars actualOperands state.locals = some args ∧
      DataSem.cutStateOpt actualLive state = some prepared ∧
      DataSem.doApp (.intOp actualOp) args prepared = .val (value, applied) ∧
      next = DataSem.setVar dest value (DataSem.installSfs (.intOp actualOp) applied) ∧
      DataSem.SameLocalControl prepared applied := by
  obtain ⟨actualOp, actualOperands, actualLive, shape⟩ := iAssign_int_shape op dest operands live corr
  rw [shape] at run
  obtain ⟨args, prepared, applied, value, read, cut, app, output, frame⟩ :=
    DataSem.evaluate_assign_int_frame actualOp dest actualOperands actualLive state next run
  exact ⟨actualOp, actualOperands, actualLive, args, prepared, applied, value, shape, read, cut, app, output, frame⟩

/-- Successful compiled integer assignments preserve the source target's
control stack, handler, local-size metadata and clock. -/
theorem evaluate_iAssign_int_control {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.localsSize = state.localsSize ∧
      next.stackFrameSizes = state.stackFrameSizes ∧ next.clock = state.clock := by
  obtain ⟨actualOp, actualOperands, actualLive, args, prepared, applied, value, shape, read, cut, app, output, frame⟩ :=
    evaluate_iAssign_int_frame op dest operands live corr state next run
  have cutControl := DataSem.cutStateOpt_control actualLive state prepared cut
  rcases cutControl with ⟨stack1, handler1, size1, sizes1, clock1⟩
  rcases frame with ⟨_, stack2, handler2, size2, sizes2, clock2⟩
  rw [output]
  simp [DataSem.setVar, DataSem.installSfs, stack2, handler2, size2, sizes2, clock2,
    stack1, handler1, size1, sizes1, clock1]

/-- A successful generated integer assignment updates its destination in
the actual cut environment and preserves the control fields. -/
theorem evaluate_iAssign_int_locals {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∃ actualLive prepared value,
      DataSem.cutStateOpt actualLive state = some prepared ∧
      next.locals = sptInsert dest value prepared.locals ∧ DataSem.SameControl state next := by
  obtain ⟨actualOp, actualOperands, actualLive, shape⟩ := iAssign_int_shape op dest operands live corr
  rw [shape] at run
  obtain ⟨prepared, value, cut, locals, control⟩ :=
    DataSem.evaluate_assign_locals (.intOp actualOp) dest actualOperands actualLive state next
      (DataSem.doApp_int_frame actualOp) run
  exact ⟨actualLive, prepared, value, cut, locals, control⟩

/-- Word lowering emits an assignment, optionally preceded by make-space;
the byte comparison rewrites remain word assignments. -/
theorem iAssign_word_shape (op : ClosLang.WordOp) (dest : Nat) (operands live corr : List Nat) :
    (∃ actualOp actualOperands actualLive,
      iAssign dest (.wordOp op) operands live corr = .assign dest (.wordOp actualOp) actualOperands actualLive) ∨
    (∃ actualOp actualOperands actualLive amount roots,
      iAssign dest (.wordOp op) operands live corr =
        .seq (.makeSpace amount roots) (.assign dest (.wordOp actualOp) actualOperands actualLive)) := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  all_goals try (cases_type AstHOL.WordSize)
  all_goals try (cases_type AstHOL.Test)
  all_goals try (cases_type Flapjack.Opb)
  all_goals try (cases_type Bool)
  all_goals simp

/-- Successful generated word assignments preserve the target control
stack, handler, metadata and clock, including through the make-space prelude. -/
theorem evaluate_iAssign_word_control {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.wordOp op) operands live corr) state = (none, next)) :
    DataSem.SameControl state next := by
  rcases iAssign_word_shape op dest operands live corr with direct | spaced
  · obtain ⟨actualOp, actualOperands, actualLive, shape⟩ := direct
    rw [shape] at run
    exact DataSem.evaluate_assign_word_control actualOp dest actualOperands actualLive state next run
  · obtain ⟨actualOp, actualOperands, actualLive, amount, roots, shape⟩ := spaced
    rw [shape] at run
    exact DataSem.evaluate_seq_control (.makeSpace amount roots) (.assign dest (.wordOp actualOp) actualOperands actualLive)
      state next (DataSem.evaluate_makeSpace_control amount roots)
      (DataSem.evaluate_assign_word_control actualOp dest actualOperands actualLive) run

end Flapjack.Compiler.Backend.BviToData
