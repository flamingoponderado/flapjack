import Flapjack.Compiler.Backend.BviToData.Assign
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

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

end Flapjack.Compiler.Backend.BviToData
