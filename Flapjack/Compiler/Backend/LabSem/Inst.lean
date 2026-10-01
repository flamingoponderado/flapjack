import Flapjack.Compiler.Backend.LabSem.Arithmetic
import Flapjack.Compiler.Backend.LabSem.Memory
import Flapjack.Compiler.Backend.LabSem.FpUpdates

/-! Literal native LabSem instruction dispatch and its full source frame
theorem. FP execution inherits the reviewed `reals_as_rational_cuts`
translation of `fpUpd` (docs/SOUNDNESS.md item 8); this module introduces no
real-number rendering of its own. Failed updates are preserved by dispatch.
-/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_inst_def"
  (words_as_type_indexed_bitvec)]
noncomputable def asmInst {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match instruction with
  | .skip => state
  | .const register value => updReg register (.word value) state
  | .arith operation => arithUpd operation state
  | .mem operator register address => memOp operator register address state
  | .fp operation => fpUpd operation state

/-- All thirteen source frame conjuncts, including unsuccessful transitions.
No assumption about operand validity, the failed flag, or a target execution
is required. The inherited FP translation is the same as that of `asmInst`. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_inst_consts"
  (words_as_type_indexed_bitvec)]
theorem asmInstConsts {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (asmInst instruction state).pc = state.pc ∧
    (asmInst instruction state).code = state.code ∧
    (asmInst instruction state).clock = state.clock ∧
    (asmInst instruction state).ffi = state.ffi ∧
    (asmInst instruction state).ioRegs = state.ioRegs ∧
    (asmInst instruction state).ioFpRegs = state.ioFpRegs ∧
    (asmInst instruction state).ccRegs = state.ccRegs ∧
    (asmInst instruction state).ccFpRegs = state.ccFpRegs ∧
    (asmInst instruction state).ptrReg = state.ptrReg ∧
    (asmInst instruction state).lenReg = state.lenReg ∧
    (asmInst instruction state).ptr2Reg = state.ptr2Reg ∧
    (asmInst instruction state).len2Reg = state.len2Reg ∧
    (asmInst instruction state).linkReg = state.linkReg := by
  cases instruction with
  | skip => simp [asmInst]
  | const register value => simp [asmInst, updReg]
  | arith operation =>
      cases operation <;> simp only [asmInst, arithUpd]
      all_goals repeat' first
        | simp_all [binopUpd, updReg, assertState]
        | split
  | mem operator register address =>
      cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
        memLoad32, memStore32, memLoadByte, memStoreByte]
      all_goals repeat' first
        | simp_all [updReg, updMem, assertState]
        | split
  | fp operation =>
      cases operation <;> simp only [asmInst, fpUpd]
      all_goals repeat' first
        | simp_all [updFpReg, updReg, assertState]
        | split

end Flapjack.Compiler.Backend.LabSem
