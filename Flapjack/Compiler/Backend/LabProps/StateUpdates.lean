module

public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Compiler.Backend.LabSem.Arithmetic
public import Flapjack.Compiler.Backend.LabSem.FpUpdates

@[expose] public section

/-!
# labProps state-update lemmas

The `labPropsScript.sml` `[simp]` facts about `labSem` state updates that leave
every non-register field alone. They live in this leaf beneath the
`LabProps` counterpart module.
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `with_same_clock` (`labPropsScript.sml:118`): rewriting a state's
    clock to its own value is the identity. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "with_same_clock"
  (words_as_type_indexed_bitvec)]
theorem with_same_clock {width : Nat} [NeZero width] {C F : Type} (s : State width C F) :
    ({ s with clock := s.clock } : State width C F) = s := by
  rfl

/-- Exact HOL `inc_pc_dec_clock` (`labPropsScript.sml:124`): advancing the
    program counter commutes with taking a clock tick. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "inc_pc_dec_clock"
  (words_as_type_indexed_bitvec)]
theorem inc_pc_dec_clock {width : Nat} [NeZero width] {C F : Type} (x : State width C F) :
    incPc (decClock x) = decClock (incPc x) := by
  rfl

/-- Exact HOL `binop_upd_consts` (`labPropsScript.sml:185`): a binary-operation
    register write leaves every other state component unchanged. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem binop_upd_consts {width : Nat} [NeZero width] {C F : Type} (a : Nat) (b : BinOp)
    (c d : BitVec width) (x : State width C F) :
    (binopUpd a b c d x).memDomain = x.memDomain ∧
    (binopUpd a b c d x).sharedMemDomain = x.sharedMemDomain ∧
    (binopUpd a b c d x).ptrReg = x.ptrReg ∧
    (binopUpd a b c d x).ptr2Reg = x.ptr2Reg ∧
    (binopUpd a b c d x).lenReg = x.lenReg ∧
    (binopUpd a b c d x).len2Reg = x.len2Reg ∧
    (binopUpd a b c d x).linkReg = x.linkReg ∧
    (binopUpd a b c d x).code = x.code ∧
    (binopUpd a b c d x).be = x.be ∧
    (binopUpd a b c d x).memory = x.memory ∧
    (binopUpd a b c d x).ioRegs = x.ioRegs ∧
    (binopUpd a b c d x).ioFpRegs = x.ioFpRegs ∧
    (binopUpd a b c d x).ccRegs = x.ccRegs ∧
    (binopUpd a b c d x).ccFpRegs = x.ccFpRegs ∧
    (binopUpd a b c d x).compile = x.compile ∧
    (binopUpd a b c d x).compileOracle = x.compileOracle ∧
    (binopUpd a b c d x).codeBuffer = x.codeBuffer ∧
    (binopUpd a b c d x).pc = x.pc ∧
    (binopUpd a b c d x).ffi = x.ffi := by
  cases b <;> simp [binopUpd, updReg]

end Flapjack.Compiler.Backend.LabSem
