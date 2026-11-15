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

/-- Exact HOL `arith_upd_consts` (`labPropsScript.sml:209`): the integer
    arithmetic instruction leaves every state component except the registers
    and the sticky failure flag unchanged. HOL's 19 conjuncts are kept as one
    conjunction in source field order. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem arith_upd_consts {width : Nat} [NeZero width] {C F : Type} (a : HolArith width)
    (x : State width C F) :
    (arithUpd a x).memDomain = x.memDomain ∧
    (arithUpd a x).sharedMemDomain = x.sharedMemDomain ∧
    (arithUpd a x).ptrReg = x.ptrReg ∧
    (arithUpd a x).ptr2Reg = x.ptr2Reg ∧
    (arithUpd a x).lenReg = x.lenReg ∧
    (arithUpd a x).len2Reg = x.len2Reg ∧
    (arithUpd a x).linkReg = x.linkReg ∧
    (arithUpd a x).code = x.code ∧
    (arithUpd a x).be = x.be ∧
    (arithUpd a x).memory = x.memory ∧
    (arithUpd a x).ioRegs = x.ioRegs ∧
    (arithUpd a x).ioFpRegs = x.ioFpRegs ∧
    (arithUpd a x).ccRegs = x.ccRegs ∧
    (arithUpd a x).ccFpRegs = x.ccFpRegs ∧
    (arithUpd a x).compile = x.compile ∧
    (arithUpd a x).compileOracle = x.compileOracle ∧
    (arithUpd a x).codeBuffer = x.codeBuffer ∧
    (arithUpd a x).pc = x.pc ∧
    (arithUpd a x).ffi = x.ffi := by
  cases a
  case binop op r1 r2 operand =>
    simp only [arithUpd]
    split
    · simp [updReg, binopUpd]
    · split
      · split
        · simp [updReg]
        · simp [assertState]
      · split
        · simp [updReg]
        · simp [assertState]
  case shift op r1 r2 operand =>
    simp only [arithUpd]
    split
    · simp [updReg, assertState]
    · simp [assertState]
  case div r1 r2 r3 =>
    simp only [arithUpd]
    split
    · simp [updReg, assertState]
    · simp [assertState]
  case addCarry r1 r2 r3 r4 =>
    simp only [arithUpd]
    split
    · simp [updReg]
    · simp [assertState]
  case longMul r1 r2 r3 r4 =>
    simp only [arithUpd]
    split
    · simp [updReg]
    · simp [assertState]
  case longDiv r1 r2 r3 r4 r5 =>
    simp only [arithUpd]
    split
    · simp [updReg, assertState]
    · simp [assertState]
  case addOverflow r1 r2 r3 r4 =>
    simp only [arithUpd]
    split
    · simp [updReg]
    · simp [assertState]
  case subOverflow r1 r2 r3 r4 =>
    simp only [arithUpd]
    split
    · simp [updReg]
    · simp [assertState]

/-- Exact HOL `fp_upd_consts` (`labPropsScript.sml:234`): the floating-point
    instruction leaves every state component except the register files and the
    sticky failure flag unchanged. HOL's field order (which differs from
    `arith_upd_consts`) is preserved. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem fp_upd_consts {width : Nat} [NeZero width] {C F : Type} (f : HolFp)
    (x : State width C F) :
    (fpUpd f x).memDomain = x.memDomain ∧
    (fpUpd f x).sharedMemDomain = x.sharedMemDomain ∧
    (fpUpd f x).ptrReg = x.ptrReg ∧
    (fpUpd f x).lenReg = x.lenReg ∧
    (fpUpd f x).ptr2Reg = x.ptr2Reg ∧
    (fpUpd f x).len2Reg = x.len2Reg ∧
    (fpUpd f x).linkReg = x.linkReg ∧
    (fpUpd f x).code = x.code ∧
    (fpUpd f x).ccRegs = x.ccRegs ∧
    (fpUpd f x).ccFpRegs = x.ccFpRegs ∧
    (fpUpd f x).codeBuffer = x.codeBuffer ∧
    (fpUpd f x).compile = x.compile ∧
    (fpUpd f x).compileOracle = x.compileOracle ∧
    (fpUpd f x).be = x.be ∧
    (fpUpd f x).memory = x.memory ∧
    (fpUpd f x).ioRegs = x.ioRegs ∧
    (fpUpd f x).ioFpRegs = x.ioFpRegs ∧
    (fpUpd f x).pc = x.pc ∧
    (fpUpd f x).ffi = x.ffi := by
  cases f
  case fpLess r d1 d2 =>
    simp [fpUpd, updReg]
  case fpLessEqual r d1 d2 =>
    simp [fpUpd, updReg]
  case fpEqual r d1 d2 =>
    simp [fpUpd, updReg]
  case fpMov d1 d2 =>
    simp [fpUpd, updFpReg]
  case fpAbs d1 d2 =>
    simp [fpUpd, updFpReg]
  case fpNeg d1 d2 =>
    simp [fpUpd, updFpReg]
  case fpSqrt d1 d2 =>
    simp [fpUpd, updFpReg]
  case fpAdd d1 d2 d3 =>
    simp [fpUpd, updFpReg]
  case fpSub d1 d2 d3 =>
    simp [fpUpd, updFpReg]
  case fpMul d1 d2 d3 =>
    simp [fpUpd, updFpReg]
  case fpDiv d1 d2 d3 =>
    simp [fpUpd, updFpReg]
  case fpFma d1 d2 d3 =>
    simp [fpUpd, updFpReg]
  case fpMovToReg r1 r2 d =>
    simp only [fpUpd]
    split
    · simp [updReg]
    · simp [updReg]
  case fpMovFromReg d r1 r2 =>
    simp only [fpUpd]
    split
    · split
      · simp [updFpReg]
      · simp [assertState]
    · split
      · simp [updFpReg]
      · simp [assertState]
  case fpToInt d1 d2 =>
    simp only [fpUpd]
    split
    · simp [assertState]
    · split
      · simp [updFpReg, assertState]
      · split
        · simp [updFpReg, assertState]
        · simp [updFpReg, assertState]
  case fpFromInt d1 d2 =>
    simp [fpUpd, updFpReg]

end Flapjack.Compiler.Backend.LabSem
