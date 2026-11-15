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

/-- Exact HOL `read_reg_inc_pc` (`labPropsScript.sml:112`): advancing the
    program counter leaves the register file alone. HOL's `read_reg` is the
    overload `λr s. s.regs r`, so the equation is stated on `.regs`. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_inc_pc"
  (words_as_type_indexed_bitvec)]
theorem read_reg_inc_pc {width : Nat} [NeZero width] {C F : Type} (r : Nat)
    (x : State width C F) :
    (incPc x).regs r = x.regs r := by
  rfl

/-- Exact HOL `update_simps` (`labPropsScript.sml:130`): the 51-conjunct
    `[simp]` conjunction of `upd_pc`, `dec_clock` and `inc_pc` projections, in
    HOL's order and with HOL's repeated `ffi` conjuncts retained. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "update_simps"
  (words_as_type_indexed_bitvec)]
theorem update_simps {width : Nat} [NeZero width] {C F : Type} (x : Nat)
    (s : State width C F) :
    ((updPc x s).ffi = s.ffi) ∧
    ((decClock s).ffi = s.ffi) ∧
    ((updPc x s).pc = x) ∧
    ((decClock s).pc = s.pc) ∧
    ((updPc x s).clock = s.clock) ∧
    ((updPc x s).ffi = s.ffi) ∧
    ((decClock s).clock = s.clock - 1) ∧
    ((decClock s).lenReg = s.lenReg) ∧
    ((decClock s).len2Reg = s.len2Reg) ∧
    ((decClock s).linkReg = s.linkReg) ∧
    ((decClock s).code = s.code) ∧
    ((decClock s).ptrReg = s.ptrReg) ∧
    ((decClock s).ptr2Reg = s.ptr2Reg) ∧
    ((decClock s).ffi = s.ffi) ∧
    ((updPc x s).lenReg = s.lenReg) ∧
    ((updPc x s).len2Reg = s.len2Reg) ∧
    ((updPc x s).linkReg = s.linkReg) ∧
    ((updPc x s).code = s.code) ∧
    ((updPc x s).ptrReg = s.ptrReg) ∧
    ((updPc x s).ptr2Reg = s.ptr2Reg) ∧
    ((updPc x s).memDomain = s.memDomain) ∧
    ((updPc x s).sharedMemDomain = s.sharedMemDomain) ∧
    ((updPc x s).failed = s.failed) ∧
    ((updPc x s).be = s.be) ∧
    ((updPc x s).memory = s.memory) ∧
    ((updPc x s).regs = s.regs) ∧
    ((updPc x s).fpRegs = s.fpRegs) ∧
    ((updPc x s).ffi = s.ffi) ∧
    ((incPc s).ptrReg = s.ptrReg) ∧
    ((incPc s).ptr2Reg = s.ptr2Reg) ∧
    ((incPc s).lenReg = s.lenReg) ∧
    ((incPc s).len2Reg = s.len2Reg) ∧
    ((incPc s).linkReg = s.linkReg) ∧
    ((incPc s).code = s.code) ∧
    ((incPc s).be = s.be) ∧
    ((incPc s).failed = s.failed) ∧
    ((incPc s).memDomain = s.memDomain) ∧
    ((incPc s).sharedMemDomain = s.sharedMemDomain) ∧
    ((incPc s).ioRegs = s.ioRegs) ∧
    ((incPc s).ioFpRegs = s.ioFpRegs) ∧
    ((incPc s).ccRegs = s.ccRegs) ∧
    ((incPc s).ccFpRegs = s.ccFpRegs) ∧
    ((incPc s).compile = s.compile) ∧
    ((incPc s).compileOracle = s.compileOracle) ∧
    ((incPc s).codeBuffer = s.codeBuffer) ∧
    ((incPc s).memory = s.memory) ∧
    ((incPc s).regs = s.regs) ∧
    ((incPc s).fpRegs = s.fpRegs) ∧
    ((incPc s).pc = s.pc + 1) ∧
    ((incPc s).ffi = s.ffi) := by
  simp [updPc, decClock, incPc]

end Flapjack.Compiler.Backend.LabSem
