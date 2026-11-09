import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Address
import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Logical
import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Shift

/-!
# Composition of the ARMv8 encoder bridge

The computable `Arm8.arm8Enc` lowers a `HolAsm 64` to a list of computable
`Insn` and concatenates their bytes; the L3 `arm8Enc` lowers it to L3
`instruction` forms and concatenates their `Encode` bytes.  The per-instruction
lemmas in `L3/Executable/` relate the two encodings of a single instruction
form.  This module lifts them to whole `HolAsm` values, one lemma per
`arm8_ast` family.

No HOL claim is introduced: each lemma relates two Lean renderings of the same
lowering and encoding.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- A truncated `Nat` field of a `MoveWide` immediate, moved onto the `BitVec 16`
carrier; the computable lowering keeps the `Nat` modulus. -/
theorem ofNat16_mod (v : Nat) :
    BitVec.ofNat 16 (v % 65536) = BitVec.ofNat 16 v := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- A truncated `Nat` field of a `MoveWide` half-word index, moved onto the
`BitVec 2` carrier. -/
theorem ofNat2_mod (v : Nat) : BitVec.ofNat 2 (v % 4) = BitVec.ofNat 2 v := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- A truncated `Nat` register field, moved onto the `BitVec 5` carrier. -/
theorem ofNat5_mod (v : Nat) : BitVec.ofNat 5 (v % 32) = BitVec.ofNat 5 v := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- `.jump` lowers to the same branch-immediate form. -/
theorem arm8Enc_jump_eq (target : BitVec 64) :
    Arm8.arm8Enc (.jump target) = arm8Enc (.jump target) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, encodeBytes_branchImmediate]
  simp

/-- `.call` lowers to the same branch-immediate form. -/
theorem arm8Enc_call_eq (target : BitVec 64) :
    Arm8.arm8Enc (.call target) = arm8Enc (.call target) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, encodeBytes_branchImmediate]
  simp

/-- `.jumpReg` lowers to the same branch-register form. -/
theorem arm8Enc_jumpReg_eq (target : Nat) :
    Arm8.arm8Enc (.jumpReg target) = arm8Enc (.jumpReg target) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, encodeBytes_branchRegister]
  simp

/-- `.loc` lowers to the same address/move-wide sequence, in range and out. -/
theorem arm8Enc_loc_eq (register : Nat) (offset : BitVec 64) :
    Arm8.arm8Enc (.loc register offset) = arm8Enc (.loc register offset) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast, temp]
  by_cases hf : fitsSigned 20 offset = true
  · have hl3 : arm8LocInRange offset = true :=
      (fitsSigned20_iff_arm8LocInRange offset).mp hf
    simp only [hf, hl3, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_address]
    rfl
  · have hf' : fitsSigned 20 offset = false := by
      cases h : fitsSigned 20 offset
      · rfl
      · exact absurd h hf
    have hl3 : arm8LocInRange offset = false := by
      cases h : arm8LocInRange offset
      · rfl
      · exact absurd ((fitsSigned20_iff_arm8LocInRange offset).mpr h) hf
    simp only [hf, Bool.false_eq_true, if_false, hl3, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, encodeBytes_address,
      encodeBytes_moveWide, encodeBytes_addSubShiftedRegister, ofNat16_mod]
    simp

/-- `.jumpCmp` with a register operand lowers to the same compare + branch pair. -/
theorem arm8Enc_jumpCmp_reg_eq (operator : Cmp) (source right : Nat) (target : BitVec 64) :
    Arm8.arm8Enc (.jumpCmp operator source (.reg right) target) =
      arm8Enc (.jumpCmp operator source (.reg right) target) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast]
  by_cases ht : isTest operator = true
  · simp only [if_pos ht, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_logicalShiftedRegister .and .LogicalOp_AND false true .lsl 0 right source 31 3
        rfl (by decide) (by decide), encodeBytes_branchConditional]
    rw [← arm8CmpCond_eq operator]
    simp
  · simp only [if_neg ht, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubShiftedRegister, encodeBytes_branchConditional]
    rw [← arm8CmpCond_eq operator]
    simp

/-- `.jumpCmp` with an immediate operand lowers to the same compare + branch
pair. -/
theorem arm8Enc_jumpCmp_imm_eq (operator : Cmp) (source : Nat) (value : BitVec 64)
    (target : BitVec 64) :
    Arm8.arm8Enc (.jumpCmp operator source (.imm value) target) =
      arm8Enc (.jumpCmp operator source (.imm value) target) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, arm8Enc, arm8Ast]
  by_cases ht : isTest operator = true
  · simp only [if_pos ht, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_logicalImmediate .and .LogicalOp_AND true value source 31
        (by rw [EncodeLogicalOp_AND true]), encodeBytes_branchConditional]
    rw [← arm8CmpCond_eq operator]
    simp
  · simp only [if_neg ht, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubImmediate, encodeBytes_branchConditional]
    rw [← arm8CmpCond_eq operator]
    simp

/-- `.inst .skip` lowers to the same no-op. -/
theorem arm8Enc_inst_skip_eq :
    Arm8.arm8Enc (.inst .skip) = arm8Enc (.inst .skip) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, encodeBytes_noOp]

/-- `.inst (.arith (.div ...))` lowers to the same division form. -/
theorem arm8Enc_inst_div_eq (destination dividend divisor : Nat) :
    Arm8.arm8Enc (.inst (.arith (.div destination dividend divisor))) =
      arm8Enc (.inst (.arith (.div destination dividend divisor))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, encodeBytes_division]
  simp

/-- `.inst (.arith (.shift ... (.reg ...)))` lowers to the same shift form. -/
theorem arm8Enc_inst_shiftReg_eq (sh : Shift) (destination source right : Nat) :
    Arm8.arm8Enc (.inst (.arith (.shift sh destination source (.reg right)))) =
      arm8Enc (.inst (.arith (.shift sh destination source (.reg right)))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, encodeBytes_shift]
  simp

/-- `.inst (.arith (.longMul ...))` lowers to the same multiply pair. -/
theorem arm8Enc_inst_longMul_eq (destinationLeft destinationRight sourceLeft
    sourceRight : Nat) :
    Arm8.arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight
        sourceLeft sourceRight))) =
      arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight
        sourceLeft sourceRight))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_multiplyHigh, encodeBytes_multiplyAddSub]
  simp

/-- `.inst (.arith (.longDiv ...))` lowers to the same no-op. -/
theorem arm8Enc_inst_longDiv_eq (destinationLeft destinationRight sourceLeft
    sourceRight quotient : Nat) :
    Arm8.arm8Enc (.inst (.arith (.longDiv destinationLeft destinationRight
        sourceLeft sourceRight quotient))) =
      arm8Enc (.inst (.arith (.longDiv destinationLeft destinationRight
        sourceLeft sourceRight quotient))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    arm8EncodeFail, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_noOp]

/-- `.inst (.arith (.addCarry ...))` lowers to the same five-instruction
sequence. -/
theorem arm8Enc_inst_addCarry_eq (destination resultCarry sourceLeft
    sourceRight : Nat) :
    Arm8.arm8Enc (.inst (.arith (.addCarry destination resultCarry
        sourceLeft sourceRight))) =
      arm8Enc (.inst (.arith (.addCarry destination resultCarry
        sourceLeft sourceRight))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_addSubImmediate, encodeBytes_conditionalCompareImmediate,
    encodeBytes_addSubCarry, encodeBytes_moveWide]
  simp

/-- `.inst (.arith (.addOverflow ...))` lowers to the same two-instruction
sequence. -/
theorem arm8Enc_inst_addOverflow_eq (destination resultCarry sourceLeft
    sourceRight : Nat) :
    Arm8.arm8Enc (.inst (.arith (.addOverflow destination resultCarry
        sourceLeft sourceRight))) =
      arm8Enc (.inst (.arith (.addOverflow destination resultCarry
        sourceLeft sourceRight))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_addSubShiftedRegister, encodeBytes_conditionalSelect]
  simp

/-- `.inst (.arith (.subOverflow ...))` lowers to the same two-instruction
sequence. -/
theorem arm8Enc_inst_subOverflow_eq (destination resultCarry sourceLeft
    sourceRight : Nat) :
    Arm8.arm8Enc (.inst (.arith (.subOverflow destination resultCarry
        sourceLeft sourceRight))) =
      arm8Enc (.inst (.arith (.subOverflow destination resultCarry
        sourceLeft sourceRight))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_addSubShiftedRegister, encodeBytes_conditionalSelect]
  simp

/-- `.inst (.mem .load8 ...)` lowers to the same byte load. -/
theorem arm8Enc_inst_load8_eq (destination base : Nat) (offset : BitVec 64) :
    Arm8.arm8Enc (.inst (.mem .load8 destination (.addr base offset))) =
      arm8Enc (.inst (.mem .load8 destination (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_loadStore8_load]
  simp

/-- `.inst (.mem .store8 ...)` lowers to the same byte store. -/
theorem arm8Enc_inst_store8_eq (destination base : Nat) (offset : BitVec 64) :
    Arm8.arm8Enc (.inst (.mem .store8 destination (.addr base offset))) =
      arm8Enc (.inst (.mem .store8 destination (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_loadStore8_store]
  simp

/-- `.inst (.fp _)` lowers to the same no-op. -/
theorem arm8Enc_inst_fp_eq (operation : HolFp) :
    Arm8.arm8Enc (.inst (.fp operation)) = arm8Enc (.inst (.fp operation)) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast,
    arm8EncodeFail, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_noOp]

end Flapjack.Compiler.Encoders.Arm8.L3
