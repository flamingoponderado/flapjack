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
  simp

/-- A truncated `Nat` field of a `MoveWide` half-word index, moved onto the
`BitVec 2` carrier. -/
theorem ofNat2_mod (v : Nat) : BitVec.ofNat 2 (v % 4) = BitVec.ofNat 2 v := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- A truncated `Nat` register field, moved onto the `BitVec 5` carrier. -/
theorem ofNat5_mod (v : Nat) : BitVec.ofNat 5 (v % 32) = BitVec.ofNat 5 v := by
  apply BitVec.eq_of_toNat_eq
  simp

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

/-- The computable and L3 bitmask-success tests agree. -/
theorem encodeBitMask_isSome_eq (imm : BitVec 64) :
    (encodeBitMask imm).isSome = (EncodeBitMask (TN := 64) imm).isSome := by
  rw [EncodeBitMask_eq_map]
  cases encodeBitMask imm <;> rfl

/-- `.inst (.const ...)` lowers to the same move-wide or logical-immediate
sequence, in all four cases. -/
theorem arm8Enc_inst_const_eq (destination : Nat) (value : BitVec 64) :
    Arm8.arm8Enc (.inst (.const destination value)) =
      arm8Enc (.inst (.const destination value)) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  have hmap := encMovImm_eq value
  cases h1 : encMovImm value with
  | some p =>
    obtain ⟨imm16, hw⟩ := p
    have h1' : arm8EncMovImm value =
        some (BitVec.ofNat 16 imm16, BitVec.ofNat 2 hw) := by
      rw [h1] at hmap
      simpa using hmap.symm
    simp only [h1', List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [encodeBytes_moveWide]
    rfl
  | none =>
    have h1' : arm8EncMovImm value = none := by
      rw [h1] at hmap
      simpa using hmap.symm
    have hmap2 := encMovImm_eq (~~~value)
    cases h2 : encMovImm (~~~value) with
    | some p =>
      obtain ⟨imm16, hw⟩ := p
      have h2' : arm8EncMovImm (~~~value) =
          some (BitVec.ofNat 16 imm16, BitVec.ofNat 2 hw) := by
        rw [h2] at hmap2
        simpa using hmap2.symm
      simp only [h1', h2', List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [encodeBytes_moveWide]
      rfl
    | none =>
      have h2' : arm8EncMovImm (~~~value) = none := by
        rw [h2] at hmap2
        simpa using hmap2.symm
      cases hb : (encodeBitMask value).isSome
      · have hb' : (EncodeBitMask (TN := 64) value).isSome = false := by
          rw [← encodeBitMask_isSome_eq]
          exact hb
        simp only [h1', h2', hb', Bool.false_eq_true, if_false,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          encodeBytes_moveWide, ofNat16_mod]
        simp
      · have hb' : (EncodeBitMask (TN := 64) value).isSome = true := by
          rw [← encodeBitMask_isSome_eq]
          exact hb
        simp only [h1', h2', hb', if_true,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          encodeBytes_logicalImmediate .orr .LogicalOp_ORR false value 31 destination
            (EncodeLogicalOp_ORR false)]
        simp

/-- `.inst (.arith (.binop ... (.reg ...)))` lowers to the same register
operation. -/
theorem arm8Enc_inst_binop_reg_eq (bop : BinOp) (destination source right : Nat) :
    Arm8.arm8Enc (.inst (.arith (.binop bop destination source (.reg right)))) =
      arm8Enc (.inst (.arith (.binop bop destination source (.reg right)))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  cases bop
  case add =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubShiftedRegister]
    simp
  case sub =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubShiftedRegister]
    simp
  case and =>
    simp only [bopEnc, arm8BopEnc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      encodeBytes_logicalShiftedRegister .and .LogicalOp_AND false false .lsl 0 right source destination 0
        rfl (by decide) (by decide)]
    simp
  case or =>
    simp only [bopEnc, arm8BopEnc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      encodeBytes_logicalShiftedRegister .orr .LogicalOp_ORR false false .lsl 0 right source destination 1
        rfl (by decide) (by decide)]
    simp
  case xor =>
    simp only [bopEnc, arm8BopEnc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      encodeBytes_logicalShiftedRegister .eor .LogicalOp_EOR false false .lsl 0 right source destination 2
        rfl (by decide) (by decide)]
    simp

/-- `.inst (.arith (.binop ... (.imm ...)))` lowers to the same immediate
operation, including the `xor -1` special case. -/
theorem arm8Enc_inst_binop_imm_eq (bop : BinOp) (destination source : Nat)
    (value : BitVec 64) :
    Arm8.arm8Enc (.inst (.arith (.binop bop destination source (.imm value)))) =
      arm8Enc (.inst (.arith (.binop bop destination source (.imm value)))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  cases bop
  case add =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubImmediate]
    simp
  case sub =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_addSubImmediate]
    simp
  case xor =>
    by_cases hv : value = -1
    · simp only [hv, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        encodeBytes_logicalShiftedRegister .orr .LogicalOp_ORR true false .lsl 0 source 31 destination 1
          rfl (by decide) (by decide)]
      simp
    · simp only [hv, if_false, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        encodeBytes_logicalImmediate .eor .LogicalOp_EOR false value source destination
          (EncodeLogicalOp_EOR false)]
      simp
  case and =>
    simp only [bopEnc, arm8BopEnc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      encodeBytes_logicalImmediate .and .LogicalOp_AND false value source destination
        (EncodeLogicalOp_AND false)]
    simp
  case or =>
    simp only [bopEnc, arm8BopEnc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      encodeBytes_logicalImmediate .orr .LogicalOp_ORR false value source destination
        (EncodeLogicalOp_ORR false)]
    simp


/-- The L3 `-i6` rotation field is the computable `(64 - n % 64) % 64`. -/
theorem bitfieldLslR_toNat (value : BitVec 64) :
    ((-(BitVec.ofNat 6 value.toNat) : BitVec 6)).toNat =
      (64 - value.toNat % 64) % 64 := by
  rw [BitVec.toNat_neg]
  have hlt : (BitVec.ofNat 6 value.toNat).toNat = value.toNat % 64 := by
    simp
  rw [hlt]

/-- The L3 `63 - i6` field is the computable `63 - n % 64`. -/
theorem bitfieldLslS_toNat (value : BitVec 64) :
    (((63 : BitVec 6) - BitVec.ofNat 6 value.toNat)).toNat =
      63 - value.toNat % 64 := by
  have hlt : (BitVec.ofNat 6 value.toNat).toNat = value.toNat % 64 := by
    simp
  rw [BitVec.toNat_sub, hlt]
  have h63 : (63 : BitVec 6).toNat = 63 := by decide
  rw [h63]
  have : value.toNat % 64 ≤ 63 := by omega
  omega

/-- The L3 `BitVec.ofNat 6 n` is the computable `n % 64` on `Nat`. -/
theorem bitfieldN_toNat (value : BitVec 64) :
    (BitVec.ofNat 6 value.toNat).toNat = value.toNat % 64 := by
  simp

/-- `decodeBitMasks` succeeds with the `toNat` masks whenever `DecodeBitMasks`
does. -/
theorem decodeBitMasks_some (immN : BitVec 1) (imms immr : BitVec 6) (b : Bool)
    (wmask tmask : BitVec 64)
    (h : DecodeBitMasks (TM := 64) (immN, (imms, (immr, b))) = some (wmask, tmask)) :
    decodeBitMasks immN.toNat imms.toNat immr.toNat b =
      some (wmask.toNat, tmask.toNat) := by
  rw [decodeBitMasks_eq, h]
  rfl

/-- `decodeBitMasks` fails whenever `DecodeBitMasks` does. -/
theorem decodeBitMasks_none (immN : BitVec 1) (imms immr : BitVec 6) (b : Bool)
    (h : DecodeBitMasks (TM := 64) (immN, (imms, (immr, b))) = none) :
    decodeBitMasks immN.toNat imms.toNat immr.toNat b = none := by
  rw [decodeBitMasks_eq, h]
  rfl

/-- A six-bit truncation on the `Nat` side moves onto the `BitVec 6` carrier. -/
theorem ofNat6_mod (v : Nat) : BitVec.ofNat 6 (v % 64) = BitVec.ofNat 6 v := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- The `BitVec 6` carrier roundtrips through its `toNat`. -/
theorem ofNat_toNat_six (x : BitVec 6) : BitVec.ofNat 6 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- `.inst (.arith (.shift ... (.imm ...)))` lowers to the same shift form, in
all four shift kinds. -/
theorem arm8Enc_inst_shiftImm_eq (sh : Shift) (destination source : Nat)
    (value : BitVec 64) :
    Arm8.arm8Enc (.inst (.arith (.shift sh destination source (.imm value)))) =
      arm8Enc (.inst (.arith (.shift sh destination source (.imm value)))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  cases sh
  case lsl =>
    rw [← bitfieldLslS_toNat value, ← bitfieldLslR_toNat value]
    cases hd : DecodeBitMasks (TM := 64) ((1 : BitVec 1),
        ((63 : BitVec 6) - BitVec.ofNat 6 value.toNat,
         (-(BitVec.ofNat 6 value.toNat), false))) with
    | none =>
      have hd' : decodeBitMasks 1 ((64 - value.toNat % 64 + 63) % 64)
          ((64 - value.toNat % 64) % 64) false = none := by
        rw [show (64 - value.toNat % 64 + 63) % 64 = 63 - value.toNat % 64 from by omega]
        have h := decodeBitMasks_none 1 ((63 : BitVec 6) - BitVec.ofNat 6 value.toNat)
          (-(BitVec.ofNat 6 value.toNat)) false hd
        rwa [bitfieldLslS_toNat value, bitfieldLslR_toNat value] at h
      simp [hd', encodeBytes_noOp, arm8EncodeFail]
    | some p =>
      obtain ⟨wmask, tmask⟩ := p
      have hd' : decodeBitMasks 1 ((63 : BitVec 6) - BitVec.ofNat 6 value.toNat).toNat
          ((-(BitVec.ofNat 6 value.toNat)).toNat) false =
          some (wmask.toNat, tmask.toNat) :=
        decodeBitMasks_some 1 ((63 : BitVec 6) - BitVec.ofNat 6 value.toNat)
          (-(BitVec.ofNat 6 value.toNat)) false wmask tmask hd
      simp only [hd', List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [encodeBytes_bitfieldMove true false ((-(BitVec.ofNat 6 value.toNat)).toNat)
        (((63 : BitVec 6) - BitVec.ofNat 6 value.toNat)).toNat source destination 2 wmask tmask
        rfl (by rw [bitfieldLslR_toNat]; omega) (by rw [bitfieldLslS_toNat]; omega)
        (by rw [ofNat_toNat_six, ofNat_toNat_six]; exact hd)]
      rfl
  case ror =>
    simp [encodeBytes_extractRegister, ofNat6_mod]
  case lsr =>
    cases hd : DecodeBitMasks (TM := 64) ((1 : BitVec 1),
        ((63 : BitVec 6), (BitVec.ofNat 6 value.toNat, false))) with
    | none =>
      have hd' : decodeBitMasks 1 63 (BitVec.ofNat 6 value.toNat).toNat false = none :=
        decodeBitMasks_none 1 63 (BitVec.ofNat 6 value.toNat) false hd
      rw [bitfieldN_toNat] at hd'
      simp [hd', encodeBytes_noOp, arm8EncodeFail]
    | some p =>
      obtain ⟨wmask, tmask⟩ := p
      have hd' : decodeBitMasks 1 63 (BitVec.ofNat 6 value.toNat).toNat false =
          some (wmask.toNat, tmask.toNat) :=
        decodeBitMasks_some 1 63 (BitVec.ofNat 6 value.toNat) false wmask tmask hd
      rw [bitfieldN_toNat] at hd'
      simp only [hd', show (Shift.lsr == Shift.asr) = false from by decide,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases hlt : value.toNat < 64
      · rw [encodeBytes_bitfieldMove true false value.toNat 63 source destination 2 wmask tmask
          rfl hlt (by omega) hd]
        rfl
      · rw [encodeBytes_bitfieldMove_bad true false value.toNat 63 source destination wmask tmask
          (by omega)]
        rfl
  case asr =>
    cases hd : DecodeBitMasks (TM := 64) ((1 : BitVec 1),
        ((63 : BitVec 6), (BitVec.ofNat 6 value.toNat, false))) with
    | none =>
      have hd' : decodeBitMasks 1 63 (BitVec.ofNat 6 value.toNat).toNat false = none :=
        decodeBitMasks_none 1 63 (BitVec.ofNat 6 value.toNat) false hd
      rw [bitfieldN_toNat] at hd'
      simp [hd', encodeBytes_noOp, arm8EncodeFail]
    | some p =>
      obtain ⟨wmask, tmask⟩ := p
      have hd' : decodeBitMasks 1 63 (BitVec.ofNat 6 value.toNat).toNat false =
          some (wmask.toNat, tmask.toNat) :=
        decodeBitMasks_some 1 63 (BitVec.ofNat 6 value.toNat) false wmask tmask hd
      rw [bitfieldN_toNat] at hd'
      simp only [hd', show (Shift.asr == Shift.asr) = true from by decide,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases hlt : value.toNat < 64
      · rw [encodeBytes_bitfieldMove true true value.toNat 63 source destination 0 wmask tmask
          rfl hlt (by omega) hd]
        rfl
      · rw [encodeBytes_bitfieldMove_bad true true value.toNat 63 source destination wmask tmask
          (by omega)]
        rfl

/-! ## Load/store immediate

`load_store_ast` and its 32/16-bit siblings share one shape: a nine-bit
signed-offset guard and, when it fails, a `temp`-register address computation
followed by the scaled immediate form.  The computable encoder writes the
scaled offset with `BitVec.ofNat 64` while the L3 ast uses `zeroExtend`; the
two agree on the same twelve-bit field. -/

/-- The computable scaled offset is the L3 `scaled` word, at the same shift. -/
theorem loadStoreScaled_eq (k : Nat) (a : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat >>> k % 4096)) <<< k =
      (BitVec.zeroExtend 64 (BitVec.ofNat 12 (a.toNat >>> k))) <<< k := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- The L3 sign-extended nine-bit immediate is the computable `sx9`. -/
theorem sx9_eq (a : BitVec 64) :
    BitVec.signExtend 64 (BitVec.ofNat 9 a.toNat) =
      BitVec.signExtend 64 (BitVec.setWidth 9 a) := by
  congr 1

/-- The computable nine-bit fit test is the L3 `a = sx9` test. -/
theorem fitsSigned9_eq (a : BitVec 64) :
    fitsSigned 9 a = (a == BitVec.signExtend 64 (BitVec.ofNat 9 a.toNat)) := by
  rw [loadStoreGuard9_eq, h9w_eq, ← sx9_eq]

/-- A 64-bit load lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst64_load_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 3 false .load r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst .MemOp_LOAD r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore64_load]

/-- A 64-bit store lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst64_store_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 3 false .store r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst .MemOp_STORE r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore64_store]

/-- A 32-bit load lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst32_load_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 2 true .load r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst32 .MemOp_LOAD r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst32, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore32_load]

/-- A 32-bit store lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst32_store_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 2 true .store r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst32 .MemOp_STORE r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst32, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore32_store]

/-- A 16-bit load lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst16_load_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 1 true .load r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst16 .MemOp_LOAD r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst16, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore16_load]

/-- A 16-bit store lowers to the same instruction list, up to encoding. -/
theorem loadStoreAst16_store_eq (r1 r2 : Nat) (a : BitVec 64) :
    (loadStoreAst 1 true .store r1 r2 a).flatMap encodeBytes =
      (arm8LoadStoreAst16 .MemOp_STORE r1 r2 a).flatMap arm8Encode := by
  simp [loadStoreAst, arm8LoadStoreAst16, loadStoreScaled_eq, fitsSigned9_eq]
  split_ifs <;> simp_all [temp, encodeBytes_addSubImmediate, encodeBytes_loadStore16_store]

/-- `.inst (.mem .load ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore64_load_eq (destination base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .load destination (.addr base offset))) =
      arm8Enc (.inst (.mem .load destination (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst64_load_eq destination base offset

/-- `.inst (.mem .store ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore64_store_eq (source base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .store source (.addr base offset))) =
      arm8Enc (.inst (.mem .store source (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst64_store_eq source base offset

/-- `.inst (.mem .load32 ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore32_load_eq (destination base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .load32 destination (.addr base offset))) =
      arm8Enc (.inst (.mem .load32 destination (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst32_load_eq destination base offset

/-- `.inst (.mem .store32 ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore32_store_eq (source base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .store32 source (.addr base offset))) =
      arm8Enc (.inst (.mem .store32 source (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst32_store_eq source base offset

/-- `.inst (.mem .load16 ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore16_load_eq (destination base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .load16 destination (.addr base offset))) =
      arm8Enc (.inst (.mem .load16 destination (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst16_load_eq destination base offset

/-- `.inst (.mem .store16 ...)` lowers to the same bytes. -/
theorem arm8Enc_inst_loadStore16_store_eq (source base : Nat) (offset : W) :
    Arm8.arm8Enc (.inst (.mem .store16 source (.addr base offset))) =
      arm8Enc (.inst (.mem .store16 source (.addr base offset))) := by
  simp only [Arm8.arm8Enc, Arm8.arm8Ast, Arm8.arm8Inst, arm8Enc, arm8Ast]
  exact loadStoreAst16_store_eq source base offset

end Flapjack.Compiler.Encoders.Arm8.L3
