import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Overflow

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# `JumpCmp`: the flag-setting compare instructions

`arm8_ast` lowers `JumpCmp` to a compare into `XZR` (`0x1Fw`) followed by a
`BranchConditional` on `cmp_cond cmp`.  The `is_test` forms emit
`LogicalShiftedRegister@64` with `LogicalOp_AND` and `S := T` (its opcode bits
are `0b11`); the ordering forms emit `AddSubShiftedRegister@64` with
`op := T` and `S := T`.

This module records the instruction-level `Encode`/`Decode`/`Run`/`Next` facts
for both compare shapes.  These are Flapjack case splits of the single HOL
theorem `arm8_encoder_correct` (`cakeml/compiler/encoders/arm8/
arm8_targetProofScript.sml`), so they carry no `@[hol]` tag of their own; the
HOL `JumpCmp` case is tracked on the assembling theorem.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-! ## The `is_test` compare: `ANDS` into `XZR` -/

/-- `Encode` of the `LogicalShiftedRegister@64` that `arm8_ast` emits for the
`is_test` comparisons: an `AND` with `S := T`, whose opcode bits are `0b11`. -/
theorem arm8Encode_logicalShiftedRegister_ands (rm rn rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd) := by
  rfl

/-- The rendered `Decode` inverts `arm8LogicalShiftedRegisterWord` when the
decoded opcode carries the set-flags bit. -/
theorem arm8Decode_logicalShiftedRegister_setflags (opc : LogicalOp) (opcbits : BitVec 2)
    (hdec : DecodeLogicalOp opcbits = (opc, true)) (invert : Bool) (rm rn rd : BitVec 5) :
    Decode (arm8LogicalShiftedRegisterWord opcbits invert .lsl 0 rm rn rd) =
      instruction.Data (Data.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (opc, (invert, (true, (ShiftType.lsl,
          (0, (rm, (rn, rd))))))))) := by
  simp only [arm8LogicalShiftedRegisterWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases invert <;>
    simp [holV2w_two, holV2w_two_zero, holV2w_five, arm8HolV2w_one_false,
      arm8HolV2w_one_true, arm8HolV2w_six_zero, hdec, DecodeShift, num2ShiftType,
      ShiftType2num]

/-- `DecodeLogicalOp` of the `ANDS` opcode bits is `LogicalOp_AND` with the
set-flags bit. -/
theorem arm8DecodeLogicalOp_ands :
    DecodeLogicalOp (3 : BitVec 2) = (.LogicalOp_AND, true) := by
  simp [DecodeLogicalOp]

/-- `Decode` of the `ANDS` word is the compare instruction. -/
theorem arm8Decode_logicalShiftedRegister_ands (rm rn rd : BitVec 5) :
    Decode (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false .lsl 0 rm rn rd) =
      instruction.Data (Data.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
          (0, (rm, (rn, rd))))))))) :=
  arm8Decode_logicalShiftedRegister_setflags .LogicalOp_AND 3 arm8DecodeLogicalOp_ands false rm rn rd

/-- `Run` of the `ANDS` compare into `XZR`: the `AND` result sets `N` from its
most significant bit, `Z` from its zero-ness, and clears `C` and `V`; the
`XZR` destination discards the value. -/
theorem arm8Run_logicalShiftedRegister_ands_eq (rm rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl,
        (0, (rm, (rn, 31)))))))))) st =
      { st with
        PSTATE :=
          { st.PSTATE with
            N := BitVec.msb (X (TN := 64) rn st &&& X (TN := 64) rm st),
            Z := (X (TN := 64) rn st &&& X (TN := 64) rm st) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  simp only [Run, «dfn'LogicalShiftedRegister», SetTheFlags, ShiftReg, ShiftValue,
    BitVec.shiftLeft_zero, «write'X», if_true, Bool.false_eq_true]
  rfl

/-- One `arm8Next` step on the `ANDS` compare word: the flags come from the
`AND`, the destination is `XZR`, and `PC` advances by four. -/
theorem arm8Next_logicalShiftedRegister_ands (ms : arm8_state) (rm rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := BitVec.msb (X (TN := 64) rn ms &&& X (TN := 64) rm ms),
            Z := (X (TN := 64) rn ms &&& X (TN := 64) rm ms) == (0 : BitVec 64),
            C := false,
            V := false } } := by
  let i : instruction := instruction.Data (Data.«LogicalShiftedRegister@64»
    ((1 : BitVec 64), (.LogicalOp_AND, (false, (true, (ShiftType.lsl, (0, (rm, (rn, 31)))))))))
  have hdec : Decode (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31) = i := by
    dsimp only [i]
    exact arm8Decode_logicalShiftedRegister_ands rm rn 31
  have hrun := arm8Run_logicalShiftedRegister_ands_eq rm rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8LogicalShiftedRegisterWord (3 : BitVec 2) false ShiftType.lsl 0 rm rn 31)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

/-! ## The ordering compare: `SUBS` into `XZR` -/

/-- Writing to `XZR` (`31`) leaves the state unchanged. -/
theorem arm8WriteX_xzr (s : arm8_state) (v : BitVec 64) :
    «write'X» (v, (31 : BitVec 5)) s = s := by
  simp [«write'X»]

/-- `Run` of the flag-setting `AddSubShiftedRegister@64` compare into `XZR`:
the subtraction `Rn - Rm` sets the flags from `AddWithCarry` and the `XZR`
destination discards the value. -/
theorem arm8Run_addSubShiftedRegister_setflags_xzr_eq (rm rn : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (true, (true, (ShiftType.lsl, (rm, (0, (rn, 31))))))))) st =
      { st with
        PSTATE :=
          { st.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn st,
              (~~~X (TN := 64) rm st, true))).2.2.2.2 } } := by
  rw [arm8Run_addSubShiftedRegister_setflags]
  dsimp only
  rw [arm8WriteX_xzr]
  have hz : BitVec.toNat (0 : BitVec 6) = 0 := by decide
  simp only [SetTheFlags, ShiftReg, ShiftValue, if_true, hz, BitVec.shiftLeft_zero]

/-- One `arm8Next` step on the `SUBS` compare word: the flags come from
`Rn - Rm`, the destination is `XZR`, and `PC` advances by four. -/
theorem arm8Next_addSubShiftedRegister_setflags_xzr (ms : arm8_state) (rm rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31 >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        PC := ms.PC + 4,
        PSTATE :=
          { ms.PSTATE with
            N := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.1,
            Z := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.1,
            C := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.2.1,
            V := (AddWithCarry (TN := 64) (X (TN := 64) rn ms,
              (~~~X (TN := 64) rm ms, true))).2.2.2.2 } } := by
  let i : instruction := instruction.Data (Data.«AddSubShiftedRegister@64»
    ((1 : BitVec 64), (true, (true, (ShiftType.lsl, (rm, (0, (rn, 31))))))))
  have hdec : Decode (arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31) = i := by
    dsimp only [i]
    exact arm8Decode_addSubShiftedRegister true true rm 0 rn 31
  have hrun := arm8Run_addSubShiftedRegister_setflags_xzr_eq rm rn { ms with branch_hint := none }
  have hbr : (Run i { ms with branch_hint := none }).branch_hint = none := by
    dsimp only [i]
    rw [hrun]
  have hexc : (Run i { ms with branch_hint := none }).exception = exception.NoException := by
    dsimp only [i]
    rw [hrun]
    simpa using hexc0
  have hn := arm8Next_word ms (arm8AddSubShiftedRegisterWord true true ShiftType.lsl rm 0 rn 31)
    i hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn]
  dsimp only [i]
  rw [hrun]
  rfl

end Flapjack.Compiler.Encoders.Arm8.L3
