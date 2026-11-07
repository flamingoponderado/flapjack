import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Arith
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Loc

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The out-of-range `Loc` constructor of `encoder_correct arm8TargetL3`

When the `Loc` offset is outside the signed 20-bit range, `arm8_ast` lowers it
to six instructions: `Address` with immediate zero (writing `PC` to the
destination), four `MoveWide .k` insertions of the offset into the temporary
register 26, and a final `AddSubShiftedRegister@64` adding the temporary to the
destination.

This module records the lowering shape, its 24-byte encoding, the six
`NextStateARM8` steps, and the resulting case theorem.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The `Address` instruction of the out-of-range `Loc` lowering. -/
abbrev arm8LocBigAddrInsn (register : Nat) : instruction :=
  .Address (false, (0, BitVec.ofNat 5 register))

/-- The `k`-th `MoveWide .k` instruction of the out-of-range `Loc` lowering,
which inserts bits `16*k+15:16*k` of the offset into register 26. -/
abbrev arm8LocBigMovInsn (k : Nat) (offset : BitVec 64) : instruction :=
  .Data (.«MoveWide@64»
    (1, .k, BitVec.ofNat 2 k, BitVec.ofNat 16 ((offset >>> (16 * k)).toNat), 26))

/-- The final `AddSubShiftedRegister@64` instruction, adding register 26 to the
destination. -/
abbrev arm8LocBigAddInsn (register : Nat) : instruction :=
  .Data (.«AddSubShiftedRegister@64» (1, false, false, .lsl, 26, 0, register, register))

/-- The out-of-range `Loc` lowering shape. -/
theorem arm8Ast_loc_big (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = false) :
    arm8Ast (.loc register offset) =
      [arm8LocBigAddrInsn register,
       arm8LocBigMovInsn 0 offset,
       arm8LocBigMovInsn 1 offset,
       arm8LocBigMovInsn 2 offset,
       arm8LocBigMovInsn 3 offset,
       arm8LocBigAddInsn register] := by
  simp only [arm8Ast]
  rw [ite_eq_right (by rw [h]; decide)]
  simp [arm8LocBigAddrInsn, arm8LocBigMovInsn, arm8LocBigAddInsn]

/-- The encoded bytes of the out-of-range `Loc` lowering. -/
theorem arm8Enc_loc_big (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = false) :
    arm8Enc (.loc register offset) =
      (arm8Encode (arm8LocBigAddrInsn register) ++
        (arm8Encode (arm8LocBigMovInsn 0 offset) ++
          (arm8Encode (arm8LocBigMovInsn 1 offset) ++
            (arm8Encode (arm8LocBigMovInsn 2 offset) ++
              (arm8Encode (arm8LocBigMovInsn 3 offset) ++
                arm8Encode (arm8LocBigAddInsn register)))))) := by
  rw [arm8Enc, arm8Ast_loc_big register offset h]
  simp

/-- The out-of-range `Loc` lowering encodes to 24 bytes. -/
theorem arm8Enc_loc_big_length (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = false) :
    (arm8Enc (.loc register offset)).length = 24 := by
  rw [arm8Enc_loc_big register offset h]
  simp [arm8Encode_length]

/-! ## The final `AddSubShiftedRegister@64` step -/

/-- `Run` of the final add instruction: destination `register + 26`. -/
theorem arm8Run_locBigAdd (register : Nat) (st : arm8_state) :
    Run (arm8LocBigAddInsn register) st =
      «write'X» (X (TN := 64) (BitVec.ofNat 5 register) st +
        X (TN := 64) (26 : BitVec 5) st, BitVec.ofNat 5 register) st := by
  unfold arm8LocBigAddInsn
  rw [arm8Run_addSubShiftedRegister]
  simp [ShiftValue, ShiftReg, SetTheFlags, arm8AddWithCarry_add]

/-- One `NextStateARM8` step on the final add instruction. -/
theorem arm8Next_locBigAdd (ms : arm8_state) (register : Nat)
    (hrd : register ≠ 31) (hlt : register < 32)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false
      ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false
      ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false
      ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false
      ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 register)
          (X (TN := 64) (BitVec.ofNat 5 register) ms + X (TN := 64) (26 : BitVec 5) ms) ms.REG,
        PC := ms.PC + 4 } := by
  have hdec : Decode (arm8AddSubShiftedRegisterWord false false ShiftType.lsl 26 0
      (BitVec.ofNat 5 register) (BitVec.ofNat 5 register)) =
      arm8LocBigAddInsn register := by
    unfold arm8LocBigAddInsn
    exact arm8Decode_addSubShiftedRegister false false (26 : BitVec 5) (0 : BitVec 6) _ _
  have hrun : Run (arm8LocBigAddInsn register) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 register)
          (X (TN := 64) (BitVec.ofNat 5 register) ms + X (TN := 64) (26 : BitVec 5) ms) ms.REG } := by
    rw [arm8Run_locBigAdd]
    rw [arm8WriteX_of_valid _ _ hrd hlt]
    rfl
  refine arm8Next_eq ms _ _ _ hdec ?_ rfl hexc0 h0 h1 h2 h3 hal he0 hel
  rw [hrun]

/-! ## The six-step chain -/

/-- The state after the `Address` step. -/
def arm8LocBigT1 (ms : arm8_state) (register : Nat) : arm8_state :=
  { ms with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 register) (ms.PC + (0 : BitVec 64)) ms.REG,
    PC := ms.PC + 4 }

/-- The state after the first `MoveWide .k` step. -/
def arm8LocBigT2 (ms : arm8_state) (offset : BitVec 64) (register : Nat) : arm8_state :=
  { arm8LocBigT1 ms register with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((offset >>> 0).toNat))
        (X (TN := 64) (26 : BitVec 5) (arm8LocBigT1 ms register)))
      (arm8LocBigT1 ms register).REG,
    PC := (arm8LocBigT1 ms register).PC + 4 }

/-- The state after the second `MoveWide .k` step. -/
def arm8LocBigT3 (ms : arm8_state) (offset : BitVec 64) (register : Nat) : arm8_state :=
  { arm8LocBigT2 ms offset register with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((offset >>> 16).toNat))
        (X (TN := 64) (26 : BitVec 5) (arm8LocBigT2 ms offset register)))
      (arm8LocBigT2 ms offset register).REG,
    PC := (arm8LocBigT2 ms offset register).PC + 4 }

/-- The state after the third `MoveWide .k` step. -/
def arm8LocBigT4 (ms : arm8_state) (offset : BitVec 64) (register : Nat) : arm8_state :=
  { arm8LocBigT3 ms offset register with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((offset >>> 32).toNat))
        (X (TN := 64) (26 : BitVec 5) (arm8LocBigT3 ms offset register)))
      (arm8LocBigT3 ms offset register).REG,
    PC := (arm8LocBigT3 ms offset register).PC + 4 }

/-- The state after the fourth `MoveWide .k` step. -/
def arm8LocBigT5 (ms : arm8_state) (offset : BitVec 64) (register : Nat) : arm8_state :=
  { arm8LocBigT4 ms offset register with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((offset >>> 48).toNat))
        (X (TN := 64) (26 : BitVec 5) (arm8LocBigT4 ms offset register)))
      (arm8LocBigT4 ms offset register).REG,
    PC := (arm8LocBigT4 ms offset register).PC + 4 }

/-- The state after the final `AddSubShiftedRegister@64` step. -/
def arm8LocBigT6 (ms : arm8_state) (offset : BitVec 64) (register : Nat) : arm8_state :=
  { arm8LocBigT5 ms offset register with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 register)
      (X (TN := 64) (BitVec.ofNat 5 register) (arm8LocBigT5 ms offset register) +
        X (TN := 64) (26 : BitVec 5) (arm8LocBigT5 ms offset register))
      (arm8LocBigT5 ms offset register).REG,
    PC := (arm8LocBigT5 ms offset register).PC + 4 }

/-- `holAligned 2` of `PC + 4`, `+ 8`, `+ 12`, `+ 16`, `+ 20` and `+ 24`. -/
theorem holAligned_add_four' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 4) = true := by
  rw [(alignedAddSub 2 pc 4 (by rw [holAligned_iff]; decide)).1, h]

theorem holAligned_add_eight' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 8) = true := by
  rw [(alignedAddSub 2 pc 8 (by rw [holAligned_iff]; decide)).1, h]

theorem holAligned_add_twelve' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 12) = true := by
  rw [(alignedAddSub 2 pc 12 (by rw [holAligned_iff]; decide)).1, h]

theorem holAligned_add_sixteen' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 16) = true := by
  rw [(alignedAddSub 2 pc 16 (by rw [holAligned_iff]; decide)).1, h]

theorem holAligned_add_twenty' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 20) = true := by
  rw [(alignedAddSub 2 pc 20 (by rw [holAligned_iff]; decide)).1, h]

theorem holAligned_add_twentyfour' (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 24) = true := by
  rw [(alignedAddSub 2 pc 24 (by rw [holAligned_iff]; decide)).1, h]

/-- The `Address` step reaches `arm8LocBigT1`. -/
theorem arm8Next_locBigT1 (ms : arm8_state) (register : Nat)
    (hr : register ≠ 31) (hlt : register < 32)
    (hexc0 : ms.exception = exception.NoException)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 (0 : BitVec 64) ++ holWordExtract 2 1 0 (0 : BitVec 64))) = 0)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 0).toNat))
    (hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 8).toNat))
    (hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 16).toNat))
    (hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 24).toNat)) :
    arm8Next ms = arm8LocBigT1 ms register := by
  unfold arm8LocBigT1
  exact arm8Next_address ms 0 register hr hlt hround hexc0 hb0 hb1 hb2 hb3 hal he0 hel


/-- `BitVec` literal reassociation for the later instruction windows. -/
theorem bv_add_16_1 (a : BitVec 64) : a + 16 + 1 = a + 17 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_16_2 (a : BitVec 64) : a + 16 + 2 = a + 18 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_16_3 (a : BitVec 64) : a + 16 + 3 = a + 19 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_16_4 (a : BitVec 64) : a + 16 + 4 = a + 20 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_20_1 (a : BitVec 64) : a + 20 + 1 = a + 21 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_20_2 (a : BitVec 64) : a + 20 + 2 = a + 22 := by
  rw [BitVec.add_assoc]; congr 1
theorem bv_add_20_3 (a : BitVec 64) : a + 20 + 3 = a + 23 := by
  rw [BitVec.add_assoc]; congr 1

/-- `26` is not the zero register. -/
theorem arm8TwentySix_ne_31 : (26 : BitVec 5) ≠ (31 : BitVec 5) := by decide

/-- The first `MoveWide .k` step reaches `arm8LocBigT2`. -/
theorem arm8Next_locBigT2 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hexc0 : ms.exception = exception.NoException)
    (hal4 : Aligned (TN := 64) (ms.PC + 4, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((arm8MoveWideWord .k 0 (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 0).toNat))
    (hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((arm8MoveWideWord .k 0 (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 8).toNat))
    (hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((arm8MoveWideWord .k 0 (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 16).toNat))
    (hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((arm8MoveWideWord .k 0 (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 24).toNat)) :
    arm8Next (arm8LocBigT1 ms register) = arm8LocBigT2 ms offset register := by
  unfold arm8LocBigT2
  have ht1pc : (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl
  have ht1mem : ∀ a, (arm8LocBigT1 ms register).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_movK (arm8LocBigT1 ms register) (BitVec.ofNat 2 0)
    (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8LocBigT1 ms register).exception = exception.NoException
    exact hexc0
  · show (arm8LocBigT1 ms register).MEM (arm8LocBigT1 ms register).PC = _
    rw [ht1pc, ht1mem]; simpa using hb4
  · show (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 1) = _
    rw [ht1pc, ht1mem, bv_add_4_1]; simpa using hb5
  · show (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 2) = _
    rw [ht1pc, ht1mem, bv_add_4_2]; simpa using hb6
  · show (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 3) = _
    rw [ht1pc, ht1mem, bv_add_4_3]; simpa using hb7
  · show Aligned (TN := 64) ((arm8LocBigT1 ms register).PC, 4) = true
    rw [ht1pc]; exact hal4
  · show (arm8LocBigT1 ms register).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8LocBigT1 ms register).PSTATE.EL = (0 : BitVec 2)
    exact hel


/-- The second `MoveWide .k` step reaches `arm8LocBigT3`. -/
theorem arm8Next_locBigT3 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hexc0 : ms.exception = exception.NoException)
    (hal8 : Aligned (TN := 64) (ms.PC + 8, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb8 : ms.MEM (ms.PC + 8) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 0).toNat))
    (hb9 : ms.MEM (ms.PC + 9) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 8).toNat))
    (hb10 : ms.MEM (ms.PC + 10) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 16).toNat))
    (hb11 : ms.MEM (ms.PC + 11) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 24).toNat)) :
    arm8Next (arm8LocBigT2 ms offset register) = arm8LocBigT3 ms offset register := by
  unfold arm8LocBigT3
  have ht2pc : (arm8LocBigT2 ms offset register).PC = ms.PC + 8 := by
    show (arm8LocBigT1 ms register).PC + 4 = ms.PC + 8
    have h : (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl
    rw [h, bv_add_4_4]
  have ht2mem : ∀ a, (arm8LocBigT2 ms offset register).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_movK (arm8LocBigT2 ms offset register) (BitVec.ofNat 2 1)
    (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8LocBigT2 ms offset register).exception = exception.NoException
    exact hexc0
  · show (arm8LocBigT2 ms offset register).MEM (arm8LocBigT2 ms offset register).PC = _
    rw [ht2pc, ht2mem]; simpa using hb8
  · show (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 1) = _
    rw [ht2pc, ht2mem, bv_add_8_1]; simpa using hb9
  · show (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 2) = _
    rw [ht2pc, ht2mem, bv_add_8_2]; simpa using hb10
  · show (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 3) = _
    rw [ht2pc, ht2mem, bv_add_8_3]; simpa using hb11
  · show Aligned (TN := 64) ((arm8LocBigT2 ms offset register).PC, 4) = true
    rw [ht2pc]; exact hal8
  · show (arm8LocBigT2 ms offset register).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8LocBigT2 ms offset register).PSTATE.EL = (0 : BitVec 2)
    exact hel

/-- The third `MoveWide .k` step reaches `arm8LocBigT4`. -/
theorem arm8Next_locBigT4 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hexc0 : ms.exception = exception.NoException)
    (hal12 : Aligned (TN := 64) (ms.PC + 12, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb12 : ms.MEM (ms.PC + 12) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 0).toNat))
    (hb13 : ms.MEM (ms.PC + 13) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 8).toNat))
    (hb14 : ms.MEM (ms.PC + 14) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 16).toNat))
    (hb15 : ms.MEM (ms.PC + 15) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 24).toNat)) :
    arm8Next (arm8LocBigT3 ms offset register) = arm8LocBigT4 ms offset register := by
  unfold arm8LocBigT4
  have ht3pc : (arm8LocBigT3 ms offset register).PC = ms.PC + 12 := by
    show (arm8LocBigT2 ms offset register).PC + 4 = ms.PC + 12
    have h : (arm8LocBigT2 ms offset register).PC = ms.PC + 8 := by
      show (arm8LocBigT1 ms register).PC + 4 = ms.PC + 8
      have h1 : (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl
      rw [h1, bv_add_4_4]
    rw [h, bv_add_8_4]
  have ht3mem : ∀ a, (arm8LocBigT3 ms offset register).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_movK (arm8LocBigT3 ms offset register) (BitVec.ofNat 2 2)
    (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8LocBigT3 ms offset register).exception = exception.NoException
    exact hexc0
  · show (arm8LocBigT3 ms offset register).MEM (arm8LocBigT3 ms offset register).PC = _
    rw [ht3pc, ht3mem]; simpa using hb12
  · show (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 1) = _
    rw [ht3pc, ht3mem, bv_add_12_1]; simpa using hb13
  · show (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 2) = _
    rw [ht3pc, ht3mem, bv_add_12_2]; simpa using hb14
  · show (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 3) = _
    rw [ht3pc, ht3mem, bv_add_12_3]; simpa using hb15
  · show Aligned (TN := 64) ((arm8LocBigT3 ms offset register).PC, 4) = true
    rw [ht3pc]; exact hal12
  · show (arm8LocBigT3 ms offset register).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8LocBigT3 ms offset register).PSTATE.EL = (0 : BitVec 2)
    exact hel

/-- The fourth `MoveWide .k` step reaches `arm8LocBigT5`. -/
theorem arm8Next_locBigT5 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hexc0 : ms.exception = exception.NoException)
    (hal16 : Aligned (TN := 64) (ms.PC + 16, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb16 : ms.MEM (ms.PC + 16) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 0).toNat))
    (hb17 : ms.MEM (ms.PC + 17) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 8).toNat))
    (hb18 : ms.MEM (ms.PC + 18) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 16).toNat))
    (hb19 : ms.MEM (ms.PC + 19) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 24).toNat)) :
    arm8Next (arm8LocBigT4 ms offset register) = arm8LocBigT5 ms offset register := by
  unfold arm8LocBigT5
  have ht4pc : (arm8LocBigT4 ms offset register).PC = ms.PC + 16 := by
    show (arm8LocBigT3 ms offset register).PC + 4 = ms.PC + 16
    have h : (arm8LocBigT3 ms offset register).PC = ms.PC + 12 := by
      show (arm8LocBigT2 ms offset register).PC + 4 = ms.PC + 12
      have h2 : (arm8LocBigT2 ms offset register).PC = ms.PC + 8 := by
        show (arm8LocBigT1 ms register).PC + 4 = ms.PC + 8
        have h1 : (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl
        rw [h1, bv_add_4_4]
      rw [h2, bv_add_8_4]
    rw [h, bv_add_12_4]
  have ht4mem : ∀ a, (arm8LocBigT4 ms offset register).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_movK (arm8LocBigT4 ms offset register) (BitVec.ofNat 2 3)
    (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8LocBigT4 ms offset register).exception = exception.NoException
    exact hexc0
  · show (arm8LocBigT4 ms offset register).MEM (arm8LocBigT4 ms offset register).PC = _
    rw [ht4pc, ht4mem]; simpa using hb16
  · show (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 1) = _
    rw [ht4pc, ht4mem, bv_add_16_1]; simpa using hb17
  · show (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 2) = _
    rw [ht4pc, ht4mem, bv_add_16_2]; simpa using hb18
  · show (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 3) = _
    rw [ht4pc, ht4mem, bv_add_16_3]; simpa using hb19
  · show Aligned (TN := 64) ((arm8LocBigT4 ms offset register).PC, 4) = true
    rw [ht4pc]; exact hal16
  · show (arm8LocBigT4 ms offset register).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8LocBigT4 ms offset register).PSTATE.EL = (0 : BitVec 2)
    exact hel

/-- The final add step reaches `arm8LocBigT6`. -/
theorem arm8Next_locBigT6 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hr : register ≠ 31) (hlt : register < 32)
    (hexc0 : ms.exception = exception.NoException)
    (hal20 : Aligned (TN := 64) (ms.PC + 20, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hb20 : ms.MEM (ms.PC + 20) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 0).toNat))
    (hb21 : ms.MEM (ms.PC + 21) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 8).toNat))
    (hb22 : ms.MEM (ms.PC + 22) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 16).toNat))
    (hb23 : ms.MEM (ms.PC + 23) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 24).toNat)) :
    arm8Next (arm8LocBigT5 ms offset register) = arm8LocBigT6 ms offset register := by
  unfold arm8LocBigT6
  have ht5pc : (arm8LocBigT5 ms offset register).PC = ms.PC + 20 := by
    show (arm8LocBigT4 ms offset register).PC + 4 = ms.PC + 20
    have h : (arm8LocBigT4 ms offset register).PC = ms.PC + 16 := by
      show (arm8LocBigT3 ms offset register).PC + 4 = ms.PC + 16
      have h3 : (arm8LocBigT3 ms offset register).PC = ms.PC + 12 := by
        show (arm8LocBigT2 ms offset register).PC + 4 = ms.PC + 12
        have h2 : (arm8LocBigT2 ms offset register).PC = ms.PC + 8 := by
          show (arm8LocBigT1 ms register).PC + 4 = ms.PC + 8
          have h1 : (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl
          rw [h1, bv_add_4_4]
        rw [h2, bv_add_8_4]
      rw [h3, bv_add_12_4]
    rw [h, bv_add_16_4]
  have ht5mem : ∀ a, (arm8LocBigT5 ms offset register).MEM a = ms.MEM a := fun _ => rfl
  refine arm8Next_locBigAdd (arm8LocBigT5 ms offset register) register hr hlt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (arm8LocBigT5 ms offset register).exception = exception.NoException
    exact hexc0
  · show (arm8LocBigT5 ms offset register).MEM (arm8LocBigT5 ms offset register).PC = _
    rw [ht5pc, ht5mem]; simpa using hb20
  · show (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 1) = _
    rw [ht5pc, ht5mem, bv_add_20_1]; simpa using hb21
  · show (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 2) = _
    rw [ht5pc, ht5mem, bv_add_20_2]; simpa using hb22
  · show (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 3) = _
    rw [ht5pc, ht5mem, bv_add_20_3]; simpa using hb23
  · show Aligned (TN := 64) ((arm8LocBigT5 ms offset register).PC, 4) = true
    rw [ht5pc]; exact hal20
  · show (arm8LocBigT5 ms offset register).SCTLR_EL1.E0E = false
    exact he0
  · show (arm8LocBigT5 ms offset register).PSTATE.EL = (0 : BitVec 2)
    exact hel


/-- Reassociation for the final window. -/
theorem bv_add_20_4 (a : BitVec 64) : a + 20 + 4 = a + 24 := by
  rw [BitVec.add_assoc]; congr 1

/-- Five-bit register numbers below `32` are injective. -/
theorem ofNat5_eq_ofNat5 (a b : Nat) (ha : a < 32) (hb : b < 32)
    (h : (BitVec.ofNat 5 a) = (BitVec.ofNat 5 b)) : a = b := by
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at ht
  have ha' : a % 2 ^ 5 = a := Nat.mod_eq_of_lt (by omega)
  have hb' : b % 2 ^ 5 = b := Nat.mod_eq_of_lt (by omega)
  omega

/-- `PC` after the `Address` step. -/
theorem arm8LocBigT1_pc (ms : arm8_state) (register : Nat) :
    (arm8LocBigT1 ms register).PC = ms.PC + 4 := rfl

/-- `PC` after the first `MoveWide .k` step. -/
theorem arm8LocBigT2_pc (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT2 ms offset register).PC = ms.PC + 8 := by
  show (arm8LocBigT1 ms register).PC + 4 = ms.PC + 8
  rw [arm8LocBigT1_pc, bv_add_4_4]

/-- `PC` after the second `MoveWide .k` step. -/
theorem arm8LocBigT3_pc (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT3 ms offset register).PC = ms.PC + 12 := by
  show (arm8LocBigT2 ms offset register).PC + 4 = ms.PC + 12
  rw [arm8LocBigT2_pc, bv_add_8_4]

/-- `PC` after the third `MoveWide .k` step. -/
theorem arm8LocBigT4_pc (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT4 ms offset register).PC = ms.PC + 16 := by
  show (arm8LocBigT3 ms offset register).PC + 4 = ms.PC + 16
  rw [arm8LocBigT3_pc, bv_add_12_4]

/-- `PC` after the fourth `MoveWide .k` step. -/
theorem arm8LocBigT5_pc (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT5 ms offset register).PC = ms.PC + 20 := by
  show (arm8LocBigT4 ms offset register).PC + 4 = ms.PC + 20
  rw [arm8LocBigT4_pc, bv_add_16_4]

/-- `PC` after the final add step. -/
theorem arm8LocBigT6_pc (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT6 ms offset register).PC = ms.PC + 24 := by
  show (arm8LocBigT5 ms offset register).PC + 4 = ms.PC + 24
  rw [arm8LocBigT5_pc, bv_add_20_4]

theorem arm8LocBigT6_mem (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    ∀ a, (arm8LocBigT6 ms offset register).MEM a = ms.MEM a := fun _ => rfl

/-- The `Address` step writes `PC` into the destination. -/
theorem arm8LocBigT1_reg (ms : arm8_state) (register : Nat) :
    (arm8LocBigT1 ms register).REG (BitVec.ofNat 5 register) = ms.PC := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 register) (ms.PC + (0 : BitVec 64))
    ms.REG (BitVec.ofNat 5 register) = _
  rw [holUpdate_self]
  simp

/-- The `Address` step leaves other registers untouched. -/
theorem arm8LocBigT1_reg_ne (ms : arm8_state) (register j : Nat)
    (h : (BitVec.ofNat 5 register) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT1 ms register).REG (BitVec.ofNat 5 j) = ms.REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 register) _ ms.REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h

/-- The first `MoveWide .k` step inserts bits `15:0` into register 26. -/
theorem arm8LocBigT2_reg_step (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT2 ms offset register).REG (26 : BitVec 5) =
      Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((offset >>> 0).toNat))
        (BitVec.setWidth 64 ((arm8LocBigT1 ms register).REG (26 : BitVec 5))) := by
  have hbeq : ((26 : BitVec 5) == BitVec.ofNat 5 31) = false := by decide
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 15 0 (BitVec.ofNat 16 ((offset >>> 0).toNat))
        (X (26 : BitVec 5) (arm8LocBigT1 ms register)))
      (arm8LocBigT1 ms register).REG (26 : BitVec 5) = _
  rw [holUpdate_self]
  simp only [X, hbeq, Bool.false_eq_true, ite_false]

theorem arm8LocBigT3_reg_step (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT3 ms offset register).REG (26 : BitVec 5) =
      Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((offset >>> 16).toNat))
        (BitVec.setWidth 64 ((arm8LocBigT2 ms offset register).REG (26 : BitVec 5))) := by
  have hbeq : ((26 : BitVec 5) == BitVec.ofNat 5 31) = false := by decide
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 31 16 (BitVec.ofNat 16 ((offset >>> 16).toNat))
        (X (26 : BitVec 5) (arm8LocBigT2 ms offset register)))
      (arm8LocBigT2 ms offset register).REG (26 : BitVec 5) = _
  rw [holUpdate_self]
  simp only [X, hbeq, Bool.false_eq_true, ite_false]

theorem arm8LocBigT4_reg_step (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT4 ms offset register).REG (26 : BitVec 5) =
      Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((offset >>> 32).toNat))
        (BitVec.setWidth 64 ((arm8LocBigT3 ms offset register).REG (26 : BitVec 5))) := by
  have hbeq : ((26 : BitVec 5) == BitVec.ofNat 5 31) = false := by decide
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 47 32 (BitVec.ofNat 16 ((offset >>> 32).toNat))
        (X (26 : BitVec 5) (arm8LocBigT3 ms offset register)))
      (arm8LocBigT3 ms offset register).REG (26 : BitVec 5) = _
  rw [holUpdate_self]
  simp only [X, hbeq, Bool.false_eq_true, ite_false]

theorem arm8LocBigT5_reg_step (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT5 ms offset register).REG (26 : BitVec 5) =
      Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((offset >>> 48).toNat))
        (BitVec.setWidth 64 ((arm8LocBigT4 ms offset register).REG (26 : BitVec 5))) := by
  have hbeq : ((26 : BitVec 5) == BitVec.ofNat 5 31) = false := by decide
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5)
      (Flapjack.RiscV.L3.holBitFieldInsert 63 48 (BitVec.ofNat 16 ((offset >>> 48).toNat))
        (X (26 : BitVec 5) (arm8LocBigT4 ms offset register)))
      (arm8LocBigT4 ms offset register).REG (26 : BitVec 5) = _
  rw [holUpdate_self]
  simp only [X, hbeq, Bool.false_eq_true, ite_false]

theorem arm8LocBigT2_reg_ne (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (26 : BitVec 5) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT2 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT1 ms register).REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5) _ (arm8LocBigT1 ms register).REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h

theorem arm8LocBigT3_reg_ne (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (26 : BitVec 5) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT3 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT2 ms offset register).REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5) _ (arm8LocBigT2 ms offset register).REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h

theorem arm8LocBigT4_reg_ne (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (26 : BitVec 5) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT4 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT3 ms offset register).REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5) _ (arm8LocBigT3 ms offset register).REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h

theorem arm8LocBigT5_reg_ne (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (26 : BitVec 5) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT5 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT4 ms offset register).REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (26 : BitVec 5) _ (arm8LocBigT4 ms offset register).REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h

/-- A register other than 26 is unchanged by the four insertions. -/
theorem arm8LocBigT5_reg (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (26 : BitVec 5) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT5 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT1 ms register).REG (BitVec.ofNat 5 j) := by
  rw [arm8LocBigT5_reg_ne ms offset register j h,
    arm8LocBigT4_reg_ne ms offset register j h,
    arm8LocBigT3_reg_ne ms offset register j h,
    arm8LocBigT2_reg_ne ms offset register j h]

/-- The four insertions put `offset` into register 26. -/
theorem arm8LocBigT5_reg26 (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hr26 : register ≠ 26) (hrlt : register < 32) :
    (arm8LocBigT5 ms offset register).REG (26 : BitVec 5) = offset := by
  have hT1 : (arm8LocBigT1 ms register).REG (26 : BitVec 5) = ms.REG (26 : BitVec 5) := by
    apply arm8LocBigT1_reg_ne ms register 26
    intro hh
    exact hr26 (ofNat5_eq_ofNat5 register 26 hrlt (by decide) hh)
  rw [arm8LocBigT5_reg_step, arm8LocBigT4_reg_step, arm8LocBigT3_reg_step,
    arm8LocBigT2_reg_step, hT1]
  exact arm8MoveWideK_chain (BitVec.setWidth 64 (ms.REG (26 : BitVec 5))) offset

/-- The final add writes `PC + offset` into the destination. -/
theorem arm8LocBigT6_reg_step (ms : arm8_state) (offset : BitVec 64) (register : Nat) :
    (arm8LocBigT6 ms offset register).REG (BitVec.ofNat 5 register) =
      X (BitVec.ofNat 5 register) (arm8LocBigT5 ms offset register) +
        X (26 : BitVec 5) (arm8LocBigT5 ms offset register) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 register) _ (arm8LocBigT5 ms offset register).REG
    (BitVec.ofNat 5 register) = _
  rw [holUpdate_self]

theorem arm8LocBigT6_reg (ms : arm8_state) (offset : BitVec 64) (register : Nat)
    (hr26 : register ≠ 26) (hrlt : register < 32) (hr31 : register ≠ 31) :
    (arm8LocBigT6 ms offset register).REG (BitVec.ofNat 5 register) = ms.PC + offset := by
  have hrd : (BitVec.ofNat 5 register) ≠ (31 : BitVec 5) := by
    intro hh
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    have ht := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, h31] at ht
    have hr32 : register % 2 ^ 5 = register := Nat.mod_eq_of_lt (by omega)
    omega
  have hbeq : ((BitVec.ofNat 5 register) == BitVec.ofNat 5 31) = false := by
    rw [beq_eq_false_iff_ne]; exact hrd
  have h26ne : (26 : BitVec 5) ≠ (BitVec.ofNat 5 register) := by
    intro hh
    exact hr26 (ofNat5_eq_ofNat5 26 register (by decide) hrlt hh).symm
  have hT5 : (arm8LocBigT5 ms offset register).REG (BitVec.ofNat 5 register) = ms.PC := by
    rw [arm8LocBigT5_reg ms offset register register h26ne]
    rw [arm8LocBigT1_reg]
  have hXr : X (BitVec.ofNat 5 register) (arm8LocBigT5 ms offset register) = ms.PC := by
    simp only [X, hbeq, Bool.false_eq_true, ite_false, BitVec.setWidth_eq, hT5]
  have hbeq26 : ((26 : BitVec 5) == BitVec.ofNat 5 31) = false := by decide
  have hX26 : X (26 : BitVec 5) (arm8LocBigT5 ms offset register) = offset := by
    simp only [X, hbeq26, Bool.false_eq_true, ite_false, BitVec.setWidth_eq]
    exact arm8LocBigT5_reg26 ms offset register hr26 hrlt
  rw [arm8LocBigT6_reg_step, hXr, hX26]

theorem arm8LocBigT6_reg_ne (ms : arm8_state) (offset : BitVec 64) (register j : Nat)
    (h : (BitVec.ofNat 5 register) ≠ (BitVec.ofNat 5 j)) :
    (arm8LocBigT6 ms offset register).REG (BitVec.ofNat 5 j) =
      (arm8LocBigT5 ms offset register).REG (BitVec.ofNat 5 j) := by
  show Flapjack.RiscV.L3.holUpdate (BitVec.ofNat 5 register) _ (arm8LocBigT5 ms offset register).REG
    (BitVec.ofNat 5 j) = _
  simp only [Flapjack.RiscV.L3.holUpdate]
  exact ite_eq_right h


/-- Applying `arm8Next` to two states that agree on `d` and carry the final add
word gives states that still agree. -/
theorem arm8Next_locBigAdd_agree (d : BitVec 64 → Prop) (s t : arm8_state)
    (h : Arm8L3Agree d s t) (hok : arm8Ok s = true) (register : Nat)
    (hrd : register ≠ 31) (hlt : register < 32)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl 26 0 (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  refine arm8L3Agree_next h hok _ _ (fun u => arm8Next_locBigAdd u register hrd hlt) ?_ hf hb0 hb1 hb2 hb3
  have hrn : X (TN := 64) (BitVec.ofNat 5 register) s = X (TN := 64) (BitVec.ofNat 5 register) t :=
    arm8X_congr_or_zero h (BitVec.ofNat 5 register)
  have h26 : X (TN := 64) (26 : BitVec 5) s = X (TN := 64) (26 : BitVec 5) t :=
    arm8X_congr_or_zero h 26
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, hrn, h26]
  · simp [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]

/-- The out-of-range `Loc` constructor of `encoder_correct arm8TargetL3`: the
`Address` instruction, four `MoveWide .k` insertions of the offset into the
temporary register 26, and a final `AddSubShiftedRegister@64` write `PC +
offset` into the destination and advance `PC` by 24.  `hfalse` is the false
branch of HOL's own `Cases_on` on the `Loc` range test, not an added
hypothesis: `Complete.lean` splits on it exactly as HOL does, so the assembled
`arm8EncoderCorrectL3` assumes nothing. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_loc_big (register : Nat) (offset : BitVec 64)
    (hrange : arm8LocInRange offset = false)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.loc register offset) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.loc register offset) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change arm8Ok ms = true at hok
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hregok : asmRegOkExact register arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simp only [asmOkExact, arm8ConfigL3, Bool.and_eq_true] at hk
    exact hk.1
  obtain ⟨hr_lt, hr_av, hr_31⟩ := regOk_of_asmL3 hregok
  have hr26 : register ≠ 26 := by
    intro hh
    rw [hh] at hr_av
    simp [arm8ConfigL3] at hr_av
  have hrd5 : (BitVec.ofNat 5 register) ≠ (31 : BitVec 5) := by
    intro hh
    have h31 : (31 : BitVec 5).toNat = 31 := by decide
    have ht := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, h31] at ht
    have hr32 : register % 2 ^ 5 = register := Nat.mod_eq_of_lt (by omega)
    omega
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := aligned_of_holAligned ms.PC halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.loc register offset)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have henclen := arm8Enc_loc_big_length register offset hrange
  have hround0 : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 (0 : BitVec 64) ++ holWordExtract 2 1 0 (0 : BitVec 64))) = 0 := by
    rw [arm8AddressRoundtripBits]; simp
  have henc := arm8Enc_loc_big register offset hrange
  simp only [arm8LocBigAddrInsn, arm8LocBigMovInsn, arm8LocBigAddInsn,
    Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at henc
  rw [arm8EncodeBytes_address 0 (BitVec.ofNat 5 register) hround0] at henc
  simp only [arm8Encode_movK, arm8EncodeBytes_addSubShiftedRegister] at henc
  have hbyte (i : Nat) (hi : i < 24) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) = (arm8Enc (.loc register offset)).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [henclen]; exact hi)
  have hb0 : ms.MEM (ms.PC) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddressWord 0 (BitVec.ofNat 5 register) >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb8 : ms.MEM (ms.PC + 8) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    have hh := hbyte 8 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb9 : ms.MEM (ms.PC + 9) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    have hh := hbyte 9 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb10 : ms.MEM (ms.PC + 10) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    have hh := hbyte 10 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb11 : ms.MEM (ms.PC + 11) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    have hh := hbyte 11 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb12 : ms.MEM (ms.PC + 12) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    have hh := hbyte 12 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb13 : ms.MEM (ms.PC + 13) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    have hh := hbyte 13 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb14 : ms.MEM (ms.PC + 14) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    have hh := hbyte 14 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb15 : ms.MEM (ms.PC + 15) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    have hh := hbyte 15 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb16 : ms.MEM (ms.PC + 16) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    have hh := hbyte 16 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb17 : ms.MEM (ms.PC + 17) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    have hh := hbyte 17 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb18 : ms.MEM (ms.PC + 18) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    have hh := hbyte 18 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb19 : ms.MEM (ms.PC + 19) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    have hh := hbyte 19 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb20 : ms.MEM (ms.PC + 20) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 0).toNat) := by
    have hh := hbyte 20 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb21 : ms.MEM (ms.PC + 21) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 8).toNat) := by
    have hh := hbyte 21 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb22 : ms.MEM (ms.PC + 22) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 16).toNat) := by
    have hh := hbyte 22 (by norm_num)
    rw [henc] at hh
    simpa using hh
  have hb23 : ms.MEM (ms.PC + 23) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 24).toNat) := by
    have hh := hbyte 23 (by norm_num)
    rw [henc] at hh
    simpa using hh

  have hal4 : holAligned 2 (ms.PC + 4) = true := holAligned_add_four' ms.PC halign
  have hal8 : holAligned 2 (ms.PC + 8) = true := holAligned_add_eight' ms.PC halign
  have hal12 : holAligned 2 (ms.PC + 12) = true := holAligned_add_twelve' ms.PC halign
  have hal16 : holAligned 2 (ms.PC + 16) = true := holAligned_add_sixteen' ms.PC halign
  have hal20 : holAligned 2 (ms.PC + 20) = true := holAligned_add_twenty' ms.PC halign
  have hal24 : holAligned 2 (ms.PC + 24) = true := holAligned_add_twentyfour' ms.PC halign
  have hal4a : Aligned (TN := 64) (ms.PC + 4, 4) = true := aligned_of_holAligned _ hal4
  have hal8a : Aligned (TN := 64) (ms.PC + 8, 4) = true := aligned_of_holAligned _ hal8
  have hal12a : Aligned (TN := 64) (ms.PC + 12, 4) = true := aligned_of_holAligned _ hal12
  have hal16a : Aligned (TN := 64) (ms.PC + 16, 4) = true := aligned_of_holAligned _ hal16
  have hal20a : Aligned (TN := 64) (ms.PC + 20, 4) = true := aligned_of_holAligned _ hal20
  have hnext1 : arm8Next ms = arm8LocBigT1 ms register :=
    arm8Next_locBigT1 ms register hr_31 hr_lt hexc0 hround0 hal he0 hel hb0 hb1 hb2 hb3
  have hnext2 : arm8Next (arm8LocBigT1 ms register) = arm8LocBigT2 ms offset register :=
    arm8Next_locBigT2 ms offset register hexc0 hal4a he0 hel hb4 hb5 hb6 hb7
  have hnext3 : arm8Next (arm8LocBigT2 ms offset register) = arm8LocBigT3 ms offset register :=
    arm8Next_locBigT3 ms offset register hexc0 hal8a he0 hel hb8 hb9 hb10 hb11
  have hnext4 : arm8Next (arm8LocBigT3 ms offset register) = arm8LocBigT4 ms offset register :=
    arm8Next_locBigT4 ms offset register hexc0 hal12a he0 hel hb12 hb13 hb14 hb15
  have hnext5 : arm8Next (arm8LocBigT4 ms offset register) = arm8LocBigT5 ms offset register :=
    arm8Next_locBigT5 ms offset register hexc0 hal16a he0 hel hb16 hb17 hb18 hb19
  have hnext6 : arm8Next (arm8LocBigT5 ms offset register) = arm8LocBigT6 ms offset register :=
    arm8Next_locBigT6 ms offset register hr_31 hr_lt hexc0 hal20a he0 hel hb20 hb21 hb22 hb23
  have hok1 : arm8Ok (arm8LocBigT1 ms register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT1_pc]; exact hal4
  have hok2 : arm8Ok (arm8LocBigT2 ms offset register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT2_pc]; exact hal8
  have hok3 : arm8Ok (arm8LocBigT3 ms offset register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT3_pc]; exact hal12
  have hok4 : arm8Ok (arm8LocBigT4 ms offset register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT4_pc]; exact hal16
  have hok5 : arm8Ok (arm8LocBigT5 ms offset register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT5_pc]; exact hal20
  have hok6 : arm8Ok (arm8LocBigT6 ms offset register) = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [arm8LocBigT6_pc]; exact hal24
  have ht1b0 : (arm8LocBigT1 ms register).MEM (arm8LocBigT1 ms register).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 0).toNat) := hb4
  have ht1b1 : (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    rw [show (arm8LocBigT1 ms register).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_1]
    exact hb5
  have ht1b2 : (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    rw [show (arm8LocBigT1 ms register).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_2]
    exact hb6
  have ht1b3 : (arm8LocBigT1 ms register).MEM ((arm8LocBigT1 ms register).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    rw [show (arm8LocBigT1 ms register).PC = ms.PC + (4 : BitVec 64) from rfl, bv_add_4_3]
    exact hb7
  have ht2b0 : (arm8LocBigT2 ms offset register).MEM (arm8LocBigT2 ms offset register).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    rw [arm8LocBigT2_pc]; exact hb8
  have ht2b1 : (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    rw [arm8LocBigT2_pc, bv_add_8_1]; exact hb9
  have ht2b2 : (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    rw [arm8LocBigT2_pc, bv_add_8_2]; exact hb10
  have ht2b3 : (arm8LocBigT2 ms offset register).MEM ((arm8LocBigT2 ms offset register).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    rw [arm8LocBigT2_pc, bv_add_8_3]; exact hb11
  have ht3b0 : (arm8LocBigT3 ms offset register).MEM (arm8LocBigT3 ms offset register).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    rw [arm8LocBigT3_pc]; exact hb12
  have ht3b1 : (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    rw [arm8LocBigT3_pc, bv_add_12_1]; exact hb13
  have ht3b2 : (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    rw [arm8LocBigT3_pc, bv_add_12_2]; exact hb14
  have ht3b3 : (arm8LocBigT3 ms offset register).MEM ((arm8LocBigT3 ms offset register).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    rw [arm8LocBigT3_pc, bv_add_12_3]; exact hb15
  have ht4b0 : (arm8LocBigT4 ms offset register).MEM (arm8LocBigT4 ms offset register).PC = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 0).toNat) := by
    rw [arm8LocBigT4_pc]; exact hb16
  have ht4b1 : (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 1) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 8).toNat) := by
    rw [arm8LocBigT4_pc, bv_add_16_1]; exact hb17
  have ht4b2 : (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 2) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 16).toNat) := by
    rw [arm8LocBigT4_pc, bv_add_16_2]; exact hb18
  have ht4b3 : (arm8LocBigT4 ms offset register).MEM ((arm8LocBigT4 ms offset register).PC + 3) = BitVec.ofNat 8 ((arm8MoveWideWord .k (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) >>> 24).toNat) := by
    rw [arm8LocBigT4_pc, bv_add_16_3]; exact hb19
  have ht5b0 : (arm8LocBigT5 ms offset register).MEM (arm8LocBigT5 ms offset register).PC = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 0).toNat) := by
    rw [arm8LocBigT5_pc]; exact hb20
  have ht5b1 : (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 1) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 8).toNat) := by
    rw [arm8LocBigT5_pc, bv_add_20_1]; exact hb21
  have ht5b2 : (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 2) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 16).toNat) := by
    rw [arm8LocBigT5_pc, bv_add_20_2]; exact hb22
  have ht5b3 : (arm8LocBigT5 ms offset register).MEM ((arm8LocBigT5 ms offset register).PC + 3) = BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord false false ShiftType.lsl (26 : BitVec 5) (0 : BitVec 6) (BitVec.ofNat 5 register) (BitVec.ofNat 5 register) >>> 24).toNat) := by
    rw [arm8LocBigT5_pc, bv_add_20_3]; exact hb23

  have hdom1 : ∀ j, j < 4 → s1.memDomain ((arm8LocBigT1 ms register).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8LocBigT1 ms register).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (4 + j) := by
      rw [show (arm8LocBigT1 ms register).PC = ms.PC + (4 : BitVec 64) from rfl, hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have hdom2 : ∀ j, j < 4 → s1.memDomain ((arm8LocBigT2 ms offset register).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8LocBigT2 ms offset register).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (8 + j) := by
      rw [show (arm8LocBigT2 ms offset register).PC = ms.PC + (8 : BitVec 64) from
        arm8LocBigT2_pc ms offset register, hpc]
      exact bv_add_split s1.pc 8 j
    rw [h1]
    exact hdom (8 + j) (by omega)
  have hdom3 : ∀ j, j < 4 → s1.memDomain ((arm8LocBigT3 ms offset register).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8LocBigT3 ms offset register).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (12 + j) := by
      rw [show (arm8LocBigT3 ms offset register).PC = ms.PC + (12 : BitVec 64) from
        arm8LocBigT3_pc ms offset register, hpc]
      exact bv_add_split s1.pc 12 j
    rw [h1]
    exact hdom (12 + j) (by omega)
  have hdom4 : ∀ j, j < 4 → s1.memDomain ((arm8LocBigT4 ms offset register).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8LocBigT4 ms offset register).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (16 + j) := by
      rw [show (arm8LocBigT4 ms offset register).PC = ms.PC + (16 : BitVec 64) from
        arm8LocBigT4_pc ms offset register, hpc]
      exact bv_add_split s1.pc 16 j
    rw [h1]
    exact hdom (16 + j) (by omega)
  have hdom5 : ∀ j, j < 4 → s1.memDomain ((arm8LocBigT5 ms offset register).PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : (arm8LocBigT5 ms offset register).PC + BitVec.ofNat 64 j =
        s1.pc + BitVec.ofNat 64 (20 + j) := by
      rw [show (arm8LocBigT5 ms offset register).PC = ms.PC + (20 : BitVec 64) from
        arm8LocBigT5_pc ms offset register, hpc]
      exact bv_add_split s1.pc 20 j
    rw [h1]
    exact hdom (20 + j) (by omega)
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [henclen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 24 := by rw [← hupd]; simp [asmUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by intro x; rw [← hupd]; simp [asmUpd, updPc, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [← hupd]; simp [asmUpd, updPc, updReg]
  have hs2regs : ∀ k, s2.regs k = if k = register then s1.pc + offset else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, updPc, updReg]
  have hq : targetStateRel arm8TargetL3 s2 (arm8LocBigT6 ms offset register) := by
    refine ⟨hok6, ?_, ?_, ?_, ?_⟩
    · change (arm8LocBigT6 ms offset register).PC = s2.pc
      rw [arm8LocBigT6_pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → (arm8LocBigT6 ms offset register).MEM a = s2.mem a
      intro a ha
      rw [arm8LocBigT6_mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        (arm8LocBigT6 ms offset register).REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      have hk26 : k ≠ 26 := by
        intro hh
        have hc := hk.2
        rw [hh] at hc
        simp [arm8ConfigL3] at hc
      rw [hs2regs k]
      by_cases hkr : k = register
      · rw [hkr, ite_eq_left rfl]
        rw [arm8LocBigT6_reg ms offset register hr26 hr_lt hr_31]
        rw [← hpc]
      · have hne : (BitVec.ofNat 5 register) ≠ (BitVec.ofNat 5 k) := by
          intro hh
          exact hkr (ofNat5_eq_ofNat5 register k hr_lt hk32 hh).symm
        have hne26 : (26 : BitVec 5) ≠ (BitVec.ofNat 5 k) := by
          intro hh
          exact hk26 (ofNat5_eq_ofNat5 26 k (by decide) hk32 hh).symm
        rw [ite_eq_right hkr]
        rw [arm8LocBigT6_reg_ne ms offset register k hne]
        rw [arm8LocBigT5_reg ms offset register k hne26]
        rw [arm8LocBigT1_reg_ne ms register k hne]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  let T : Nat → arm8_state := fun k => match k with
    | 0 => ms
    | 1 => arm8LocBigT1 ms register
    | 2 => arm8LocBigT2 ms offset register
    | 3 => arm8LocBigT3 ms offset register
    | 4 => arm8LocBigT4 ms offset register
    | 5 => arm8LocBigT5 ms offset register
    | _ => arm8LocBigT6 ms offset register
  refine asmCaseChain _ 5 T s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ henclen
    ?_ ?_ ?_ ?_ ?_ hs2dom hq
  · intro k hk u hu
    interval_cases k
    · rw [hu.1 rfl, hnext1]
      exact Arm8L3Agree.refl _ _
    · have hh := arm8Next_movK_agree s1.memDomain u (arm8LocBigT1 ms register) (hu.2 (by decide))
        (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok1) (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat))
        (26 : BitVec 5) arm8TwentySix_ne_31 hdom1 ht1b0 ht1b1 ht1b2 ht1b3
      rw [hnext2] at hh
      exact hh
    · have hh := arm8Next_movK_agree s1.memDomain u (arm8LocBigT2 ms offset register) (hu.2 (by decide))
        (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok2) (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat))
        (26 : BitVec 5) arm8TwentySix_ne_31 hdom2 ht2b0 ht2b1 ht2b2 ht2b3
      rw [hnext3] at hh
      exact hh
    · have hh := arm8Next_movK_agree s1.memDomain u (arm8LocBigT3 ms offset register) (hu.2 (by decide))
        (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok3) (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat))
        (26 : BitVec 5) arm8TwentySix_ne_31 hdom3 ht3b0 ht3b1 ht3b2 ht3b3
      rw [hnext4] at hh
      exact hh
    · have hh := arm8Next_movK_agree s1.memDomain u (arm8LocBigT4 ms offset register) (hu.2 (by decide))
        (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok4) (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat))
        (26 : BitVec 5) arm8TwentySix_ne_31 hdom4 ht4b0 ht4b1 ht4b2 ht4b3
      rw [hnext5] at hh
      exact hh
    · have hh := arm8Next_locBigAdd_agree s1.memDomain u (arm8LocBigT5 ms offset register)
        (hu.2 (by decide)) (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok5) register
        hr_31 hr_lt hdom5 ht5b0 ht5b1 ht5b2 ht5b3
      rw [hnext6] at hh
      exact hh
  · intro k hk u hu x _
    interval_cases k
    · rw [hu.1 rfl, hnext1]
      rfl
    · have hu1 : Arm8L3Agree s1.memDomain u (arm8LocBigT1 ms register) := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdom1 _ ht1b0 ht1b1 ht1b2 ht1b3
      exact arm8Next_movK_mem u (BitVec.ofNat 2 0) (BitVec.ofNat 16 ((offset >>> 0).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31
        (hu1.exc.trans hexc0) b0 b1 b2 b3 (by rw [hu1.pc, arm8LocBigT1_pc ms register]; exact hal4a)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel) x
    · have hu1 : Arm8L3Agree s1.memDomain u (arm8LocBigT2 ms offset register) := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdom2 _ ht2b0 ht2b1 ht2b2 ht2b3
      exact arm8Next_movK_mem u (BitVec.ofNat 2 1) (BitVec.ofNat 16 ((offset >>> 16).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31
        (hu1.exc.trans hexc0) b0 b1 b2 b3 (by rw [hu1.pc, arm8LocBigT2_pc ms offset register]; exact hal8a)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel) x
    · have hu1 : Arm8L3Agree s1.memDomain u (arm8LocBigT3 ms offset register) := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdom3 _ ht3b0 ht3b1 ht3b2 ht3b3
      exact arm8Next_movK_mem u (BitVec.ofNat 2 2) (BitVec.ofNat 16 ((offset >>> 32).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31
        (hu1.exc.trans hexc0) b0 b1 b2 b3 (by rw [hu1.pc, arm8LocBigT3_pc ms offset register]; exact hal12a)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel) x
    · have hu1 : Arm8L3Agree s1.memDomain u (arm8LocBigT4 ms offset register) := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdom4 _ ht4b0 ht4b1 ht4b2 ht4b3
      exact arm8Next_movK_mem u (BitVec.ofNat 2 3) (BitVec.ofNat 16 ((offset >>> 48).toNat)) (26 : BitVec 5) arm8TwentySix_ne_31
        (hu1.exc.trans hexc0) b0 b1 b2 b3 (by rw [hu1.pc, arm8LocBigT4_pc ms offset register]; exact hal16a)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel) x
    · have hu1 : Arm8L3Agree s1.memDomain u (arm8LocBigT5 ms offset register) := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdom5 _ ht5b0 ht5b1 ht5b2 ht5b3
      rw [arm8Next_locBigAdd u register hr_31 hr_lt (hu1.exc.trans hexc0) b0 b1 b2 b3
        (by rw [hu1.pc, arm8LocBigT5_pc]; exact hal20a)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel)]
  · intro k h1 h2
    interval_cases k
    · exact hok1
    · exact hok2
    · exact hok3
    · exact hok4
    · exact hok5
  · intro k h1 h2
    interval_cases k
    · exact arm8LocBigT1_pc ms register
    · exact arm8LocBigT2_pc ms offset register
    · exact arm8LocBigT3_pc ms offset register
    · exact arm8LocBigT4_pc ms offset register
    · exact arm8LocBigT5_pc ms offset register
  · intro k h1 h2 x _
    interval_cases k <;> rfl

end Flapjack.Compiler.Encoders.Arm8.L3
