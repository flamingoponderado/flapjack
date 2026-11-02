import Flapjack.Compiler.Encoders.Arm8.L3.Configuration

set_option maxHeartbeats 4000000

/-!
# L3 ARMv8 encoder correctness: the `Skip` reductions

The concrete reductions needed by the `encoder_correct arm8TargetL3` `Skip`
case, mirroring `Flapjack/RiscV/CorrectnessEncoding/Skip.lean`:

* `arm8Ast_skip` / `arm8Enc_skip`: `Skip` lowers to `NoOperation` and encodes
  to the AArch64 `NOP` word `0xD503201F` (little-endian bytes `1F 20 03 D5`).
* `arm8Decode_nop`: the full rendered `Decode` returns
  `Hint SystemHintOp_NOP` on that word.
* `arm8Run_nop`: the full rendered `Run` leaves the state unchanged for
  `Hint SystemHintOp_NOP`.
* `arm8Mem_nop` / `arm8Fetch_nop`: the rendered `Mem`/`Fetch` read the four
  emitted bytes (through `holFor`, `CheckAlignment` and `BigEndian`) and
  return the `NOP` word without changing the state.
* `arm8Next_nop`: `NextStateARM8` advances the PC by four and clears
  `branch_hint`, returning `some`.

The remaining `Skip` obligations are the `asmStep`/`targetStateRel`
simulation under interference (`asserts`/`asserts2`) and the post-state
relation; they are not proved here.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- `Skip` lowers to the `NoOperation` instruction. -/
theorem arm8Ast_skip : arm8Ast (HolAsm.inst HolInst.skip) = [NoOperation] := rfl

/-- `NoOperation` encodes to the AArch64 `NOP` bytes. -/
theorem arm8Encode_nop : arm8Encode NoOperation =
    [BitVec.ofNat 8 31, BitVec.ofNat 8 32, BitVec.ofNat 8 3, BitVec.ofNat 8 213] := by
  simp [arm8Encode, Encode, NoOperation, SystemHintOp2num]

/-- `Skip` encodes to the AArch64 `NOP` bytes. -/
theorem arm8Enc_skip : arm8Enc (HolAsm.inst HolInst.skip) =
    [BitVec.ofNat 8 31, BitVec.ofNat 8 32, BitVec.ofNat 8 3, BitVec.ofNat 8 213] := by
  simp [arm8Enc, arm8Ast_skip, arm8Encode_nop]

/-- The rendered L3 `Decode` returns `Hint NOP` on the emitted `NOP` word. -/
theorem arm8Decode_nop :
    Decode (BitVec.ofNat 32 0xD503201F) =
      instruction.Hint SystemHintOp.SystemHintOp_NOP := by
  simp [Decode, boolify32]
  intro _ _
  have h3 : holV2w 3 [false, false, false] = (0 : BitVec 3) := by decide
  rw [h3]
  simp [num2SystemHintOp]

/-- The rendered L3 `Run` leaves the state unchanged for `Hint NOP`. -/
theorem arm8Run_nop (s : arm8_state) :
    Run (instruction.Hint SystemHintOp.SystemHintOp_NOP) s = s := by
  simp [Run, «dfn'Hint»]

/-- A valid alignment makes `CheckAlignment` leave the state unchanged
(Flapjack infrastructure; no separate HOL theorem). -/
theorem CheckAlignment_aligned (ms : arm8_state) (a : BitVec 64) (sz : Nat)
    (t : AccType) (w : Bool) (h : Aligned (TN := 64) (a, sz) = true) :
    CheckAlignment (a, (sz, (t, w))) ms = ms := by
  simp [CheckAlignment, h]

/-- Little-endian mode is off at EL0 with `SCTLR_EL1.E0E` clear (Flapjack
infrastructure; the HOL `BigEndian` clause). -/
theorem BigEndian_false (ms : arm8_state) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (he0 : ms.SCTLR_EL1.E0E = false) : BigEndian ms = false := by
  simp [BigEndian, hel, he0]

/-- `Mem` reads the four emitted `NOP` bytes and returns `0xD503201F` without
changing the state. -/
theorem arm8Mem_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 32) (ms.PC, (4, AccType.AccType_IFETCH)) ms =
      (BitVec.ofNat 32 0xD503201F, ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false, BitVec.ofNat_eq_ofNat] at *
    rw [h0, h1, h2, h3]
    decide
  · exact CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal

/-- `Fetch` reads the four emitted `NOP` bytes. -/
theorem arm8Fetch_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Fetch ms = (BitVec.ofNat 32 0xD503201F, ms) := by
  simp only [Fetch]
  exact arm8Mem_nop ms h0 h1 h2 h3 hal he0 hel

/-- One `NextStateARM8` step on a state holding the emitted `NOP` bytes advances
the PC by four and clears `branch_hint`. -/
theorem arm8Next_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hexc : ms.exception = exception.NoException) :
    NextStateARM8 ms = some { ms with branch_hint := none, PC := ms.PC + 4 } := by
  have hfetch := arm8Fetch_nop { ms with branch_hint := none } h0 h1 h2 h3 hal he0 hel
  simp only [Next, NextStateARM8]
  rw [hfetch]
  simp [arm8Decode_nop, arm8Run_nop, hexc]

end Flapjack.Compiler.Encoders.Arm8.L3
