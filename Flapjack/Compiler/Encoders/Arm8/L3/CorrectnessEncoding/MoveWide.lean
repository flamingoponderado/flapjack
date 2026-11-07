import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Infrastructure

set_option maxHeartbeats 4000000

/-!
# L3 ARMv8 `MoveWide` encode/decode inverses

The decoder-inverse building block for the `Const` case of
`encoder_correct arm8TargetL3`: the word emitted by `Encode` for
`MoveWide@64 (1, opc, hw, imm16, rd)` decodes back to that instruction.  The
guard bits are fixed by the encoding (bit 31 = 1, bits 28-23 = `100101`), so
the full rendered `Decode` reduces on the symbolic word once the concatenated
bit fields are normalized.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- The 32-bit word `Encode` emits for `MoveWide@64 (1, opc, hw, imm16, rd)`. -/
def arm8MoveWideWord (opc : MoveWideOp) (hw : BitVec 2) (imm16 : BitVec 16)
    (rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 1 1) ++
    (BitVec.setWidth 31 (((match opc with
        | .n => (BitVec.ofNat 2 0) | .z => (BitVec.ofNat 2 2) | .k => (BitVec.ofNat 2 3))) ++
      (BitVec.setWidth 29 ((BitVec.ofNat 6 37) ++
        (BitVec.setWidth 23 (hw ++ (BitVec.setWidth 21 (imm16 ++ rd)))))))))

/-- `Encode` of `MoveWide@64` is the documented word. -/
theorem arm8Encode_moveWide (opc : MoveWideOp) (hw : BitVec 2) (imm16 : BitVec 16)
    (rd : BitVec 5) :
    Encode (instruction.Data (Data.«MoveWide@64» (1, opc, hw, imm16, rd))) =
      MachineCode.ARM8 (arm8MoveWideWord opc hw imm16 rd) := by
  simp only [Encode, e_data, arm8MoveWideWord]
  rfl

/-- `holV2w` inverts `holW2v` (Flapjack infrastructure for the bitstring/FCP
rendering). -/
theorem holV2w_holW2v {n : Nat} [NeZero n] (w : BitVec n) :
    holV2w n (holW2v w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holV2w, Flapjack.RiscV.L3.holV2w]
  rw [Flapjack.getLsbD_holFcpWord]
  simp only [holW2v, List.length_map, List.length_range, hi, decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  simp only [Option.map_some, Option.getD_some]
  rw [show n - 1 - (n - 1 - i) = i by omega]
  omega

/-- Two-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_two (w : BitVec 2) : holV2w 2 [w[1], w[0]] = w := by
  exact holV2w_holW2v w

/-- Five-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_five (w : BitVec 5) :
    holV2w 5 [w[4], w[3], w[2], w[1], w[0]] = w := by
  exact holV2w_holW2v w

/-- Nineteen-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_nineteen (w : BitVec 19) :
    holV2w 19 [w[18], w[17], w[16], w[15], w[14], w[13], w[12], w[11], w[10], w[9], w[8], w[7],
      w[6], w[5], w[4], w[3], w[2], w[1], w[0]] = w := by
  exact holV2w_holW2v w

/-- Sixteen-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_sixteen (w : BitVec 16) :
    holV2w 16 [w[15], w[14], w[13], w[12], w[11], w[10], w[9], w[8], w[7], w[6], w[5], w[4], w[3],
      w[2], w[1], w[0]] = w := by
  exact holV2w_holW2v w

theorem holV2w_one_true : holV2w 1 [true] = (1 : BitVec 1) := by decide
/-- One-bit roundtrip for the `0` bit list. -/
theorem holV2w_one_false : holV2w 1 [false] = (0 : BitVec 1) := by decide
theorem holV2w_two_zero : holV2w 2 [false, false] = (0 : BitVec 2) := by decide
theorem holV2w_two_two : holV2w 2 [true, false] = (2 : BitVec 2) := by decide
theorem holV2w_two_three : holV2w 2 [true, true] = (3 : BitVec 2) := by decide

/-- The rendered `Decode` inverts `arm8MoveWideWord`. -/
theorem arm8Decode_moveWide (opc : MoveWideOp) (hw : BitVec 2) (imm16 : BitVec 16)
    (rd : BitVec 5) :
    Decode (arm8MoveWideWord opc hw imm16 rd) =
      instruction.Data (Data.«MoveWide@64» (1, opc, hw, imm16, rd)) := by
  simp only [arm8MoveWideWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases opc <;> simp [holV2w_one_true, holV2w_two_zero, holV2w_two_two,
    holV2w_two_three, holV2w_two, holV2w_five, holV2w_sixteen]

/-- Inserting a 16-bit immediate into the zero word at `pos` is a left shift
(Flapjack infrastructure for the bitstring/FCP `bit_field_insert` rendering). -/
theorem holBitFieldInsert_zero_shift (pos : Nat) (imm16 : BitVec 16) :
    holBitFieldInsert (pos + 15) pos imm16 (BitVec.ofNat 64 0) =
      (BitVec.setWidth 64 imm16) <<< pos := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holBitFieldInsert, Flapjack.RiscV.L3.holBitFieldInsert]
  rw [Flapjack.getLsbD_holFcpWord]
  simp only [hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h1 : i < pos
  · simp [h1]
  · by_cases h2 : i ≤ pos + 15
    · have hp : pos ≤ i := by omega
      have hc : i - pos < 64 := by omega
      simp [h1, h2, hp, hc]
    · have h3 : 16 ≤ i - pos := by omega
      rw [BitVec.getLsbD_of_ge imm16 (i - pos) h3]
      simp [h1, h2]

/-- `Run` of `MoveWide@64` with opcode `z`: write the shifted immediate. -/
theorem arm8Run_moveWide_z (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5)
    (s : arm8_state) :
    Run (instruction.Data (Data.«MoveWide@64» (1, .z, hw, imm16, rd))) s =
      if rd = 31 then s else
        { s with REG := holUpdate rd ((BitVec.setWidth 64 imm16) <<< (hw.toNat * 16)) s.REG } := by
  simp only [Run, «dfn'MoveWide», «write'X»]
  simp only [show (MoveWideOp.z == MoveWideOp.n) = false from by decide,
    show (MoveWideOp.z == MoveWideOp.k) = false from by decide]
  simp only [Bool.false_eq_true, ite_false]
  have hpos : (BitVec.setWidth 6 (hw ++ (BitVec.ofNat 4 0))).toNat = hw.toNat * 16 := by
    rw [BitVec.setWidth_eq, BitVec.toNat_append]
    simp [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [hpos]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [holBitFieldInsert_zero_shift (hw.toNat * 16) imm16]
  simp

/-- `Run` of `MoveWide@64` with opcode `n`: write the complemented shifted
immediate. -/
theorem arm8Run_moveWide_n (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5)
    (s : arm8_state) :
    Run (instruction.Data (Data.«MoveWide@64» (1, .n, hw, imm16, rd))) s =
      if rd = 31 then s else
        { s with REG :=
            (holUpdate rd (~~~((BitVec.setWidth 64 imm16) <<< (hw.toNat * 16))) s.REG) } := by
  simp only [Run, «dfn'MoveWide», «write'X»]
  simp only [show (MoveWideOp.n == MoveWideOp.n) = true from by decide,
    show (MoveWideOp.n == MoveWideOp.k) = false from by decide]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  have hpos : (BitVec.setWidth 6 (hw ++ (BitVec.ofNat 4 0))).toNat = hw.toNat * 16 := by
    rw [BitVec.setWidth_eq, BitVec.toNat_append]
    simp [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [hpos]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [holBitFieldInsert_zero_shift (hw.toNat * 16) imm16]
  simp

/-- `Run` of `MoveWide@64` with opcode `k`: insert the immediate into the
existing register value. -/
theorem arm8Run_moveWide_k (hw : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5)
    (s : arm8_state) :
    Run (instruction.Data (Data.«MoveWide@64» (1, .k, hw, imm16, rd))) s =
      if rd = 31 then s else
        { s with REG :=
            (holUpdate rd (holBitFieldInsert (hw.toNat * 16 + 15) (hw.toNat * 16) imm16 (X rd s)) s.REG) } := by
  simp only [Run, «dfn'MoveWide», «write'X»]
  simp only [show (MoveWideOp.k == MoveWideOp.n) = false from by decide,
    show (MoveWideOp.k == MoveWideOp.k) = true from by decide]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  have hpos : (BitVec.setWidth 6 (hw ++ (BitVec.ofNat 4 0))).toNat = hw.toNat * 16 := by
    rw [BitVec.setWidth_eq, BitVec.toNat_append]
    simp [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [hpos]
  simp only [BitVec.ofNat_eq_ofNat] at *
  simp


end Flapjack.Compiler.Encoders.Arm8.L3
