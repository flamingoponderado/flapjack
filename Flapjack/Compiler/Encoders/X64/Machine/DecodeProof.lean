module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.Bytes

@[expose] public section

/-!
# Decoder inverses for the emitted x86-64 instruction forms

For every instruction form `x64_ast` emits, the closed decoder recovers an
instruction with the same register fields and immediate values, together with
the encoded length.  Byte-register forms may recover `Z8 true` where the source
form carries `Z8 false` (a REX prefix forced by the base or source register):
the executor ignores that flag, so the two forms execute identically.
-/

namespace Flapjack.Compiler.Encoders.X64

/-! ## Simple opcodes -/

@[simp] theorem decode_nop_one :
    decode (byteListReader (encodeInsn (.nop 1))) = some (.nop 1, 1) := by
  simp [encodeInsn, decode, decodeNoRex]

@[simp] theorem decode_cmc :
    decode (byteListReader (encodeInsn .cmc)) = some (.cmc, 1) := by
  simp [encodeInsn, decode, decodeNoRex]

/-! ## Register-to-register moves -/

theorem decode_movRR_z64 (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.movRR .z64 dst src))) =
      some (.movRR .z64 dst src, 3) := by
  interval_cases dst <;> interval_cases src <;> decide

theorem decode_movRR_z32 (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.movRR .z32 dst src))) =
      some (.movRR .z32 dst src, 2 + (if src / 8 = 1 ∨ dst / 8 = 1 then 1 else 0)) := by
  interval_cases dst <;> interval_cases src <;> decide

theorem decode_movRR_z16 (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.movRR .z16 dst src))) =
      some (.movRR .z16 dst src, 3 + (if src / 8 = 1 ∨ dst / 8 = 1 then 1 else 0)) := by
  interval_cases dst <;> interval_cases src <;> decide

theorem decode_movRR_z8 (hr : Bool) (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.movRR (.z8 hr) dst src))) =
      some (.movRR (.z8 (hr || src / 8 = 1 || dst / 8 = 1)) dst src,
        2 + (if hr || src / 8 = 1 || dst / 8 = 1 then 1 else 0)) := by
  interval_cases dst <;> interval_cases src <;> cases hr <;> decide

/-! ## Immediate moves -/

set_option maxHeartbeats 8000000 in
theorem decode_movRI_z32 (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movRI .z32 dst imm))) =
      some (.movRI .z32 dst imm, 5 + (if 8 ≤ dst then 1 else 0)) := by
  have hp : (-2147483648 : Int) ≤ imm.toInt := by norm_num at h1 ⊢; exact h1
  have hq : imm.toInt ≤ 2147483647 := by omega
  interval_cases dst
  all_goals
    simp only [encodeInsn, eOpsizeImm, eOpsize, rexPrefix, mkRex, eImm32, eImm8,
      show ZSize.z32 ≠ ZSize.z64 from by decide]
    simp [hp, hq]
    unfold decode decodeNoRex decodeRex movImm
    dsimp only
    simp only [byteListReader_cons_zero, byteListReader_cons_succ, byte_toNat, Nat.reduceMod]
    simp
    rw [imm32_eImm32_at imm _ _ (by intro j hj; interval_cases j <;> simp) h1 h2]

set_option maxHeartbeats 8000000 in
theorem decode_movRI_z64 (dst : Nat) (hd : dst < 16) (imm : BitVec 64) :
    decode (byteListReader (encodeInsn (.movRI .z64 dst imm))) =
      some (.movRI .z64 dst imm, 10) := by
  interval_cases dst
  all_goals
    simp only [encodeInsn, eOpsizeImm, eOpsize, rexPrefix, mkRex, eImm32, eImm8, eImm64]
    simp
    unfold decode decodeNoRex decodeRex movImm
    dsimp only
    simp only [byteListReader_cons_zero, byteListReader_cons_succ, byte_toNat, Nat.reduceMod]
    simp
    rw [le64_at imm _ _ (by intro j hj; interval_cases j <;> simp)]

/-! ## Unary and multiply/divide -/

theorem decode_monop_z64 (op : ZMonopName) (dst : Nat) (hd : dst < 16) :
    decode (byteListReader (encodeInsn (.monop op .z64 dst))) =
      some (.monop op .z64 dst, (encodeInsn (.monop op .z64 dst)).length) := by
  cases op <;> interval_cases dst <;> decide

theorem decode_mul_z64 (src : Nat) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.mul .z64 src))) =
      some (.mul .z64 src, (encodeInsn (.mul .z64 src)).length) := by
  interval_cases src <;> decide

theorem decode_div_z64 (src : Nat) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.div .z64 src))) =
      some (.div .z64 src, (encodeInsn (.div .z64 src)).length) := by
  interval_cases src <;> decide

theorem decode_jmp (dst : Nat) (hd : dst < 16) :
    decode (byteListReader (encodeInsn (.jmp dst))) =
      some (.jmp dst, (encodeInsn (.jmp dst)).length) := by
  interval_cases dst <;> decide

theorem decode_setcc (cond : ZCond) (dst : Nat) (hd : dst < 16) (hc : cond ≠ .zAlways) :
    decode (byteListReader (encodeInsn (.setcc cond true dst))) =
      some (.setcc cond true dst, (encodeInsn (.setcc cond true dst)).length) := by
  cases cond <;> first | exact absurd rfl hc | (interval_cases dst <;> decide)

/-! ## Register-register arithmetic -/

theorem decode_binopRR_z64 (op : ZBinopName) (dst src : Nat) (hd : dst < 16) (hs : src < 16)
    (hop : op.code < 8) :
    decode (byteListReader (encodeInsn (.binopRR op .z64 dst src))) =
      some (.binopRR op .z64 dst src, (encodeInsn (.binopRR op .z64 dst src)).length) := by
  cases op <;> simp [ZBinopName.code] at hop <;> interval_cases dst <;> interval_cases src <;> decide

theorem decode_binopRR_z32 (op : ZBinopName) (dst src : Nat) (hd : dst < 16) (hs : src < 16)
    (hop : op.code < 8) :
    decode (byteListReader (encodeInsn (.binopRR op .z32 dst src))) =
      some (.binopRR op .z32 dst src, (encodeInsn (.binopRR op .z32 dst src)).length) := by
  cases op <;> simp [ZBinopName.code] at hop <;> interval_cases dst <;> interval_cases src <;> decide

theorem decode_binopRR_test (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.binopRR .ztest .z64 dst src))) =
      some (.binopRR .ztest .z64 dst src, (encodeInsn (.binopRR .ztest .z64 dst src)).length) := by
  interval_cases dst <;> interval_cases src <;> decide

theorem decode_binopRR_shift (op : ZBinopName) (dst : Nat) (hd : dst < 16)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) :
    decode (byteListReader (encodeInsn (.binopRR op .z64 dst 1))) =
      some (.binopRR op .z64 dst 1, (encodeInsn (.binopRR op .z64 dst 1)).length) := by
  rcases hop with h|h|h|h <;> subst h <;> interval_cases dst <;> decide

end Flapjack.Compiler.Encoders.X64
