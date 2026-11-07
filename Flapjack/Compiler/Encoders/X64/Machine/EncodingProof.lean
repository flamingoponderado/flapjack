import Mathlib.Tactic
import Flapjack.Compiler.Encoders.X64.Machine.Bytes
import Flapjack.Compiler.Encoders.AsmProps.Encoding

/-!
# `enc_ok` for the x86-64 assembler configuration

`x64_config`'s encoded length does not depend on a branch offset once `asm_ok`
holds: every jump is a `rel32` form, every `jumpCmp` has a fixed length, `call`
lowers to the one-byte failure encoding, and `loc` is a fixed seven-byte
`lea`.  This module proves CakeML's `enc_ok` (`asmPropsScript.sml:27-41`) at
`x64Config`, which is the first half of `target_ok`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm

/-! ## Non-empty encodings -/

/-- `x64_enc` is never empty: an empty lowering becomes the byte `[0]`. -/
theorem x64Enc_ne_nil (i : HolAsm 64) : x64Enc i ≠ [] := by
  unfold x64Enc
  cases List.flatMap encodeInsn (x64Ast i) with
  | nil => simp
  | cons x xs => simp

/-- Every encoded instruction has non-zero length. -/
theorem x64Enc_length_pos (i : HolAsm 64) : 0 < (x64Enc i).length := by
  have := x64Enc_ne_nil i
  exact List.length_pos_iff.mpr this

/-! ## Range facts -/

/-- `x64_min32 + 13` is `-2^31 + 13` as a signed 64-bit value. -/
theorem x64Min32_add_13 : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by
  decide

/-- `x64_max32 + 5` is `2^31 - 1 + 5` as a signed 64-bit value. -/
theorem x64Max32_add_5 : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by
  decide

/-- A word in the x86-64 jump-offset range, shifted by `-5`, lies in the signed
32-bit range. -/
theorem jump_offset_sub_five (w : BitVec 64)
    (hlo : (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 5).toInt ∧ (w - 5).toInt < 2^31 := by
  have hlo' : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by decide
  have hhi' : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 5 : BitVec 64).toInt = w.toInt - 5 := by
    rw [BitVec.toInt_sub]
    have h5 : ((5 : BitVec 64).toInt : Int) = 5 := by decide
    rw [h5]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-- A word in the x86-64 `Loc` range, shifted by `-7`, lies in the signed
32-bit range. -/
theorem loc_offset_sub_seven (w : BitVec 64)
    (hlo : (x64Min32 + 7 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 7 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 7).toInt ∧ (w - 7).toInt < 2^31 := by
  have hlo' : (x64Min32 + 7 : BitVec 64).toInt = -(2^31 : Int) + 7 := by decide
  have hhi' : (x64Max32 + 7 : BitVec 64).toInt = (2^31 : Int) - 1 + 7 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 7 : BitVec 64).toInt = w.toInt - 7 := by
    rw [BitVec.toInt_sub]
    have h7 : ((7 : BitVec 64).toInt : Int) = 7 := by decide
    rw [h7]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-- The range facts `asm_ok` gives a jump offset. -/
theorem jump_offset_range (w : BitVec 64)
    (h : asmJumpOffsetOkExact x64Config w = true) :
    (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt ∧
      w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt := by
  simp only [asmJumpOffsetOkExact, asmOffsetOkExact, x64Config, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2⟩

/-- The range facts `asm_ok` gives a `Loc` offset. -/
theorem loc_offset_range (w : BitVec 64)
    (h : asmLocOffsetOkExact x64Config w = true) :
    (x64Min32 + 7 : BitVec 64).toInt ≤ w.toInt ∧
      w.toInt ≤ (x64Max32 + 7 : BitVec 64).toInt := by
  simp only [asmLocOffsetOkExact, asmOffsetOkExact, x64Config, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2⟩

/-! ## `e_imm32` succeeds on the jump and `Loc` offsets -/

/-- `e_imm32` succeeds on an offset in the signed 32-bit range. -/
theorem eImm32_some {imm : BitVec 64}
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    ∃ l, eImm32 imm = some l := by
  unfold eImm32
  rw [ite_eq_left]
  · exact ⟨_, rfl⟩
  · omega

/-- A successful `e_imm32` is four bytes. -/
theorem eImm32_length {imm : BitVec 64} {l : List (BitVec 8)} (h : eImm32 imm = some l) :
    l.length = 4 := by
  unfold eImm32 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp
  · simp at h

/-! ## Encoded lengths -/

/-- `x64_enc` of a jump is the five-byte `rel32` form under `asm_ok`. -/
theorem x64Enc_jump_length (w : BitVec 64)
    (h : asmOkExact (.jump w) x64Config = true) :
    (x64Enc (.jump w)).length = 5 := by
  have hok : asmJumpOffsetOkExact x64Config w = true := by simpa [asmOkExact] using h
  obtain ⟨hlo, hhi⟩ := jump_offset_range w hok
  have hr := jump_offset_sub_five w hlo hhi
  obtain ⟨l, hl⟩ := eImm32_some hr.1 hr.2
  simp only [x64Enc, x64Ast, List.flatMap_cons, List.flatMap_nil, encodeInsn]
  rw [hl]
  simp [eImm32_length hl]

/-- `x64_enc` of a call is the one-byte failure encoding. -/
theorem x64Enc_call_length (w : BitVec 64) :
    (x64Enc (.call w)).length = 1 := by
  simp [x64Enc, x64Ast]

/-- `x64_enc` of a `Loc` is the fixed seven-byte `lea` under `asm_ok`. -/
theorem x64Enc_loc_length (r : Nat) (w : BitVec 64)
    (h : asmOkExact (.loc r w) x64Config = true) :
    (x64Enc (.loc r w)).length = 7 := by
  have hok : asmLocOffsetOkExact x64Config w = true :=
    (by simpa [asmOkExact] using h : asmRegOkExact r x64Config = true ∧
      asmLocOffsetOkExact x64Config w = true).2
  obtain ⟨hlo, hhi⟩ := loc_offset_range w hok
  have hr := loc_offset_sub_seven w hlo hhi
  obtain ⟨l, hl⟩ := eImm32_some hr.1 hr.2
  simp only [x64Enc, x64Ast, List.flatMap_cons, List.flatMap_nil, encodeInsn, eGenRmReg,
    eModRM, eOpsize, rexPrefix, mkRex]
  rw [hl]
  simp [eImm32_length hl]

/-! ## Conditional-jump lengths -/

/-- The x86-64 comparison mapping never produces the parity or unconditional
condition codes, so a `jumpCmp` branch is always the long `rel32` form. -/
theorem x64Cmp_ne_zP (op : Cmp) : x64Cmp op ≠ .zP := by cases op <;> decide

theorem x64Cmp_ne_zAlways (op : Cmp) : x64Cmp op ≠ .zAlways := by cases op <;> decide

/-- A long conditional branch is six bytes. -/
theorem encodeInsn_jcc_long (cond : ZCond) (imm : BitVec 64)
    (hp : cond ≠ .zP) (ha : cond ≠ .zAlways)
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    (encodeInsn (.jcc cond imm)).length = 6 := by
  simp only [encodeInsn]
  rw [ite_eq_right ha, ite_eq_right hp]
  obtain ⟨l, hl⟩ := eImm32_some h1 h2
  rw [hl]
  simp [eImm32_length hl]

/-- A successful `e_imm32` has four bytes. -/
theorem eImm32_length' {imm : BitVec 64} {l : List (BitVec 8)} (h : eImm32 imm = some l) :
    l.length = 4 := eImm32_length h

end Flapjack.Compiler.Encoders.X64

