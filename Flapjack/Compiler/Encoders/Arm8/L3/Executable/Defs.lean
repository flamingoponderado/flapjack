import Flapjack.Compiler.Encoders.Arm8.L3.Configuration
import Flapjack.Compiler.Encoders.Arm8.Configuration

/-!
# Bridge infrastructure for the executed encoder

Shared lemmas used by `L3/Executable/` to compare the computable encoder
`Arm8.arm8Enc` of `Arm8/Target.lean` with the L3 rendering `L3.arm8Enc`.

Two kinds of fact live here:

* byte-carrier facts: `encodeBytes` emits the four little-endian bytes of the
  32-bit word produced by `encodeInsn32`;
* word-carrier facts: the `Nat`-valued truncation that `fields` performs in
  `Arm8/Encode.lean` moves onto the `BitVec` carrier, and `holWordExtract` is
  a truncated shift.  The `fields`/concatenation bridge itself is proved with
  the per-instruction lemmas in `L3/Executable/Encoder.lean`.

No HOL claim is introduced; these relate two Lean renderings of the same
instruction word.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The low eight bits at position `s` of a 32-bit word, after the 64-bit
carrier widening that `wordBytes` performs. -/
theorem extractLsb_setWidth_eq (w : BitVec 32) (s : Nat) :
    (w.setWidth 64).extractLsb' s 8 = BitVec.ofNat 8 ((w >>> s).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]
  rw [Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64)]

/-- The four little-endian bytes of a 32-bit word, as `encodeBytes` emits them
for the 64-bit carrier `wordBytes` uses. -/
theorem wordBytes_setWidth (w : BitVec 32) :
    wordBytes (w.setWidth 64) =
      [BitVec.ofNat 8 ((w >>> 0).toNat), BitVec.ofNat 8 ((w >>> 8).toNat),
       BitVec.ofNat 8 ((w >>> 16).toNat), BitVec.ofNat 8 ((w >>> 24).toNat)] := by
  simp only [wordBytes, extractLsb_setWidth_eq]
  rfl

/-- `encodeBytes` of an encodable instruction is the four little-endian bytes
of its 32-bit word. -/
theorem encodeBytes_eq_of_encodeInsn32 (i : Insn) (w : BitVec 32)
    (h : encodeInsn32 i = some w) :
    encodeBytes i =
      [BitVec.ofNat 8 ((w >>> 0).toNat), BitVec.ofNat 8 ((w >>> 8).toNat),
       BitVec.ofNat 8 ((w >>> 16).toNat), BitVec.ofNat 8 ((w >>> 24).toNat)] := by
  unfold encodeBytes encodeInsn
  rw [h]
  simp only [Option.map_some]
  exact wordBytes_setWidth w

/-- `encodeBytes` of a non-encodable instruction is four zero bytes; this is
the zero-bytes fallback arm of HOL's `arm8_encode`, not a claim that
`encodeInsn32` returns `none` exactly when the L3 `Encode` returns `BadCode`
(that correspondence is proved per instruction in `L3/Executable/Encoder.lean`). -/
theorem encodeBytes_eq_of_encodeInsn32_none (i : Insn)
    (h : encodeInsn32 i = none) : encodeBytes i = [0, 0, 0, 0] := by
  unfold encodeBytes encodeInsn
  rw [h]
  rfl

/-- A truncated `Nat` field, moved onto the `BitVec` carrier. -/
theorem ofNat_mod_setWidth (w : Nat) (v : Nat) :
    BitVec.ofNat 32 (v % 2 ^ w) = (BitVec.ofNat w v).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- `holWordExtract b h l w` is the low `b` bits of `w >>> l`, provided the
selected window covers those bits. -/
theorem holWordExtract_eq_setWidth (b : Nat) {a : Nat} (h l : Nat) (w : BitVec a)
    (hla : l + b ≤ a) (hh : l + b - 1 ≤ h) (hb : 1 ≤ b) :
    RiscV.L3.holWordExtract b h l w = (w >>> l).setWidth b := by
  unfold RiscV.L3.holWordExtract
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  have hK : min h (a - 1) + 1 - l = min h (a - 1) - l + 1 := by omega
  rw [hK]
  have hbK : b ≤ min h (a - 1) - l + 1 := by omega
  have hKa : min h (a - 1) - l + 1 ≤ a := by omega
  have hx : (w.toNat >>> l) % 2 ^ (min h (a - 1) - l + 1) < 2 ^ a := by
    have hle : 2 ^ (min h (a - 1) - l + 1) ≤ 2 ^ a :=
      Nat.pow_le_pow_right (by decide) hKa
    omega
  simp only [Nat.mod_eq_of_lt hx]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hbK)]

/-- `bit false = 0`. -/
@[simp] theorem bit_false : bit false = 0 := rfl

/-- `bit true = 1`. -/
@[simp] theorem bit_true : bit true = 1 := rfl

end Flapjack.Compiler.Encoders.Arm8
