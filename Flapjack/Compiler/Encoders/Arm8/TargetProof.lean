import Flapjack.Compiler.Encoders.Arm8.Target

/-! Structural facts about the ARMv8 encoder.

`arm8_targetProofScript.sml` begins with length lemmas for `arm8_encode` and `arm8_enc`
(`length_arm8_encode`, `length_arm8_enc`, `arm8_encode_not_nil`, `arm8_encoding`) before
the state-transition proof of `arm8_encoder_correct`.  This module also contains the
first semantic helper lemmas, `Decode_EncodeBitMask` (word64 conjunct) and `mul_long`.
None of these declarations is tagged as an exact HOL port: HOL's structural lemmas range
over the full L3 `arm8$instruction` datatype, while `Insn` here is the subset that
`arm8_ast` emits, `encodeBytes` replaces HOL's `arm8_encode` `BadCode` result with its
four zero bytes, and the bitmask/product helpers use Flapjack's `Nat` and `BitVec`
carriers instead of HOL's word/bitstring operations.

The main `arm8_encoder_correct` theorem is not ported: it needs the ARMv8 L3 machine
semantics (`arm8Script.sml` and `arm8_stepScript.sml`), which Flapjack does not yet
contain.  Source-to-assembly parity is checked instead by
`Flapjack/Test/Arm8Parity.lean`. -/
namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `arm8_encode` produces exactly four bytes for every instruction, including the
`BadCode` case (four zero bytes). -/
theorem length_encodeBytes (i : Insn) : (encodeBytes i).length = 4 := by
  unfold encodeBytes
  split <;> simp [wordBytes]

/-- `length_arm8_enc` for a list of lowered instructions. -/
theorem length_flatMap_encodeBytes (instructions : List Insn) :
    (instructions.flatMap encodeBytes).length = 4 * instructions.length := by
  induction instructions with
  | nil => simp
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.length_append, length_encodeBytes, ih,
        List.length_cons, Nat.mul_succ]
      omega

/-- `length_arm8_enc`: the lowered byte sequence has length four times the number of
lowered instructions. -/
theorem length_arm8Enc (instruction : HolAsm 64) :
    (arm8Enc instruction).length = 4 * (arm8Ast instruction).length := by
  rw [arm8Enc]
  exact length_flatMap_encodeBytes _

/-- `arm8_encode_not_nil`: every instruction encodes to a nonempty byte list. -/
theorem encodeBytes_not_nil (i : Insn) : encodeBytes i ≠ [] := by
  intro empty
  have length := length_encodeBytes i
  rw [empty] at length
  simp at length

/-- `Decode_EncodeBitMask`, word64 conjunct.  `decodeBitMasks` returns `(wmask, tmask)`
as `Nat`s, so the decoded word is stated as `w.toNat` and `v` is the T mask.  Only the
word64 half of the HOL conjunction is stated, because the Lean encoder is fixed at width
64.  The carrier difference is why this is not tagged as an exact HOL port. -/
theorem decodeEncodeBitMask (w : W) (n s r : Nat)
    (h : encodeBitMask w = some (n, s, r)) :
    ∃ v, decodeBitMasks n s r true = some (w.toNat, v) := by
  simp only [encodeBitMask] at h
  split at h <;> simp_all

/-- `mul_long`: the high 64 bits of the 128-bit product, stated over `BitVec` rather
than HOL's `word128`/`w2w`/`extract`. -/
theorem mulLong (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat * b.toNat) / 2^64) =
      ((a.zeroExtend 128) * (b.zeroExtend 128)).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    Nat.shiftRight_eq_div_pow]
  have ha : a.toNat < 2^128 := by omega
  have hb : b.toNat < 2^128 := by omega
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hlt : a.toNat * b.toNat < 2^128 := by
    calc
      a.toNat * b.toNat < 2^64 * 2^64 := Nat.mul_lt_mul'' a.isLt b.isLt
      _ = 2^128 := by rw [show 128 = 64 + 64 by rfl, Nat.pow_add]
  rw [Nat.mod_eq_of_lt hlt]

/-- The `LENGTH l MOD 4 = 0` half of `arm8_encoding`, for the lowered byte list. -/
theorem length_arm8Enc_mod (instruction : HolAsm 64) :
    (arm8Enc instruction).length % 4 = 0 := by
  rw [length_arm8Enc]
  omega

end Flapjack.Compiler.Encoders.Arm8
