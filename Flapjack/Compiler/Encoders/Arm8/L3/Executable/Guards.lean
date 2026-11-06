import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Defs

/-!
# Guards of the computable ARMv8 encoder

`Arm8/Encode.lean` tests immediates with `fitsSigned n v`, which compares
`v.toInt` with Flapjack's `Nat`-valued `sextValue`; the L3 `Encode` instead
requires `v` to be the `BitVec.signExtend` of its own low `n` bits.  This
module proves the two tests are the same proposition, which is what lets each
per-instruction bridge reuse the reviewed L3 `arm8Encode_*` theorems under the
computable encoder's guard.

No new HOL claim is introduced: the lemmas relate two Lean renderings of the
same signed-range test.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8

/-- The signed value of the low `n` bits of `x` is the `toInt` of its `n`-bit
truncation: Flapjack's `sextValue` and `BitVec.toInt` agree. -/
theorem ofNat_toInt_sextValue (n : Nat) (hn : 1 ≤ n) (x : Nat) :
    (BitVec.ofNat n x).toInt = sextValue n x := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [Nat.pow_succ, Nat.mul_comm]
  rw [BitVec.toInt_eq_msb_cond, BitVec.toNat_ofNat]
  unfold sextValue
  have hmsb : (BitVec.ofNat n x).msb = true ↔ 2 * (x % 2 ^ n) ≥ 2 ^ n := by
    rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_ofNat]
  by_cases h : 2 * (x % 2 ^ n) ≥ 2 ^ n
  · have h' : (BitVec.ofNat n x).msb = true := hmsb.mpr h
    have hlt : ¬ (x % 2 ^ n < 2 ^ (n - 1)) := by omega
    simp [h', hlt]
  · have h' : (BitVec.ofNat n x).msb = false := by
      cases hm : (BitVec.ofNat n x).msb with
      | false => rfl
      | true => exact absurd (hmsb.mp hm) h
    have hlt : x % 2 ^ n < 2 ^ (n - 1) := by omega
    simp [h', hlt]

/-- Sign extending the low `n` bits of a 64-bit word to 64 bits preserves the
signed value of those bits. -/
theorem signExtend_toInt_sextValue (n : Nat) (hn : 1 ≤ n) (hn64 : n ≤ 64)
    (v : BitVec 64) :
    (BitVec.signExtend 64 (BitVec.setWidth n v)).toInt = sextValue n v.toNat := by
  rw [BitVec.toInt_signExtend_of_le hn64, BitVec.toInt_setWidth, ← BitVec.toInt_ofNat']
  exact ofNat_toInt_sextValue n hn v.toNat

/-- `fitsSigned n v` is exactly the statement that `v` is the sign extension of
its own low `n` bits — the guard the L3 `Encode` uses. -/
theorem fitsSigned_iff_signExtend (n : Nat) (hn : 1 ≤ n) (hn64 : n ≤ 64)
    (v : BitVec 64) :
    fitsSigned n v = true ↔ v = BitVec.signExtend 64 (BitVec.setWidth n v) := by
  unfold fitsSigned
  rw [decide_eq_true_eq, ← signExtend_toInt_sextValue n hn hn64 v]
  exact BitVec.toInt_inj

end Flapjack.Compiler.Encoders.Arm8.L3
