module

public import Flapjack.Misc.BytesInMemory
public import Flapjack.Compiler.Encoders.AsmProps.PcCoverage
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Shared ARMv8 bit-vector and byte-walk lemmas

Carrier-independent facts used by both the closed ARMv8 machine model
(`Machine/`) and the L3 ARMv8 encoder-correctness chain
(`L3/CorrectnessEncoding/`).  They mention only `BitVec`, `Nat` and
`bytesInMemoryHOL`, so they live here rather than being copied into both
trees.  The byte-domain walk is proved once in
`AsmProps/PcCoverage.lean`'s `byteOffsetInDomain` (shared with the X64 model)
and re-exported below.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack

/-- A word whose bits are all outside the mask `M` agrees with `w &&& M`. -/
theorem and_not_eq_zero_eq (w M : BitVec 64) (h : w &&& ~~~M = 0) : w &&& M = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  have hb := congrArg (fun x : BitVec 64 => x.getLsbD i) h
  have hz : (0 : BitVec 64).getLsbD i = false := by simp
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, hz] at hb
  cases hm : M.getLsbD i with
  | false =>
      simp only [hm, Bool.not_false, Bool.and_true] at hb
      rw [hb, Bool.false_and]
  | true =>
      simp only [hm, Bool.not_true, Bool.and_false, Bool.and_true] at hb ⊢

/-- `toNat` of a left shift of an `ofNat` word. -/
theorem toNat_ofNat_shiftLeft (imm k : Nat) :
    (BitVec.ofNat 64 imm <<< k).toNat = (imm * 2 ^ k) % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- A natural number that agrees with the mask of the `k`-th 16-bit block only
has bits inside that block: it is a multiple of `2 ^ k` whose quotient fits in
16 bits, and the quotient reproduces it. -/
theorem blockDiv (x k : Nat) (hx : x &&& ((2 ^ 16 - 1) * 2 ^ k) = x) :
    x / 2 ^ k % 2 ^ 16 = x / 2 ^ k ∧ x / 2 ^ k * 2 ^ k = x := by
  have hle : x ≤ (2 ^ 16 - 1) * 2 ^ k := by
    have h := Nat.and_le_right (n := x) (m := (2 ^ 16 - 1) * 2 ^ k)
    rwa [hx] at h
  have hlow : x &&& (2 ^ k - 1) = 0 := by
    rw [← hx, Nat.and_assoc]
    have hz : ((2 ^ 16 - 1) * 2 ^ k) &&& (2 ^ k - 1) = 0 := by
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm (2 ^ 16 - 1) (2 ^ k),
        Nat.mul_mod_right]
    rw [hz, Nat.and_zero]
  have hmod : x % 2 ^ k = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod, hlow]
  have hdvd : 2 ^ k ∣ x := Nat.dvd_of_mod_eq_zero hmod
  have hdiv : x / 2 ^ k ≤ 2 ^ 16 - 1 :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hle)
  exact ⟨Nat.mod_eq_of_lt (by omega), Nat.div_mul_cancel hdvd⟩

/-- Wrapped address reassociation for the byte walk (Flapjack infrastructure). -/
theorem addOneOffset {width : Nat} (a : BitVec width) (j : Nat) :
    (a + 1) + BitVec.ofNat width j = a + BitVec.ofNat width (j + 1) :=
  Flapjack.Compiler.Encoders.AsmProps.addOneOffset a j

/-- The `j`-th byte of a byte list in memory lies in the domain, for every `j`
below the length. -/
theorem bytesInMemoryHOL_domain {width : Nat} [NeZero width]
    {a : BitVec width} {bs : List (BitVec 8)} {m : BitVec width → BitVec 8}
    {d : BitVec width → Prop} (h : bytesInMemoryHOL a bs m d) :
    ∀ j, j < bs.length → d (a + BitVec.ofNat width j) :=
  fun j hj => Flapjack.Compiler.Encoders.AsmProps.byteOffsetInDomain bs a m d h j hj

/-- The immediate of one `enc_mov_imm`/`arm8EncMovImm` branch reproduces the
masked word: if every bit of `v` outside the 16-bit block at position `k` is
zero and `imm16` is the block's value, then `imm16 <<< k` is `v`.  Shared by the
ARM8 machine `const` case and the L3 `const` encoder-correctness case. -/
theorem movWideImm_value (v : BitVec 64) (k imm16 : Nat) (hk : k ≤ 48)
    (hflag : v &&& ~~~(BitVec.ofNat 64 (0xFFFF <<< k)) = 0)
    (himm : imm16 = (v >>> k).toNat % 65536) :
    BitVec.ofNat 64 imm16 <<< k = v := by
  have hM := and_not_eq_zero_eq v (BitVec.ofNat 64 (0xFFFF <<< k)) hflag
  have hto : v.toNat &&& (BitVec.ofNat 64 (0xFFFF <<< k)).toNat = v.toNat := by
    have h := congrArg BitVec.toNat hM
    simpa using h
  have hmask : (BitVec.ofNat 64 (0xFFFF <<< k)).toNat = (2 ^ 16 - 1) * 2 ^ k := by
    rw [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hlt : 65535 * 2 ^ k < 2 ^ 64 := by
      have h2 : (2 : Nat) ^ k ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hk
      have h3 : (65535 : Nat) * 2 ^ 48 < 2 ^ 64 := by norm_num
      have := Nat.mul_le_mul_left 65535 h2
      omega
    rw [Nat.mod_eq_of_lt hlt]
    norm_num
  rw [hmask] at hto
  obtain ⟨h1, h2⟩ := blockDiv v.toNat k hto
  have hdiv : (v >>> k).toNat % 65536 = v.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact h1
  rw [himm, hdiv]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_shiftLeft, h2, Nat.mod_eq_of_lt v.isLt]

end Flapjack.Compiler.Encoders.Arm8
