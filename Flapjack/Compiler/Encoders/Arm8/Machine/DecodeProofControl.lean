/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProofConditional

/-!
# ARMv8 decoder inverses: control transfer and memory forms

Decoder inverses for the last emitted instruction forms: the two
`loadStoreImmediate` shapes (unsigned offset and signed, unscaled offset), the
two branch forms `branchImmediate` and `branchConditional`, and the
`PC`-relative `address` form.

Each inverse is stated for exactly the word `encodeInsn32` emits, with the bound
hypotheses under which its guard succeeds:

* `loadStoreImmediate` with `unsignedOffset` needs
  `offset = (BitVec.ofNat 64 imm12) <<< size` for the `imm12` the encoder
  computes; the signed (unscaled) shape needs `fitsSigned 9 offset`.  The
  lowering (`arm8_ast`) only emits `signed := false`, and with that field fixed
  the `opc` field is `0` for a store and `1` for a load, which is exactly the
  `loadStoreOpc` helper below.  A store's `opc` does not depend on
  `regsizeWord`, and a load with `signed := false` always has `opc = 1`, so the
  decoder cannot recover `regsizeWord := true` from those words: the inverses
  are stated for the canonical `regsizeWord := false` representative.  That
  representative encodes to the same bytes as the `regsizeWord := true` form
  (`regsizeWord` only enters `opc` for `signed := true`), and `execInsn` ignores
  the field, so no emitted behaviour is lost.
* `branchImmediate` needs `fitsSigned 28 imm` and `imm.toNat % 4 = 0`.
* `branchConditional` needs `fitsSigned 21 imm` and `imm.toNat % 4 = 0`.
* `address false` needs `fitsSigned 21 imm`, the encoder's own guard; the
  decoder sign-extends the same twenty-one bits.

Each family supplies the same chain: the width-typed carrier word, its `fields`
composition (`fields_*`), the decoder on that word (`decode_*_word`), the
instruction-level inverse on the emitted fields (`decode_encode_*32` and its
64-bit carrier form `decode_encode_*`), the encoder's emitted word
(`encodeInsn_*`), the composed inverse (`decode_encode_*Insn`) and the step
theorem `arm8Next_*`.

The `address true` (page) form is decoded faithfully from bits 32:14 and 13:12,
but no lowering path emits it: `arm8_ast`'s `Loc` case only produces
`.address false`.  It therefore has no step theorem here; concrete positive,
negative, and bit-32 round trips are checked in
`Flapjack/Test/Arm8Encoding.lean`.

Bit facts are proved by extensionality over `getLsbD` and `interval_cases`, and
every `Nat`/`Int` fact is a kernel proof; no native decision procedure is used.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-! ## Sign extension

`sextValue bits x` depends only on `x % 2 ^ bits`, and a value that `fitsSigned`
its own low bits is the sign extension of them. -/

/-- `sextValue` ignores everything above its low `bits` bits. -/
theorem sextValue_mod (bits value : Nat) : sextValue bits (value % 2 ^ bits) = sextValue bits value := by
  unfold sextValue
  rw [Nat.mod_mod]

/-- `sextValue` only depends on the low `bits` bits. -/
theorem sextValue_congr (bits a b : Nat) (h : a % 2 ^ bits = b % 2 ^ bits) :
    sextValue bits a = sextValue bits b := by
  unfold sextValue
  rw [h]

/-- A word that `fitsSigned` its own low `bits` bits is unchanged by sign
extension. -/
theorem sextToWord_eq_self (bits : Nat) (v : W) (h : fitsSigned bits v = true) :
    sextToWord bits v = v := by
  unfold sextToWord
  unfold fitsSigned at h
  rw [decide_eq_true_eq] at h
  rw [← h]
  exact BitVec.ofInt_toInt

/-- A multiple of four leaves the low `k + 2` bits unchanged when its `k`-bit
field above bit 1 is written back and shifted up. -/
theorem nat_field_mod_shift (k a : Nat) (hmod : a % 4 = 0) :
    (a / 4 % 2 ^ k) * 4 % 2 ^ (k + 2) = a % 2 ^ (k + 2) := by
  have hcancel : a / 4 * 4 = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
  have hpow : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have hlt : a / 4 % 2 ^ k * 4 < 2 ^ k * 4 := by
    have h := Nat.mod_lt (a / 4) (Nat.two_pow_pos k)
    exact Nat.mul_lt_mul_of_pos_right h (by norm_num)
  calc (a / 4 % 2 ^ k) * 4 % 2 ^ (k + 2)
      = (a / 4 * 4) % (2 ^ k * 4) := by
        rw [hpow, Nat.mul_mod_mul_right 4 (a / 4) (2 ^ k), Nat.mod_eq_of_lt hlt]
    _ = a % 2 ^ (k + 2) := by rw [hcancel, hpow]

/-- The field `(imm >>> 2) % 2^k` written back as `(... <<< 2)` reconstructs the
low `k + 2` bits of `imm` whenever `imm` is a multiple of four. -/
theorem field_mod_shift (k : Nat) (imm : W) (hmod : imm.toNat % 4 = 0) :
    ((((imm >>> 2).toNat % 2 ^ k) <<< 2)) % 2 ^ (k + 2) = imm.toNat % 2 ^ (k + 2) := by
  have hshift : (imm >>> 2).toNat = imm.toNat / 4 :=
    (BitVec.toNat_ushiftRight imm 2).trans (Nat.shiftRight_eq_div_pow _ _)
  rw [hshift, Nat.shiftLeft_eq]
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  rw [h4]
  exact nat_field_mod_shift k imm.toNat hmod

/-- The shifted `k`-bit field sign-extends back to the original word, provided
the word fits in `k + 2` signed bits and is a multiple of four. -/
theorem ofInt_sextValue_field_shift (k : Nat) (imm : W)
    (hmod : imm.toNat % 4 = 0) (hfits : fitsSigned (k + 2) imm = true) :
    BitVec.ofInt 64 (sextValue (k + 2) (((imm >>> 2).toNat % 2 ^ k) <<< 2)) = imm := by
  unfold fitsSigned at hfits
  rw [decide_eq_true_eq] at hfits
  have hcongr : sextValue (k + 2) (((imm >>> 2).toNat % 2 ^ k) <<< 2)
      = sextValue (k + 2) imm.toNat :=
    sextValue_congr (k + 2) _ _ (field_mod_shift k imm hmod)
  rw [hcongr, ← hfits]
  exact BitVec.ofInt_toInt

/-- The low `k + 2` bits of a `Nat` are reconstructed from its `k`-bit field
above bit 1 together with its low two bits. -/
theorem nat_field_mod_shift_add (k a : Nat) :
    ((a / 4 % 2 ^ k) * 4 + a % 4) % 2 ^ (k + 2) = a % 2 ^ (k + 2) := by
  have hpow : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  let x := a / 4 % 2 ^ k
  let y := a / 4 / 2 ^ k
  let r := a % 4
  have hq : a / 4 = x + 2 ^ k * y := by
    have h := Nat.div_add_mod (a / 4) (2 ^ k)
    dsimp [x, y]
    omega
  have ha : a = x * 4 + (2 ^ k * y) * 4 + r := by
    calc
      a = a / 4 * 4 + a % 4 := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod a 4).symm
      _ = (x + 2 ^ k * y) * 4 + r := by rw [hq]
      _ = x * 4 + (2 ^ k * y) * 4 + r := by ring
  have hx : x < 2 ^ k := by
    dsimp [x]
    exact Nat.mod_lt _ (Nat.two_pow_pos k)
  have hr : r < 4 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hx4 : x * 4 < 2 ^ k * 4 := Nat.mul_lt_mul_of_pos_right hx (by norm_num)
  have hlt : x * 4 + r < 2 ^ k * 4 := by omega
  rw [hpow]
  change (x * 4 + r) % (2 ^ k * 4) = a % (2 ^ k * 4)
  calc
    (x * 4 + r) % (2 ^ k * 4) = x * 4 + r := Nat.mod_eq_of_lt hlt
    _ = a % (2 ^ k * 4) := by
      rw [ha]
      rw [show x * 4 + (2 ^ k * y) * 4 + r = (x * 4 + r) + (2 ^ k * 4) * y by ring]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The `k`-bit field `(imm >>> 2) % 2^k` together with the low two bits of
`imm` reconstructs the low `k + 2` bits of `imm`. -/
theorem field_mod_shift_add (k : Nat) (imm : W) :
    ((((imm >>> 2).toNat % 2 ^ k) <<< 2) + imm.toNat % 4) % 2 ^ (k + 2)
      = imm.toNat % 2 ^ (k + 2) := by
  have hshift : (imm >>> 2).toNat = imm.toNat / 4 :=
    (BitVec.toNat_ushiftRight imm 2).trans (Nat.shiftRight_eq_div_pow _ _)
  rw [hshift, Nat.shiftLeft_eq]
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  rw [h4]
  exact nat_field_mod_shift_add k imm.toNat

/-- The shifted `k`-bit field plus the low two bits sign-extends back to the
original word when the word fits in `k + 2` signed bits. -/
theorem ofInt_sextValue_field_shift_add (k : Nat) (imm : W)
    (hfits : fitsSigned (k + 2) imm = true) :
    BitVec.ofInt 64 (sextValue (k + 2)
      ((((imm >>> 2).toNat % 2 ^ k) <<< 2) + imm.toNat % 4)) = imm := by
  unfold fitsSigned at hfits
  rw [decide_eq_true_eq] at hfits
  have hcongr : sextValue (k + 2)
      ((((imm >>> 2).toNat % 2 ^ k) <<< 2) + imm.toNat % 4)
      = sextValue (k + 2) imm.toNat :=
    sextValue_congr (k + 2) _ _ (field_mod_shift_add k imm)
  rw [hcongr, ← hfits]
  exact BitVec.ofInt_toInt

/-- Sign-extending the low `bits` bits of a `Nat` and widening the result to a
sixty-four-bit word. -/
theorem sextToWord_ofNat (bits : Nat) (hbits : bits ≤ 64) (x : Nat) :
    sextToWord bits (BitVec.ofNat 64 x) = BitVec.ofInt 64 (sextValue bits x) := by
  unfold sextToWord
  rw [BitVec.toNat_ofNat]
  congr 1
  exact sextValue_congr bits _ _ (Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 hbits))

/-- The signed (unscaled) memory form: the nine-bit field sign-extends back to
the original offset when the offset fits in nine signed bits. -/
theorem sextToWord_ofNat_mod (bits : Nat) (hbits : bits ≤ 64) (v : W)
    (h : fitsSigned bits v = true) :
    sextToWord bits (BitVec.ofNat 64 (v.toNat % 2 ^ bits)) = v := by
  rw [sextToWord_ofNat bits hbits, sextValue_mod]
  exact sextToWord_eq_self bits v h

/-- Shifting a small `Nat` as a zero-extended word is the word of the shifted
`Nat`. -/
theorem ofNat_shiftLeft (x n : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x) <<< n = BitVec.ofNat 64 (x <<< n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]

/-! ## The lowering's twenty-bit range sits inside the encoder's twenty-one-bit range

`arm8_ast` emits `.address false imm` only under `fitsSigned 20 imm`, while
`encodeInsn32` accepts `fitsSigned 21 imm`.  The range of a twenty-bit signed
value is inside the twenty-one-bit range, so the `Loc` case can use the wider
encoder guard. -/

/-- The low twenty-one bits of `2^64 - d` for `0 < d ≤ 2^21`. -/
theorem nat_mod_pow_sub_21 (d : Nat) (hd : 0 < d) (hdb : d ≤ 2 ^ 21) :
    (2 ^ 64 - d) % 2 ^ 21 = 2 ^ 21 - d := by
  have hsplit : 2 ^ 64 - d = (2 ^ 64 - 2 ^ 21) + (2 ^ 21 - d) := by omega
  have hdvd : (2 ^ 21 : Nat) ∣ 2 ^ 64 - 2 ^ 21 := by
    have h : (2 ^ 21 : Nat) * (2 ^ 43 - 1) = 2 ^ 64 - 2 ^ 21 := by
      rw [Nat.mul_sub, Nat.mul_one, ← pow_add]
    rw [← h]
    exact dvd_mul_right _ _
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A sixty-four-bit word in the signed nineteen-bit range fits in twenty-one
signed bits. -/
theorem fitsSigned21_of_range (v : W)
    (hrange : -(2 ^ 19 : Int) ≤ v.toInt ∧ v.toInt ≤ (2 ^ 19 : Int) - 1) :
    fitsSigned 21 v = true := by
  have hx : v.toNat < 2 ^ 64 := v.isLt
  have hcond : v.toInt = if 2 * v.toNat < 2 ^ 64 then (v.toNat : Int)
      else (v.toNat : Int) - (2 : Int) ^ 64 := by
    rw [BitVec.toInt_eq_toNat_cond]
    norm_num
  unfold fitsSigned
  rw [decide_eq_true_eq]
  unfold sextValue
  by_cases hcase : 2 * v.toNat < 2 ^ 64
  · have htoInt : v.toInt = (v.toNat : Int) := by rw [hcond, if_pos hcase]
    have hxlt : v.toNat < 2 ^ 19 := by
      have h : (v.toNat : Int) ≤ (2 : Int) ^ 19 - 1 := by rw [← htoInt]; exact hrange.2
      norm_num at h
      omega
    have hmod : v.toNat % 2 ^ 21 = v.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hmod, if_pos (by omega), htoInt]
  · have htoInt : v.toInt = (v.toNat : Int) - (2 : Int) ^ 64 := by rw [hcond, if_neg hcase]
    have hxge : 2 ^ 64 - 2 ^ 19 ≤ v.toNat := by
      have h : (v.toNat : Int) ≥ (2 : Int) ^ 64 - (2 : Int) ^ 19 := by
        have := hrange.1; rw [htoInt] at this; omega
      omega
    have hdpos : 0 < 2 ^ 64 - v.toNat := by omega
    have hxeq : v.toNat = 2 ^ 64 - (2 ^ 64 - v.toNat) := by omega
    have hmod : v.toNat % 2 ^ 21 = 2 ^ 21 - (2 ^ 64 - v.toNat) := by
      conv_lhs => rw [hxeq]
      exact nat_mod_pow_sub_21 (2 ^ 64 - v.toNat) hdpos (by omega)
    have hneg : ¬ 2 ^ 21 - (2 ^ 64 - v.toNat) < 2 ^ 20 := by omega
    have hcD : ((2 ^ 64 - v.toNat : Nat) : Int) = (2 : Int) ^ 64 - (v.toNat : Int) := by
      rw [Nat.cast_sub (by omega : v.toNat ≤ 2 ^ 64)]
      norm_num
    have hc21 : ((2 ^ 21 - (2 ^ 64 - v.toNat) : Nat) : Int)
        = (2 : Int) ^ 21 - ((2 ^ 64 - v.toNat : Nat) : Int) := by
      rw [Nat.cast_sub (by omega : 2 ^ 64 - v.toNat ≤ 2 ^ 21)]
      norm_num
    rw [hmod, if_neg hneg, htoInt, hc21, hcD]
    norm_num

/-- The lowering's twenty-bit guard implies the encoder's twenty-one-bit
range. -/
theorem fitsSigned20_imp_21 (v : W) (h : fitsSigned 20 v = true) : fitsSigned 21 v = true :=
  fitsSigned21_of_range v ((fitsSigned20_toInt v).1 h)

/-! ## `branchImmediate` -/

/-- The 32-bit word of a `branchImmediate` instruction, over width-typed atoms. -/
def branchImmediateWord (call : BitVec 1) (imm26 : BitVec 26) : BitVec 32 :=
  (((0 : BitVec 32) <<< 1 ||| call.setWidth 32) <<< 5 ||| (5 : BitVec 32)) <<< 26 |||
    imm26.setWidth 32

/-- The `fields` composition of a `branchImmediate` is the width-typed word. -/
theorem fields_branchImmediate (call : Bool) (imm26 : Nat) :
    fields [(1, bit call), (5, 5), (26, imm26)]
      = branchImmediateWord (BitVec.ofNat 1 (bit call)) (BitVec.ofNat 26 imm26) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `branchImmediate` word. -/
theorem decode_branchImmediate_word (call : BitVec 1) (imm26 : BitVec 26) :
    decodeInsn32 (branchImmediateWord call imm26)
      = some (.branchImmediate (BitVec.ofInt 64 (sextValue 28 (imm26.toNat <<< 2)))
          (call.toNat = 1)) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (branchImmediateWord call imm26) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h2 : bitMatches (branchImmediateWord call imm26) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h3 : bitMatches (branchImmediateWord call imm26) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h4 : bitMatches (branchImmediateWord call imm26) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h5 : bitMatches (branchImmediateWord call imm26) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h6 : bitMatches (branchImmediateWord call imm26) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h7 : bitMatches (branchImmediateWord call imm26) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h8 : bitMatches (branchImmediateWord call imm26) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h9 : bitMatches (branchImmediateWord call imm26) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h10 : bitMatches (branchImmediateWord call imm26) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h11 : bitMatches (branchImmediateWord call imm26) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h12 : bitMatches (branchImmediateWord call imm26) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h13 : bitMatches (branchImmediateWord call imm26) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h14 : bitMatches (branchImmediateWord call imm26) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h15 : bitMatches (branchImmediateWord call imm26) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h16 : bitMatches (branchImmediateWord call imm26) 0x3D000000 0x39000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have h17 : bitMatches (branchImmediateWord call imm26) 0x3F000000 0x38000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchImmediateWord] at hb
    simp at hb
  have hK : bitMatches (branchImmediateWord call imm26) 0x7C000000 0x14000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchImmediateWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    hK, Bool.false_eq_true, if_true, if_false]
  have f0 : part (branchImmediateWord call imm26) 0 26 = imm26.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchImmediateWord]
    simp
  have f31 : part (branchImmediateWord call imm26) 31 1 = call.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchImmediateWord]
    simp
    interval_cases i
    simp
  simp only [f0, f31]

/-- The `branchImmediate` word decodes back to the encoded instruction. -/
theorem decode_encode_branchImmediate32 (imm : W) (call : Bool)
    (hfits : fitsSigned 28 imm = true) (hmod : imm.toNat % 4 = 0) :
    decodeInsn32 (fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)])
      = some (.branchImmediate imm call) := by
  rw [fields_branchImmediate call ((imm >>> 2).toNat % 2 ^ 26),
    decode_branchImmediate_word (BitVec.ofNat 1 (bit call))
      (BitVec.ofNat 26 ((imm >>> 2).toNat % 2 ^ 26))]
  have h26 : (BitVec.ofNat 26 ((imm >>> 2).toNat % 2 ^ 26)).toNat
      = (imm >>> 2).toNat % 2 ^ 26 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  rw [h26, ofInt_sextValue_field_shift 26 imm hmod hfits]
  cases call <;> rfl

/-- The 64-bit carrier word emitted for a `branchImmediate`. -/
theorem encodeInsn_branchImmediate (imm : W) (call : Bool)
    (hfits : fitsSigned 28 imm = true) (hmod : imm.toNat % 4 = 0) :
    encodeInsn (.branchImmediate imm call) =
      some ((fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]).setWidth 64) := by
  unfold encodeInsn
  rw [show encodeInsn32 (.branchImmediate imm call)
      = some (fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]) by
    simp only [encodeInsn32, hfits, hmod]
    rw [if_pos]
    rfl]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_branchImmediate (imm : W) (call : Bool)
    (hfits : fitsSigned 28 imm = true) (hmod : imm.toNat % 4 = 0) :
    decodeInsn ((fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]).setWidth 64)
      = some (.branchImmediate imm call) := by
  rw [show decodeInsn ((fields [(1, bit call), (5, 5),
      (26, (imm >>> 2).toNat % 2 ^ 26)]).setWidth 64)
      = decodeInsn32 (fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]) by
    simp [decodeInsn]]
  exact decode_encode_branchImmediate32 imm call hfits hmod

/-- `decodeInsn` inverts `encodeInsn` on a `branchImmediate`. -/
theorem decode_encode_branchImmediateInsn (imm : W) (call : Bool)
    (hfits : fitsSigned 28 imm = true) (hmod : imm.toNat % 4 = 0) :
    decodeInsn ((encodeInsn (.branchImmediate imm call)).getD 0)
      = some (.branchImmediate imm call) := by
  rw [encodeInsn_branchImmediate imm call hfits hmod, Option.getD_some]
  exact decode_encode_branchImmediate imm call hfits hmod

/-- One machine step executes a `branchImmediate` whose bytes are at the PC. -/
theorem arm8Next_branchImmediate (s : Arm8State) (d : BitVec 64 → Prop)
    (imm : W) (call : Bool) (hfits : fitsSigned 28 imm = true)
    (hmod : imm.toNat % 4 = 0)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.branchImmediate imm call)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.branchImmediate imm call) := by
  rw [arm8Next_encodeBytes s (.branchImmediate imm call)
    ((fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]).setWidth 64) d
    (encodeInsn_branchImmediate imm call hfits hmod)
    (decode_encode_branchImmediate imm call hfits hmod) hbytes]


/-! ## `branchConditional` -/

/-- The 32-bit word of a `branchConditional` instruction, over width-typed
atoms. -/
def branchConditionalWord (imm19 : BitVec 19) (cond : BitVec 4) : BitVec 32 :=
  ((((0 : BitVec 32) <<< 8 ||| (84 : BitVec 32)) <<< 19 ||| imm19.setWidth 32) <<< 1 |||
    (0 : BitVec 32)) <<< 4 ||| cond.setWidth 32

/-- The `fields` composition of a `branchConditional` is the width-typed word. -/
theorem fields_branchConditional (imm19 cond : Nat) :
    fields [(8, 84), (19, imm19), (1, 0), (4, cond)]
      = branchConditionalWord (BitVec.ofNat 19 imm19) (BitVec.ofNat 4 cond) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `branchConditional` word. -/
theorem decode_branchConditional_word (imm19 : BitVec 19) (cond : BitVec 4) :
    decodeInsn32 (branchConditionalWord imm19 cond)
      = some (.branchConditional (BitVec.ofInt 64 (sextValue 21 (imm19.toNat <<< 2)))
          cond.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (branchConditionalWord imm19 cond) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 4) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h2 : bitMatches (branchConditionalWord imm19 cond) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h3 : bitMatches (branchConditionalWord imm19 cond) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h4 : bitMatches (branchConditionalWord imm19 cond) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h5 : bitMatches (branchConditionalWord imm19 cond) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h6 : bitMatches (branchConditionalWord imm19 cond) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h7 : bitMatches (branchConditionalWord imm19 cond) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h8 : bitMatches (branchConditionalWord imm19 cond) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h9 : bitMatches (branchConditionalWord imm19 cond) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h10 : bitMatches (branchConditionalWord imm19 cond) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h11 : bitMatches (branchConditionalWord imm19 cond) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h12 : bitMatches (branchConditionalWord imm19 cond) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h13 : bitMatches (branchConditionalWord imm19 cond) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h14 : bitMatches (branchConditionalWord imm19 cond) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h15 : bitMatches (branchConditionalWord imm19 cond) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h16 : bitMatches (branchConditionalWord imm19 cond) 0x3D000000 0x39000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h17 : bitMatches (branchConditionalWord imm19 cond) 0x3F000000 0x38000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have h18 : bitMatches (branchConditionalWord imm19 cond) 0x7C000000 0x14000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    simp only [branchConditionalWord] at hb
    simp at hb
  have hK : bitMatches (branchConditionalWord imm19 cond) 0xFF000010 0x54000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchConditionalWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    hK, Bool.false_eq_true, if_true, if_false]
  have f5 : part (branchConditionalWord imm19 cond) 5 19 = imm19.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchConditionalWord]
    simp
    interval_cases i <;> simp
  have f0 : part (branchConditionalWord imm19 cond) 0 4 = cond.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchConditionalWord]
    simp
  simp only [f5, f0]

/-- The `branchConditional` word decodes back to the encoded instruction. -/
theorem decode_encode_branchConditional32 (imm : W) (cond : Nat)
    (hfits : fitsSigned 21 imm = true) (hmod : imm.toNat % 4 = 0) (hcond : cond < 16) :
    decodeInsn32 (fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)])
      = some (.branchConditional imm cond) := by
  rw [fields_branchConditional ((imm >>> 2).toNat % 2 ^ 19) cond,
    decode_branchConditional_word (BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19))
      (BitVec.ofNat 4 cond)]
  have h19 : (BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19)).toNat
      = (imm >>> 2).toNat % 2 ^ 19 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  have h4 : (BitVec.ofNat 4 cond).toNat = cond := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcond]
  rw [h19, h4, ofInt_sextValue_field_shift 19 imm hmod hfits]

/-- The 64-bit carrier word emitted for a `branchConditional`. -/
theorem encodeInsn_branchConditional (imm : W) (cond : Nat)
    (hfits : fitsSigned 21 imm = true) (hmod : imm.toNat % 4 = 0) :
    encodeInsn (.branchConditional imm cond) =
      some ((fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0),
        (4, cond)]).setWidth 64) := by
  unfold encodeInsn
  rw [show encodeInsn32 (.branchConditional imm cond)
      = some (fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)]) by
    simp only [encodeInsn32, hfits, hmod]
    rw [if_pos]
    rfl]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_branchConditional (imm : W) (cond : Nat)
    (hfits : fitsSigned 21 imm = true) (hmod : imm.toNat % 4 = 0) (hcond : cond < 16) :
    decodeInsn ((fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0),
      (4, cond)]).setWidth 64) = some (.branchConditional imm cond) := by
  rw [show decodeInsn ((fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0),
      (4, cond)]).setWidth 64)
      = decodeInsn32 (fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0),
          (4, cond)]) by
    simp [decodeInsn]]
  exact decode_encode_branchConditional32 imm cond hfits hmod hcond

/-- `decodeInsn` inverts `encodeInsn` on a `branchConditional`. -/
theorem decode_encode_branchConditionalInsn (imm : W) (cond : Nat)
    (hfits : fitsSigned 21 imm = true) (hmod : imm.toNat % 4 = 0) (hcond : cond < 16) :
    decodeInsn ((encodeInsn (.branchConditional imm cond)).getD 0)
      = some (.branchConditional imm cond) := by
  rw [encodeInsn_branchConditional imm cond hfits hmod, Option.getD_some]
  exact decode_encode_branchConditional imm cond hfits hmod hcond

/-- One machine step executes a `branchConditional` whose bytes are at the PC. -/
theorem arm8Next_branchConditional (s : Arm8State) (d : BitVec 64 → Prop)
    (imm : W) (cond : Nat) (hfits : fitsSigned 21 imm = true) (hmod : imm.toNat % 4 = 0)
    (hcond : cond < 16)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.branchConditional imm cond)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.branchConditional imm cond) := by
  rw [arm8Next_encodeBytes s (.branchConditional imm cond)
    ((fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)]).setWidth 64) d
    (encodeInsn_branchConditional imm cond hfits hmod)
    (decode_encode_branchConditional imm cond hfits hmod hcond) hbytes]


/-! ## `address false` -/

/-- The 32-bit word of a `PC`-relative `address` instruction, over width-typed
atoms. -/
def addressFalseWord (imm2 : BitVec 2) (imm19 : BitVec 19) (rd : BitVec 5) : BitVec 32 :=
  (((((0 : BitVec 32) <<< 1 ||| (0 : BitVec 32)) <<< 2 ||| imm2.setWidth 32) <<< 5 |||
    (16 : BitVec 32)) <<< 19 ||| imm19.setWidth 32) <<< 5 ||| rd.setWidth 32

/-- The `fields` composition of an `address false` is the width-typed word. -/
theorem fields_addressFalse (imm2 imm19 rd : Nat) :
    fields [(1, 0), (2, imm2), (5, 16), (19, imm19), (5, rd)]
      = addressFalseWord (BitVec.ofNat 2 imm2) (BitVec.ofNat 19 imm19)
          (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `address false` word. -/
theorem decode_addressFalse_word (imm2 : BitVec 2) (imm19 : BitVec 19) (rd : BitVec 5) :
    decodeInsn32 (addressFalseWord imm2 imm19 rd)
      = some (.address false
          (BitVec.ofInt 64 (sextValue 21 (imm19.toNat <<< 2 + imm2.toNat)))
          rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h2 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h3 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h4 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h5 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h6 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h7 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h8 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h9 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h10 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h11 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h12 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h13 : bitMatches (addressFalseWord imm2 imm19 rd) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h14 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h15 : bitMatches (addressFalseWord imm2 imm19 rd) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h16 : bitMatches (addressFalseWord imm2 imm19 rd) 0x3D000000 0x39000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h17 : bitMatches (addressFalseWord imm2 imm19 rd) 0x3F000000 0x38000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h18 : bitMatches (addressFalseWord imm2 imm19 rd) 0x7C000000 0x14000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h19 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFF000010 0x54000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [addressFalseWord] at hb
    simp at hb
  have h20 : bitMatches (addressFalseWord imm2 imm19 rd) 0xFF9FFC1F 0xD61F0000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 31) h
    simp only [addressFalseWord] at hb
    simp at hb
  have hK : bitMatches (addressFalseWord imm2 imm19 rd) 0x9F000000 0x10000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addressFalseWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, hK, Bool.false_eq_true, if_true, if_false]
  have f5 : part (addressFalseWord imm2 imm19 rd) 5 19 = imm19.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addressFalseWord]
    simp
    interval_cases i <;> simp
  have f29 : part (addressFalseWord imm2 imm19 rd) 29 2 = imm2.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addressFalseWord]
    simp
    interval_cases i <;> simp
  have f0 : part (addressFalseWord imm2 imm19 rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addressFalseWord]
    simp
  simp only [f5, f29, f0]

/-- The `address false` word decodes back to the encoded immediate, provided the
immediate lies inside the decoder's twenty-one-bit range. -/
theorem decode_encode_addressFalse32 (imm : W) (rd : Nat)
    (hfits : fitsSigned 21 imm = true) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 0), (2, imm.toNat % 4), (5, 16),
      (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)])
      = some (.address false imm rd) := by
  rw [fields_addressFalse (imm.toNat % 4) ((imm >>> 2).toNat % 2 ^ 19) rd,
    decode_addressFalse_word (BitVec.ofNat 2 (imm.toNat % 4))
      (BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19)) (BitVec.ofNat 5 rd)]
  have h19 : (BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19)).toNat
      = (imm >>> 2).toNat % 2 ^ 19 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  have h5 : (BitVec.ofNat 5 rd).toNat = rd := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrd]
  have h2 : (BitVec.ofNat 2 (imm.toNat % 4)).toNat = imm.toNat % 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  rw [h19, h5, h2]
  rw [ofInt_sextValue_field_shift_add 19 imm hfits]

/-- The 64-bit carrier word emitted for an `address false`. -/
theorem encodeInsn_addressFalse (imm : W) (rd : Nat) (hfits : fitsSigned 21 imm = true) :
    encodeInsn (.address false imm rd) =
      some ((fields [(1, 0), (2, imm.toNat % 4), (5, 16),
        (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]).setWidth 64) := by
  unfold encodeInsn
  rw [show encodeInsn32 (.address false imm rd)
      = some (fields [(1, 0), (2, imm.toNat % 4), (5, 16),
          (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]) by
    simp only [encodeInsn32]
    rw [if_neg (by simp), if_pos hfits]]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_addressFalse (imm : W) (rd : Nat)
    (hfits : fitsSigned 21 imm = true) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 0), (2, imm.toNat % 4), (5, 16),
      (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]).setWidth 64)
      = some (.address false imm rd) := by
  rw [show decodeInsn ((fields [(1, 0), (2, imm.toNat % 4), (5, 16),
      (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 0), (2, imm.toNat % 4), (5, 16),
          (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_addressFalse32 imm rd hfits hrd

/-- `decodeInsn` inverts `encodeInsn` on an `address false` instruction. -/
theorem decode_encode_addressFalseInsn (imm : W) (rd : Nat)
    (hfits : fitsSigned 21 imm = true) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.address false imm rd)).getD 0) = some (.address false imm rd) := by
  rw [encodeInsn_addressFalse imm rd hfits, Option.getD_some]
  exact decode_encode_addressFalse imm rd hfits hrd

/-- One machine step executes an `address false` whose bytes are at the PC. -/
theorem arm8Next_addressFalse (s : Arm8State) (d : BitVec 64 → Prop)
    (imm : W) (rd : Nat) (hfits : fitsSigned 21 imm = true)
    (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.address false imm rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.address false imm rd) := by
  rw [arm8Next_encodeBytes s (.address false imm rd)
    ((fields [(1, 0), (2, imm.toNat % 4), (5, 16),
      (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]).setWidth 64) d
    (encodeInsn_addressFalse imm rd hfits)
    (decode_encode_addressFalse imm rd hfits hrd) hbytes]


/-! ## `loadStoreImmediate`: unsigned offset -/

/-- The `opc` field `encodeInsn32` emits for a memory instruction whose `signed`
flag is `false` (the only shape the lowering emits): `0` for a store and `1` for
a load. -/
def loadStoreOpc (memop : MemOp) : Nat :=
  match memop with
  | .store => 0
  | .load => 1

/-- The 32-bit word of an unsigned-offset memory instruction, over width-typed
atoms. -/
def loadStoreUnsignedWord (size : BitVec 2) (opc : BitVec 2) (imm12 : BitVec 12)
    (rn rt : BitVec 5) : BitVec 32 :=
  ((((((0 : BitVec 32) <<< 2 ||| size.setWidth 32) <<< 6 ||| (57 : BitVec 32)) <<< 2 |||
      opc.setWidth 32) <<< 12 ||| imm12.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 |||
    (rt.setWidth 32)

/-- The `fields` composition of an unsigned-offset memory instruction is the
width-typed word. -/
theorem fields_loadStoreImmediateUnsigned (size opc imm12 rn rt : Nat) :
    fields [(2, size), (6, 57), (2, opc), (12, imm12), (5, rn), (5, rt)]
      = loadStoreUnsignedWord (BitVec.ofNat 2 size) (BitVec.ofNat 2 opc)
          (BitVec.ofNat 12 imm12) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed unsigned-offset memory word. -/
theorem decode_loadStoreImmediateUnsigned_word (size : BitVec 2) (opc : BitVec 2)
    (imm12 : BitVec 12) (rn rt : BitVec 5) :
    decodeInsn32 (loadStoreUnsignedWord size opc imm12 rn rt)
      = some (.loadStoreImmediate size.toNat (opc.toNat = 3)
          (if opc.toNat ≠ 0 then .load else .store) false true
          (BitVec.ofNat 64 (imm12.toNat <<< size.toNat)) rn.toNat rt.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 29) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h2 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h3 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h4 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h5 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h6 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h7 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h8 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h9 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h10 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h11 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h12 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h13 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h14 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have h15 : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreUnsignedWord] at hb
    simp at hb
  have hK : bitMatches (loadStoreUnsignedWord size opc imm12 rn rt) 0x3D000000 0x39000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hK,
    Bool.false_eq_true, if_true, if_false]
  have f22 : part (loadStoreUnsignedWord size opc imm12 rn rt) 22 2 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  have f10 : part (loadStoreUnsignedWord size opc imm12 rn rt) 10 12 = imm12.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  have f30 : part (loadStoreUnsignedWord size opc imm12 rn rt) 30 2 = size.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  have f5 : part (loadStoreUnsignedWord size opc imm12 rn rt) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  have f0 : part (loadStoreUnsignedWord size opc imm12 rn rt) 0 5 = rt.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreUnsignedWord]
    interval_cases i <;> simp
  simp only [f30, f22, f10, f5, f0]

/-- The unsigned-offset memory word decodes back to the encoded instruction,
whenever the offset is the scaled twelve-bit immediate the encoder writes. -/
theorem decode_encode_loadStoreImmediateUnsigned32 (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (imm12 : Nat) (offset : W) (rn rt : Nat)
    (hsize : size < 4) (himm12 : imm12 < 4096) (hreg : regsizeWord = false)
    (hrn : rn < 32) (hrt : rt < 32)
    (hshape : offset = (BitVec.ofNat 64 imm12) <<< size) :
    decodeInsn32 (fields [(2, size), (6, 57), (2, loadStoreOpc memop), (12, imm12),
      (5, rn), (5, rt)])
      = some (.loadStoreImmediate size regsizeWord memop false true offset rn rt) := by
  rw [fields_loadStoreImmediateUnsigned size (loadStoreOpc memop) imm12 rn rt,
    decode_loadStoreImmediateUnsigned_word (BitVec.ofNat 2 size)
      (BitVec.ofNat 2 (loadStoreOpc memop)) (BitVec.ofNat 12 imm12)
      (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)]
  have hs : (BitVec.ofNat 2 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ho : loadStoreOpc memop < 4 := by
    cases memop <;> simp [loadStoreOpc]
  have ho' : (BitVec.ofNat 2 (loadStoreOpc memop)).toNat = loadStoreOpc memop := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  have hi : (BitVec.ofNat 12 imm12).toNat = imm12 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt himm12]
  have hn : (BitVec.ofNat 5 rn).toNat = rn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn]
  have ht : (BitVec.ofNat 5 rt).toNat = rt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrt]
  have hi64 : imm12 < 2 ^ 64 := by omega
  have hscale : (BitVec.ofNat 64 imm12) <<< size = BitVec.ofNat 64 (imm12 <<< size) :=
    ofNat_shiftLeft imm12 size hi64
  rw [hs, ho', hi, hn, ht, ← hscale, ← hshape]
  cases memop <;> simp [loadStoreOpc, hreg]

/-- The 64-bit carrier word emitted for an unsigned-offset memory instruction. -/
theorem encodeInsn_loadStoreImmediateUnsigned (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat)
    (hshape : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size) :
    encodeInsn (.loadStoreImmediate size regsizeWord memop false true offset rn rt) =
      some ((fields [(2, size), (6, 57), (2, loadStoreOpc memop),
        (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]).setWidth 64) := by
  unfold encodeInsn
  rw [show encodeInsn32 (.loadStoreImmediate size regsizeWord memop false true offset rn rt)
      = some (fields [(2, size), (6, 57), (2, loadStoreOpc memop),
          (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]) by
    simp only [encodeInsn32, loadStoreOpc]
    cases memop <;>
      (rw [if_pos (by simp only [Bool.true_and]; exact decide_eq_true hshape)]
       try simp)]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_loadStoreImmediateUnsigned (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat) (hsize : size < 4)
    (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hshape : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size) :
    decodeInsn ((fields [(2, size), (6, 57), (2, loadStoreOpc memop),
      (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]).setWidth 64)
      = some (.loadStoreImmediate size regsizeWord memop false true offset rn rt) := by
  rw [show decodeInsn ((fields [(2, size), (6, 57), (2, loadStoreOpc memop),
      (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]).setWidth 64)
      = decodeInsn32 (fields [(2, size), (6, 57), (2, loadStoreOpc memop),
          (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]) by
    simp [decodeInsn]]
  exact decode_encode_loadStoreImmediateUnsigned32 size regsizeWord memop
    ((offset >>> size).toNat % 4096) offset rn rt hsize (Nat.mod_lt _ (by norm_num))
    hreg hrn hrt hshape

/-- `decodeInsn` inverts `encodeInsn` on an unsigned-offset memory instruction. -/
theorem decode_encode_loadStoreImmediateUnsignedInsn (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat) (hsize : size < 4)
    (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hshape : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size) :
    decodeInsn ((encodeInsn (.loadStoreImmediate size regsizeWord memop false true
      offset rn rt)).getD 0)
      = some (.loadStoreImmediate size regsizeWord memop false true offset rn rt) := by
  rw [encodeInsn_loadStoreImmediateUnsigned size regsizeWord memop offset rn rt hshape,
    Option.getD_some]
  exact decode_encode_loadStoreImmediateUnsigned size regsizeWord memop offset rn rt hsize
    hreg hrn hrt hshape

/-- One machine step executes an unsigned-offset memory instruction whose bytes
are at the PC. -/
theorem arm8Next_loadStoreImmediateUnsigned (s : Arm8State) (d : BitVec 64 → Prop)
    (size : Nat) (regsizeWord : Bool) (memop : MemOp) (offset : W) (rn rt : Nat)
    (hsize : size < 4) (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hshape : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size regsizeWord memop false true offset rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size regsizeWord memop false true offset rn rt) := by
  rw [arm8Next_encodeBytes s (.loadStoreImmediate size regsizeWord memop false true
      offset rn rt)
    ((fields [(2, size), (6, 57), (2, loadStoreOpc memop),
      (12, (offset >>> size).toNat % 4096), (5, rn), (5, rt)]).setWidth 64) d
    (encodeInsn_loadStoreImmediateUnsigned size regsizeWord memop offset rn rt hshape)
    (decode_encode_loadStoreImmediateUnsigned size regsizeWord memop offset rn rt hsize hreg
      hrn hrt hshape) hbytes]

/-! ## `loadStoreImmediate`: signed (unscaled) offset -/

/-- The 32-bit word of a signed-offset memory instruction, over width-typed
atoms. -/
def loadStoreSignedWord (size : BitVec 2) (opc : BitVec 2) (imm9 : BitVec 9)
    (rn rt : BitVec 5) : BitVec 32 :=
  (((((((((0 : BitVec 32) <<< 2 ||| size.setWidth 32) <<< 6 ||| (56 : BitVec 32)) <<< 2 |||
      opc.setWidth 32) <<< 1 ||| (0 : BitVec 32)) <<< 9 ||| imm9.setWidth 32) <<< 1 |||
      (0 : BitVec 32)) <<< 1 ||| (0 : BitVec 32)) <<< 5 ||| rn.setWidth 32) <<< 5 |||
    (rt.setWidth 32)

/-- The `fields` composition of a signed-offset memory instruction is the
width-typed word. -/
theorem fields_loadStoreImmediateSigned (size opc imm9 rn rt : Nat) :
    fields [(2, size), (6, 56), (2, opc), (1, 0), (9, imm9), (1, 0), (1, 0), (5, rn),
      (5, rt)] = loadStoreSignedWord (BitVec.ofNat 2 size) (BitVec.ofNat 2 opc)
        (BitVec.ofNat 9 imm9) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed signed-offset memory word. -/
theorem decode_loadStoreImmediateSigned_word (size : BitVec 2) (opc : BitVec 2)
    (imm9 : BitVec 9) (rn rt : BitVec 5) :
    decodeInsn32 (loadStoreSignedWord size opc imm9 rn rt)
      = some (.loadStoreImmediate size.toNat (opc.toNat = 3)
          (if opc.toNat ≠ 0 then .load else .store) false false
          (sextToWord 9 (BitVec.ofNat 64 imm9.toNat)) rn.toNat rt.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h2 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h3 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h4 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h5 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h6 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h7 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h8 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h9 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h10 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h11 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h12 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h13 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h14 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h15 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have h16 : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x3D000000 0x39000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [loadStoreSignedWord] at hb
    simp at hb
  have hK : bitMatches (loadStoreSignedWord size opc imm9 rn rt) 0x3F000000 0x38000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hK,
    Bool.false_eq_true, if_true, if_false]
  have f22 : part (loadStoreSignedWord size opc imm9 rn rt) 22 2 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  have f12 : part (loadStoreSignedWord size opc imm9 rn rt) 12 9 = imm9.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  have f30 : part (loadStoreSignedWord size opc imm9 rn rt) 30 2 = size.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  have f5 : part (loadStoreSignedWord size opc imm9 rn rt) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  have f0 : part (loadStoreSignedWord size opc imm9 rn rt) 0 5 = rt.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [loadStoreSignedWord]
    interval_cases i <;> simp
  simp only [f30, f22, f12, f5, f0]

/-- The signed-offset memory word decodes back to the encoded instruction,
whenever the offset fits in nine signed bits. -/
theorem decode_encode_loadStoreImmediateSigned32 (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat)
    (hsize : size < 4) (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hfits : fitsSigned 9 offset = true) :
    decodeInsn32 (fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
      (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)])
      = some (.loadStoreImmediate size regsizeWord memop false false offset rn rt) := by
  rw [fields_loadStoreImmediateSigned size (loadStoreOpc memop) (offset.toNat % 512) rn rt,
    decode_loadStoreImmediateSigned_word (BitVec.ofNat 2 size)
      (BitVec.ofNat 2 (loadStoreOpc memop)) (BitVec.ofNat 9 (offset.toNat % 512))
      (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)]
  have hs : (BitVec.ofNat 2 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ho : loadStoreOpc memop < 4 := by
    cases memop <;> simp [loadStoreOpc]
  have ho' : (BitVec.ofNat 2 (loadStoreOpc memop)).toNat = loadStoreOpc memop := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  have hi : (BitVec.ofNat 9 (offset.toNat % 512)).toNat = offset.toNat % 512 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  have hn : (BitVec.ofNat 5 rn).toNat = rn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn]
  have ht : (BitVec.ofNat 5 rt).toNat = rt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrt]
  rw [hs, ho', hi, hn, ht, show (512 : Nat) = 2 ^ 9 from by norm_num,
    sextToWord_ofNat_mod 9 (by norm_num) offset hfits]
  cases memop <;> simp [loadStoreOpc, hreg]

/-- The 64-bit carrier word emitted for a signed-offset memory instruction. -/
theorem encodeInsn_loadStoreImmediateSigned (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat)
    (hfits : fitsSigned 9 offset = true) :
    encodeInsn (.loadStoreImmediate size regsizeWord memop false false offset rn rt) =
      some ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
        (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64) := by
  unfold encodeInsn
  rw [show encodeInsn32 (.loadStoreImmediate size regsizeWord memop false false offset rn rt)
      = some (fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
          (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]) by
    simp only [encodeInsn32, loadStoreOpc]
    cases memop <;>
      (rw [if_neg (by simp), if_pos hfits]
       try simp)]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_loadStoreImmediateSigned (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat) (hsize : size < 4)
    (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hfits : fitsSigned 9 offset = true) :
    decodeInsn ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
      (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64)
      = some (.loadStoreImmediate size regsizeWord memop false false offset rn rt) := by
  rw [show decodeInsn ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
      (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64)
      = decodeInsn32 (fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
          (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]) by
    simp [decodeInsn]]
  exact decode_encode_loadStoreImmediateSigned32 size regsizeWord memop offset rn rt hsize
    hreg hrn hrt hfits

/-- `decodeInsn` inverts `encodeInsn` on a signed-offset memory instruction. -/
theorem decode_encode_loadStoreImmediateSignedInsn (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat) (hsize : size < 4)
    (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hfits : fitsSigned 9 offset = true) :
    decodeInsn ((encodeInsn (.loadStoreImmediate size regsizeWord memop false false
      offset rn rt)).getD 0)
      = some (.loadStoreImmediate size regsizeWord memop false false offset rn rt) := by
  rw [encodeInsn_loadStoreImmediateSigned size regsizeWord memop offset rn rt hfits,
    Option.getD_some]
  exact decode_encode_loadStoreImmediateSigned size regsizeWord memop offset rn rt hsize hreg
    hrn hrt hfits

/-- One machine step executes a signed-offset memory instruction whose bytes are
at the PC. -/
theorem arm8Next_loadStoreImmediateSigned (s : Arm8State) (d : BitVec 64 → Prop)
    (size : Nat) (regsizeWord : Bool) (memop : MemOp) (offset : W) (rn rt : Nat)
    (hsize : size < 4) (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hfits : fitsSigned 9 offset = true)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size regsizeWord memop false false offset rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size regsizeWord memop false false offset rn rt) := by
  rw [arm8Next_encodeBytes s (.loadStoreImmediate size regsizeWord memop false false
      offset rn rt)
    ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
      (9, offset.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64) d
    (encodeInsn_loadStoreImmediateSigned size regsizeWord memop offset rn rt hfits)
    (decode_encode_loadStoreImmediateSigned size regsizeWord memop offset rn rt hsize hreg
      hrn hrt hfits) hbytes]

/-! ## `loadStoreImmediate`: combined inverse -/

/-- `decodeInsn` inverts `encodeInsn` on every emitted memory shape: the encoder
picks the scaled unsigned offset when the offset is exactly that scaled immediate,
and the unscaled signed form otherwise.  The `unsignedOffset` field of the
instruction is the encoder's own decision for the offset. -/
theorem decode_encode_loadStoreImmediate (size : Nat) (regsizeWord : Bool)
    (memop : MemOp) (offset : W) (rn rt : Nat) (hsize : size < 4)
    (hreg : regsizeWord = false) (hrn : rn < 32) (hrt : rt < 32)
    (hform : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size
      ∨ fitsSigned 9 offset = true) :
    decodeInsn ((encodeInsn (.loadStoreImmediate size regsizeWord memop false
        (offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size) offset rn rt)).getD 0)
      = some (.loadStoreImmediate size regsizeWord memop false
          (offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size) offset rn rt) := by
  by_cases h : offset = (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size
  · rw [decide_eq_true h]
    exact decode_encode_loadStoreImmediateUnsignedInsn size regsizeWord memop offset rn rt hsize
      hreg hrn hrt h
  · rcases hform with hshape | hfits
    · exact absurd hshape h
    · rw [decide_eq_false h]
      exact decode_encode_loadStoreImmediateSignedInsn size regsizeWord memop offset rn rt hsize
        hreg hrn hrt hfits

end Flapjack.Compiler.Encoders.Arm8
