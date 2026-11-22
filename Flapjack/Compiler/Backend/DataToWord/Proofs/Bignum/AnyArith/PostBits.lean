module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Multiword
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation

@[expose] public section

/-! Word arithmetic for the result checks of `AnyArith_code` (Flapjack-only
helpers following the HOL proof's small-result cases). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Misc.Multiword

theorem mcHeader_eq {width : Nat} [NeZero width] (v : Int) :
    mcHeader (i2mw v : Bool × List (BitVec width)) =
      BitVec.ofNat width ((i2mw v : Bool × List (BitVec width)).2.length * 2) +
        if decide (v < 0) then 1 else 0 := by
  simp [i2mw, mcHeader]

theorem ofNat_inj {width : Nat} (N M : Nat) (hN : N < 2 ^ width) (hM : M < 2 ^ width) :
    BitVec.ofNat width N = BitVec.ofNat width M ↔ N = M := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hM] using this
  · intro h; rw [h]

/-- The header is `2` or `3` exactly for a single positive or negative digit. -/
theorem mcHeader_two_three {width : Nat} [NeZero width] (v : Int)
    (hlen : 2 * (i2mw v : Bool × List (BitVec width)).2.length + 1 < 2 ^ width)
    (w4 : 4 < 2 ^ width) :
    (mcHeader (i2mw v : Bool × List (BitVec width)) = 2 ↔
      ¬ v < 0 ∧ (i2mw v : Bool × List (BitVec width)).2.length = 1) ∧
    (mcHeader (i2mw v : Bool × List (BitVec width)) = 3 ↔
      v < 0 ∧ (i2mw v : Bool × List (BitVec width)).2.length = 1) := by
  rw [mcHeader_eq]
  generalize (i2mw v : Bool × List (BitVec width)).2.length = L at hlen ⊢
  have e2 : (2 : BitVec width) = BitVec.ofNat width 2 := rfl
  have e3 : (3 : BitVec width) = BitVec.ofNat width 3 := rfl
  have e1 : (1 : BitVec width) = BitVec.ofNat width 1 := rfl
  have e0 : (0 : BitVec width) = BitVec.ofNat width 0 := rfl
  by_cases hv : v < 0
  · simp only [hv, decide_true, if_true, not_true_eq_false, false_and, true_and]
    rw [e1, ← BitVec.ofNat_add, e2, e3, ofNat_inj _ _ (by omega) (by omega),
      ofNat_inj _ _ (by omega) (by omega)]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro h <;> (try simp only at h) <;> omega
  · simp only [hv, decide_false, Bool.false_eq_true, if_false, not_false_eq_true, true_and,
      false_and]
    rw [e0, ← BitVec.ofNat_add, e2, e3, ofNat_inj _ _ (by omega) (by omega),
      ofNat_inj _ _ (by omega) (by omega)]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro h <;> (try simp only at h) <;> omega


theorem i2mw_single {width : Nat} [NeZero width] (v : Int)
    (h : (i2mw v : Bool × List (BitVec width)).2.length = 1) :
    (i2mw v : Bool × List (BitVec width)).2 = [BitVec.ofNat width v.natAbs] ∧
      v.natAbs < 2 ^ width ∧ v ≠ 0 := by
  simp only [i2mw] at h ⊢
  have nz : v.natAbs ≠ 0 := by
    intro z; rw [z, n2mw, if_pos rfl] at h; simp at h
  rw [n2mw, if_neg nz] at h ⊢
  simp only [List.length_cons] at h
  have h : n2mw (width := width) (v.natAbs / 2 ^ width) = [] := List.length_eq_zero_iff.1 (by omega)
  have lt : v.natAbs < 2 ^ width := by
    by_contra ge
    have : v.natAbs / 2 ^ width ≠ 0 := by
      rw [Ne, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]; omega
    rw [n2mw, if_neg this] at h; simp at h
  refine ⟨?_, lt, by omega⟩
  rw [Nat.mod_eq_of_lt lt, h]

theorem ushiftRight_eq_zero_iff {width : Nat} (x : BitVec width) (k : Nat) :
    x >>> k = 0 ↔ x.toNat < 2 ^ k := by
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]

/-- Small positive result checks (HOL: the `v1 >>> (dimindex - 3) = 0w` step). -/
theorem small_pos_bits {width : Nat} [NeZero width] (good : goodDimindex width) (v : Int)
    (pos : ¬ v < 0) (single : (i2mw v : Bool × List (BitVec width)).2.length = 1) :
    (smallInt width v ↔ (BitVec.ofNat width v.natAbs) >>> (width - 3) = 0) ∧
    (smallInt width v → (BitVec.ofNat width v.natAbs) <<< (2 : Nat) = (smallnum v : BitVec width)) := by
  obtain ⟨_, lt, _⟩ := i2mw_single v single
  have w3 : 2 ^ width / 8 = 2 ^ (width - 3) := by rcases good with h | h <;> subst h <;> norm_num
  rw [ushiftRight_eq_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]
  unfold smallInt smallnum
  simp only [pos, if_false, Int.ofNat_eq_natCast]
  constructor
  · constructor
    · intro ⟨_, h⟩; omega
    · intro h; constructor <;> omega
  · intro _
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    congr 1; omega

/-- Small negative result checks (HOL: the `(v1 + -1w) >>> (dimindex - 3) = 0w` step). -/
theorem small_neg_bits {width : Nat} [NeZero width] (good : goodDimindex width) (v : Int)
    (neg : v < 0) (single : (i2mw v : Bool × List (BitVec width)).2.length = 1) :
    (smallInt width v ↔ (BitVec.ofNat width v.natAbs - 1) >>> (width - 3) = 0) ∧
    (smallInt width v → 0 - (BitVec.ofNat width v.natAbs) <<< (2 : Nat) = (smallnum v : BitVec width)) := by
  obtain ⟨_, lt, _⟩ := i2mw_single v single
  have w3 : 2 ^ width / 8 = 2 ^ (width - 3) := by rcases good with h | h <;> subst h <;> norm_num
  have sub1 : (BitVec.ofNat width v.natAbs - 1).toNat = v.natAbs - 1 := by
    have one : (1 : BitVec width).toNat = 1 := by
      show (BitVec.ofNat width 1).toNat = 1
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))
    rw [BitVec.toNat_sub, one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt,
      show 2 ^ width - 1 + v.natAbs = 2 ^ width + (v.natAbs - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
  rw [ushiftRight_eq_zero_iff, sub1]
  unfold smallInt smallnum
  simp only [neg, if_true, Int.ofNat_eq_natCast]
  constructor
  · constructor
    · intro ⟨h, _⟩; omega
    · intro h; constructor <;> omega
  · intro _
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    congr 1; omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
