import Flapjack.RiscV.CorrectnessEncoding.Arithmetic
import Mathlib.Tactic.NormNum
namespace Flapjack.RiscV.TargetProof.SubOverflow
set_option autoImplicit false
/-- The literal final SRLI63 extracts the word64 sign bit. This is local
composition infrastructure, with no separately named HOL declaration. -/
theorem shift_msb (x : BitVec 64) :
    x >>> 63 = (if x.msb then (1 : BitVec 64) else 0) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have zero : (0 : BitVec 64).toNat = 0 := by decide
  have one : (1 : BitVec 64).toNat = 1 := by decide
  simp only [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  split <;> simp only [zero, one]
  all_goals norm_num [Nat.shiftRight_eq_div_pow] at *
  all_goals omega

/-- HOL signed subtraction overflow is exactly differing operand signs with a
result sign different from the subtrahend's complement, i.e. equal to the
subtrahend's sign. No separately named HOL declaration is claimed. -/
theorem overflow_sign (a b : BitVec 64) :
    ((a - b).toInt ≠ a.toInt - b.toInt) ↔
      ((a.msb ^^ b.msb) && !(b.msb ^^ (a-b).msb)) = true := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := (a-b).isLt
  have diff : (a-b).toNat = (2^64 - b.toNat + a.toNat) % 2^64 := BitVec.toNat_sub _ _
  have sa := BitVec.msb_eq_decide a
  have sb := BitVec.msb_eq_decide b
  have sc := BitVec.msb_eq_decide (a-b)
  cases ea : a.msb <;> cases eb : b.msb <;> cases ec : (a-b).msb
  all_goals simp only [BitVec.toInt_eq_msb_cond, ea, eb, ec, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  all_goals simp [ea, eb, ec] at sa sb sc
  all_goals norm_num at *
  all_goals omega

/-- The actual XOR/SUB/XOR/XORI/AND/SRLI sequence yields the original AsmSem
signed-overflow flag for arbitrary word64 operands. Untagged local composition
infrastructure; no additional operand or overflow premise is assumed. -/
theorem flag_value (a b : BitVec 64) :
    ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))) >>> 63 =
      (if (a-b).toInt ≠ a.toInt-b.toInt then (1 : BitVec 64) else 0) := by
  have sign : ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))).msb = true ↔
      (a-b).toInt ≠ a.toInt-b.toInt := by
    have positive : decide (0 < 64) = true := rfl
    simpa only [positive, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor,
      Bool.true_and] using (overflow_sign a b).symm
  rw [shift_msb]
  by_cases h : ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))).msb = true
  · simp only [h, ↓reduceIte, if_pos (sign.mp h)]
  · simp only [if_neg h, if_neg (fun k => h (sign.mpr k))]
end Flapjack.RiscV.TargetProof.SubOverflow
