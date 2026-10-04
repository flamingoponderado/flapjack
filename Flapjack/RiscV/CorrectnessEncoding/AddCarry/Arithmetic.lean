import Flapjack.RiscV.CorrectnessEncoding.Arithmetic
import Mathlib.Tactic.NormNum
namespace Flapjack.RiscV.TargetProof.AddCarry
open Flapjack RiscV.L3
set_option autoImplicit false
/-- Low sum of the two actual native additions; untagged arithmetic composition. -/
theorem sum_value (a b : BitVec 64) (c : Bool) :
    (a+b)+(if c then 1 else 0) =
      BitVec.ofNat 64 (a.toNat+b.toNat+(if c then 1 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  cases c <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
/-- Disjunction of the two actual native overflow flags equals the original
source carry test. No separately named HOL declaration is claimed. -/
theorem carry_value (a b : BitVec 64) (c : Bool) :
    holV2w 64 [BitVec.ult (a+b) b] |||
      holV2w 64 [BitVec.ult ((a+b)+(if c then 1 else 0)) (if c then 1 else 0)] =
      (if 18446744073709551616 ≤ a.toNat+b.toNat+(if c then 1 else 0)
       then (1 : BitVec 64) else 0) := by
  have flags : decide (18446744073709551616 ≤ a.toNat+b.toNat+(if c then 1 else 0)) =
      (BitVec.ult (a+b) b ||
        BitVec.ult ((a+b)+(if c then 1 else 0)) (if c then 1 else 0)) := by
    apply Bool.eq_iff_iff.mpr
    cases c <;> simp only [Bool.or_eq_true, BitVec.ult_eq_decide, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add]
    all_goals
      have ha := a.isLt
      have hb := b.isLt
      have zero : (0 : BitVec 64).toNat = 0 := by decide
      have one : (1 : BitVec 64).toNat = 1 := by decide
      simp only [zero, one]
      norm_num at *
      omega
  have result := (singleton_or
    (decide (18446744073709551616 ≤ a.toNat+b.toNat+(if c then 1 else 0)))
    (BitVec.ult (a+b) b)
    (BitVec.ult ((a+b)+(if c then 1 else 0)) (if c then 1 else 0))).mpr flags
  simpa using result.symm
end Flapjack.RiscV.TargetProof.AddCarry
