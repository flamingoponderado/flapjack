import Flapjack.Misc.BinaryIeeeDirectedFp32

/-! Kernel replay of50 freshly captured original binary32 toward-zero outputs.
Each proof rewrites the complete choice specification through its full-domain
agreement theorem, then evaluates the proved algorithm. These supplemental
regressions do not assert HOL-real equivalence or discharge finite upward/downward original conversion. -/
set_option maxRecDepth 200000
namespace Flapjack.Test.BinaryIeeeDirectedFp32Parity
open Flapjack

private def encode (f : HolFloat 23 8) : BitVec 32 :=
  (f.sign ++ f.exponent ++ f.significand).cast (by decide)

-- Original rtz32_zero_positive_zero
example : encode (holFloatRound .roundTowardZero false ((0 : Rat) / 1)) = 0 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_zero_negative_zero
example : encode (holFloatRound .roundTowardZero true ((0 : Rat) / 1)) = 2147483648 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 1)) = 1065353216 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 1)) = 1065353216 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 1)) = 3212836864 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 1)) = 3212836864 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_tie_even_positive_zero
example : encode (holFloatRound .roundTowardZero false ((16777217 : Rat) / 1)) = 1266679808 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_tie_even_negative_zero
example : encode (holFloatRound .roundTowardZero true ((16777217 : Rat) / 1)) = 1266679808 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_tie_odd_positive_zero
example : encode (holFloatRound .roundTowardZero false ((16777219 : Rat) / 1)) = 1266679809 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_tie_odd_negative_zero
example : encode (holFloatRound .roundTowardZero true ((16777219 : Rat) / 1)) = 1266679809 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_tie_even_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-16777217 : Rat) / 1)) = 3414163456 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_tie_even_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-16777217 : Rat) / 1)) = 3414163456 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_tie_odd_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-16777219 : Rat) / 1)) = 3414163457 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_tie_odd_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-16777219 : Rat) / 1)) = 3414163457 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_binade_boundary_positive_zero
example : encode (holFloatRound .roundTowardZero false ((33554431 : Rat) / 1)) = 1275068415 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_binade_boundary_negative_zero
example : encode (holFloatRound .roundTowardZero true ((33554431 : Rat) / 1)) = 1275068415 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_u32max_positive_zero
example : encode (holFloatRound .roundTowardZero false ((4294967295 : Rat) / 1)) = 1333788671 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_u32max_negative_zero
example : encode (holFloatRound .roundTowardZero true ((4294967295 : Rat) / 1)) = 1333788671 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_u64max_positive_zero
example : encode (holFloatRound .roundTowardZero false ((18446744073709551615 : Rat) / 1)) = 1602224127 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_u64max_negative_zero
example : encode (holFloatRound .roundTowardZero true ((18446744073709551615 : Rat) / 1)) = 1602224127 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_i64min_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-9223372036854775808 : Rat) / 1)) = 3741319168 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_i64min_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-9223372036854775808 : Rat) / 1)) = 3741319168 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_half_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_half_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 1427247692705959881058285969449495136382746624)) = 2147483648 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_half_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_half_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 1427247692705959881058285969449495136382746624)) = 2147483648 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_min_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 713623846352979940529142984724747568191373312)) = 1 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_min_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 713623846352979940529142984724747568191373312)) = 1 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_min_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 713623846352979940529142984724747568191373312)) = 2147483649 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_min_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 713623846352979940529142984724747568191373312)) = 2147483649 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_subnormal_tie_odd_positive_zero
example : encode (holFloatRound .roundTowardZero false ((3 : Rat) / 1427247692705959881058285969449495136382746624)) = 1 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_subnormal_tie_odd_negative_zero
example : encode (holFloatRound .roundTowardZero true ((3 : Rat) / 1427247692705959881058285969449495136382746624)) = 1 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_max_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((8388607 : Rat) / 713623846352979940529142984724747568191373312)) = 8388607 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_max_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((8388607 : Rat) / 713623846352979940529142984724747568191373312)) = 8388607 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_min_normal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 85070591730234615865843651857942052864)) = 8388608 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_min_normal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 85070591730234615865843651857942052864)) = 8388608 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_max_finite_positive_zero
example : encode (holFloatRound .roundTowardZero false ((340282346638528859811704183484516925440 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_max_finite_negative_zero
example : encode (holFloatRound .roundTowardZero true ((340282346638528859811704183484516925440 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_threshold_minus_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((340282356779733661637539395458142568447 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_threshold_minus_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((340282356779733661637539395458142568447 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_threshold_positive_zero
example : encode (holFloatRound .roundTowardZero false ((340282356779733661637539395458142568448 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_threshold_negative_zero
example : encode (holFloatRound .roundTowardZero true ((340282356779733661637539395458142568448 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_overflow_positive_zero
example : encode (holFloatRound .roundTowardZero false ((340282366920938463463374607431768211456 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_overflow_negative_zero
example : encode (holFloatRound .roundTowardZero true ((340282366920938463463374607431768211456 : Rat) / 1)) = 2139095039 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_threshold_plus_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-340282356779733661637539395458142568447 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_threshold_plus_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-340282356779733661637539395458142568447 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_threshold_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-340282356779733661637539395458142568448 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_threshold_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-340282356779733661637539395458142568448 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_overflow_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-340282366920938463463374607431768211456 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

-- Original rtz32_negative_overflow_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-340282366920938463463374607431768211456 : Rat) / 1)) = 4286578687 := by
  rw [holFloatRound_fp32]
  decide +kernel

end Flapjack.Test.BinaryIeeeDirectedFp32Parity


/-! Kernel regression checks for the computed directed algorithm. These rows
are not claimed as original HOL oracle evidence; finite directed conversion in
the pinned original is tracked separately on the certified-converter bead. -/
namespace Flapjack.Test.Binary32Directed
private def encode (f : HolFloat 23 8) : BitVec 32 :=
  (f.sign ++ f.exponent ++ f.significand).cast (by decide)

example : encode (holFloatRound .roundTowardZero false (16777217 : Rat)) = 1266679808 := by
  rw [holFloatRound_fp32]
  decide +kernel

example : encode (holFloatRound .roundTowardPositive false (16777217 : Rat)) = 1266679809 := by
  rw [holFloatRound_fp32]
  decide +kernel

example : encode (holFloatRound .roundTowardNegative false (16777217 : Rat)) = 1266679808 := by
  rw [holFloatRound_fp32]
  decide +kernel

example : encode (holFloatRound .roundTowardZero false (-16777217 : Rat)) = 3414163456 := by
  rw [holFloatRound_fp32]
  decide +kernel

example : encode (holFloatRound .roundTowardPositive false (-16777217 : Rat)) = 3414163456 := by
  rw [holFloatRound_fp32]
  decide +kernel

example : encode (holFloatRound .roundTowardNegative false (-16777217 : Rat)) = 3414163457 := by
  rw [holFloatRound_fp32]
  decide +kernel

end Flapjack.Test.Binary32Directed
