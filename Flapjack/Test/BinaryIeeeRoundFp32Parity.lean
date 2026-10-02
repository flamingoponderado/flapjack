import Flapjack.Misc.BinaryIeeeRoundFp32

/-! Kernel replay of50 freshly captured original binary32 nearest-even outputs.
Each proof rewrites the complete choice specification through its full-domain
agreement theorem, then evaluates the proved algorithm. These supplemental
regressions do not assert HOL-real equivalence or discharge directed modes. -/
set_option maxRecDepth 200000
namespace Flapjack.Test.BinaryIeeeRoundFp32Parity
open Flapjack

private def encode (f : HolFloat 23 8) : BitVec 32 :=
  (f.sign ++ f.exponent ++ f.significand).cast (by decide)

-- Original rte32_zero_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((0 : Rat) / 1)) = 0 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_zero_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((0 : Rat) / 1)) = 0x80000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_one_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((1 : Rat) / 1)) = 0x3F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_one_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((1 : Rat) / 1)) = 0x3F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_one_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-1 : Rat) / 1)) = 0xBF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_one_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-1 : Rat) / 1)) = 0xBF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_tie_even_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((16777217 : Rat) / 1)) = 0x4B800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_tie_even_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((16777217 : Rat) / 1)) = 0x4B800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_tie_odd_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((16777219 : Rat) / 1)) = 0x4B800002 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_tie_odd_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((16777219 : Rat) / 1)) = 0x4B800002 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_tie_even_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-16777217 : Rat) / 1)) = 0xCB800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_tie_even_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-16777217 : Rat) / 1)) = 0xCB800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_tie_odd_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-16777219 : Rat) / 1)) = 0xCB800002 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_tie_odd_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-16777219 : Rat) / 1)) = 0xCB800002 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_binade_boundary_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((33554431 : Rat) / 1)) = 0x4C000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_binade_boundary_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((33554431 : Rat) / 1)) = 0x4C000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_u32max_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((4294967295 : Rat) / 1)) = 0x4F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_u32max_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((4294967295 : Rat) / 1)) = 0x4F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_u64max_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((18446744073709551615 : Rat) / 1)) = 0x5F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_u64max_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((18446744073709551615 : Rat) / 1)) = 0x5F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_i64min_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-9223372036854775808 : Rat) / 1)) = 0xDF000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_i64min_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-9223372036854775808 : Rat) / 1)) = 0xDF000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_half_subnormal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_half_subnormal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0x80000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_half_subnormal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_half_subnormal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-1 : Rat) / 1427247692705959881058285969449495136382746624)) = 0x80000000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_min_subnormal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((1 : Rat) / 713623846352979940529142984724747568191373312)) = 1 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_min_subnormal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((1 : Rat) / 713623846352979940529142984724747568191373312)) = 1 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_min_subnormal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-1 : Rat) / 713623846352979940529142984724747568191373312)) = 0x80000001 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_min_subnormal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-1 : Rat) / 713623846352979940529142984724747568191373312)) = 0x80000001 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_subnormal_tie_odd_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((3 : Rat) / 1427247692705959881058285969449495136382746624)) = 2 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_subnormal_tie_odd_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((3 : Rat) / 1427247692705959881058285969449495136382746624)) = 2 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_max_subnormal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((8388607 : Rat) / 713623846352979940529142984724747568191373312)) = 0x7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_max_subnormal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((8388607 : Rat) / 713623846352979940529142984724747568191373312)) = 0x7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_min_normal_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((1 : Rat) / 85070591730234615865843651857942052864)) = 0x800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_min_normal_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((1 : Rat) / 85070591730234615865843651857942052864)) = 0x800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_max_finite_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((340282346638528859811704183484516925440 : Rat) / 1)) = 0x7F7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_max_finite_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((340282346638528859811704183484516925440 : Rat) / 1)) = 0x7F7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_threshold_minus_one_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((340282356779733661637539395458142568447 : Rat) / 1)) = 0x7F7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_threshold_minus_one_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((340282356779733661637539395458142568447 : Rat) / 1)) = 0x7F7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_threshold_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((340282356779733661637539395458142568448 : Rat) / 1)) = 0x7F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_threshold_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((340282356779733661637539395458142568448 : Rat) / 1)) = 0x7F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_overflow_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((340282366920938463463374607431768211456 : Rat) / 1)) = 0x7F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_overflow_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((340282366920938463463374607431768211456 : Rat) / 1)) = 0x7F800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_threshold_plus_one_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-340282356779733661637539395458142568447 : Rat) / 1)) = 0xFF7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_threshold_plus_one_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-340282356779733661637539395458142568447 : Rat) / 1)) = 0xFF7FFFFF := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_threshold_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-340282356779733661637539395458142568448 : Rat) / 1)) = 0xFF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_threshold_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-340282356779733661637539395458142568448 : Rat) / 1)) = 0xFF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_overflow_positive_zero
example : encode (holFloatRound .roundTiesToEven false ((-340282366920938463463374607431768211456 : Rat) / 1)) = 0xFF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

-- Original rte32_negative_overflow_negative_zero
example : encode (holFloatRound .roundTiesToEven true ((-340282366920938463463374607431768211456 : Rat) / 1)) = 0xFF800000 := by
  rw [holFloatRound_rte_fp32]
  decide +kernel

end Flapjack.Test.BinaryIeeeRoundFp32Parity
