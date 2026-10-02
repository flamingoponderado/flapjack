import Flapjack.Misc.BinaryIeeeDirectedFp64

/-! Kernel directed tie regressions. These are not original HOL oracle rows;
the pinned original lacks finite upward/downward conversion. -/
namespace Flapjack.Test.Binary64Directed
private def encode (f : HolFloat 52 11) : BitVec 64 :=
  (f.sign ++ f.exponent ++ f.significand).cast (by decide)

example : encode (holFloatRound .roundTowardZero false (9007199254740993 : Rat)) = 4845873199050653696 := by
  rw [holFloatRound_fp64]
  decide +kernel

example : encode (holFloatRound .roundTowardPositive false (9007199254740993 : Rat)) = 4845873199050653697 := by
  rw [holFloatRound_fp64]
  decide +kernel

example : encode (holFloatRound .roundTowardNegative false (9007199254740993 : Rat)) = 4845873199050653696 := by
  rw [holFloatRound_fp64]
  decide +kernel

example : encode (holFloatRound .roundTowardZero false (-9007199254740993 : Rat)) = 14069245235905429504 := by
  rw [holFloatRound_fp64]
  decide +kernel

example : encode (holFloatRound .roundTowardPositive false (-9007199254740993 : Rat)) = 14069245235905429504 := by
  rw [holFloatRound_fp64]
  decide +kernel

example : encode (holFloatRound .roundTowardNegative false (-9007199254740993 : Rat)) = 14069245235905429505 := by
  rw [holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.Binary64Directed
