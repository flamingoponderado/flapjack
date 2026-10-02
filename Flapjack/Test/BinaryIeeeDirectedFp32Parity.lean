import Flapjack.Misc.BinaryIeeeDirectedFp32

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
