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


-- Fresh original rtz64_zero_positive_zero
example : encode (holFloatRound .roundTowardZero false ((0 : Rat) / 1)) = 0 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_zero_negative_zero
example : encode (holFloatRound .roundTowardZero true ((0 : Rat) / 1)) = 9223372036854775808 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 1)) = 4607182418800017408 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 1)) = 4607182418800017408 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_one_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 1)) = 13830554455654793216 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_one_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 1)) = 13830554455654793216 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_third_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 3)) = 4599676419421066581 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_third_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 3)) = 4599676419421066581 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_third_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 3)) = 13823048456275842389 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_third_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 3)) = 13823048456275842389 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_tie_even_positive_zero
example : encode (holFloatRound .roundTowardZero false ((9007199254740993 : Rat) / 1)) = 4845873199050653696 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_tie_even_negative_zero
example : encode (holFloatRound .roundTowardZero true ((9007199254740993 : Rat) / 1)) = 4845873199050653696 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_tie_odd_positive_zero
example : encode (holFloatRound .roundTowardZero false ((9007199254740995 : Rat) / 1)) = 4845873199050653697 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_tie_odd_negative_zero
example : encode (holFloatRound .roundTowardZero true ((9007199254740995 : Rat) / 1)) = 4845873199050653697 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_tie_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-9007199254740993 : Rat) / 1)) = 14069245235905429504 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_tie_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-9007199254740993 : Rat) / 1)) = 14069245235905429504 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_half_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568)) = 0 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_half_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568)) = 9223372036854775808 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_half_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-1 : Rat) / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568)) = 0 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_half_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-1 : Rat) / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568)) = 9223372036854775808 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_min_subnormal_positive_zero
example : encode (holFloatRound .roundTowardZero false ((1 : Rat) / 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)) = 1 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_min_subnormal_negative_zero
example : encode (holFloatRound .roundTowardZero true ((1 : Rat) / 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)) = 1 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_u64max_positive_zero
example : encode (holFloatRound .roundTowardZero false ((18446744073709551615 : Rat) / 1)) = 4895412794951729151 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_u64max_negative_zero
example : encode (holFloatRound .roundTowardZero true ((18446744073709551615 : Rat) / 1)) = 4895412794951729151 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_max_finite_positive_zero
example : encode (holFloatRound .roundTowardZero false ((179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368 : Rat) / 1)) = 9218868437227405311 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_max_finite_negative_zero
example : encode (holFloatRound .roundTowardZero true ((179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368 : Rat) / 1)) = 9218868437227405311 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_overflow_positive_zero
example : encode (holFloatRound .roundTowardZero false ((179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 : Rat) / 1)) = 9218868437227405311 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_overflow_negative_zero
example : encode (holFloatRound .roundTowardZero true ((179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 : Rat) / 1)) = 9218868437227405311 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_overflow_positive_zero
example : encode (holFloatRound .roundTowardZero false ((-179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 : Rat) / 1)) = 18442240474082181119 := by
  rw [holFloatRound_fp64]
  decide +kernel

-- Fresh original rtz64_negative_overflow_negative_zero
example : encode (holFloatRound .roundTowardZero true ((-179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 : Rat) / 1)) = 18442240474082181119 := by
  rw [holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.Binary64Directed
