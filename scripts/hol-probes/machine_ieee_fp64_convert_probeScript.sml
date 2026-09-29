(*
  Direct HOL-EVAL fixture for binary64 integer conversions rendered in
  Flapjack/Misc/BinaryIeeeConvert.lean (HOL/src/floating-point/
  binary_ieeeScript.sml:539-572 and the machine_ieeeLib fp64_to_int /
  int_to_fp64 encodings) and used by wordSem inst_def FPToInt / FPFromInt.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_to_int_def,
  int_to_fp64_def, real_to_fp64_def, real_to_float_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

fun ti label mode w = print_eval label ``fp64_to_int ^mode ^w``;
fun it label i = print_eval label ``int_to_fp64 roundTiesToEven (^i : int)``;

val _ = ti "to_int_2_5" ``roundTiesToEven`` ``0x4004000000000000w : word64``;
val _ = ti "to_int_3_5" ``roundTiesToEven`` ``0x400C000000000000w : word64``;
val _ = ti "to_int_neg_2_5" ``roundTiesToEven`` ``0xC004000000000000w : word64``;
val _ = ti "to_int_tenth" ``roundTiesToEven`` ``0x3FB999999999999Aw : word64``;
val _ = ti "to_int_neg_0_7" ``roundTiesToEven`` ``0xBFE6666666666666w : word64``;
val _ = ti "to_int_1e20" ``roundTiesToEven`` ``0x4415AF1D78B58C40w : word64``;
val _ = ti "to_int_nz" ``roundTiesToEven`` ``0x8000000000000000w : word64``;
val _ = ti "to_int_nan" ``roundTiesToEven`` ``0x7FF8000000000000w : word64``;
val _ = ti "to_int_inf" ``roundTiesToEven`` ``0x7FF0000000000000w : word64``;
val _ = ti "to_int_rtz_neg_2_5" ``roundTowardZero`` ``0xC004000000000000w : word64``;
val _ = ti "to_int_rtp_2_1" ``roundTowardPositive`` ``0x4000CCCCCCCCCCCDw : word64``;
val _ = ti "to_int_rtn_neg_2_1" ``roundTowardNegative`` ``0xC000CCCCCCCCCCCDw : word64``;
val _ = it "from_int_0" ``0i``;
val _ = it "from_int_neg1" ``-1i``;
val _ = it "from_int_2p53_1" ``9007199254740993i``;
val _ = it "from_int_2p53_3" ``9007199254740995i``;
val _ = it "from_int_big" ``&(2 EXP 1024) : int``;
val _ = it "from_int_neg_big" ``-(&(2 EXP 60 + 1)) : int``;
