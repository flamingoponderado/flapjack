(*
  Direct HOL-EVAL fixture for float_round roundTiesToEven at binary64
  (HOL/src/floating-point/binary_ieeeScript.sml:411-515), compared by
  Flapjack/Test/BinaryIeeeRoundFp64Parity.lean against the computable
  holFp64RoundTiesToEven (proved equal to HOL float_round in
  Flapjack/Misc/BinaryIeeeRoundFp64.lean).  binary_ieeeLib extends EVAL with
  round_CONV.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [float_to_fp64_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

fun r label toneg x =
  print_eval label
    ``float_to_fp64 (float_round roundTiesToEven ^toneg ^x : (52, 11) float)``;

val _ = r "third" ``F`` ``1r / 3``;
val _ = r "tenth" ``F`` ``1r / 10``;
val _ = r "neg_third" ``F`` ``-1r / 3``;
val _ = r "one" ``F`` ``1r``;
val _ = r "tie_down_even" ``F`` ``1r + 1 / 2 pow 53``;
val _ = r "tie_up_even" ``F`` ``1r + 3 / 2 pow 53``;
val _ = r "near_tie_up" ``F`` ``1r + 1 / 2 pow 53 + 1 / 2 pow 80``;
val _ = r "sub_half_ulp" ``F`` ``1r / 2 pow 1075``;
val _ = r "sub_half_ulp_neg" ``T`` ``-1r / 2 pow 1075``;
val _ = r "sub_three_half" ``F`` ``3r / 2 pow 1075``;
val _ = r "sub_tiny_neg" ``F`` ``-1r / 2 pow 1100``;
val _ = r "zero_toneg" ``T`` ``0r``;
val _ = r "zero_pos" ``F`` ``0r``;
val _ = r "largest_exact" ``F`` ``largest (:52 # 11)``;
val _ = r "below_threshold" ``F`` ``threshold (:52 # 11) - 1``;
val _ = r "at_threshold" ``F`` ``threshold (:52 # 11)``;
val _ = r "neg_threshold" ``F`` ``-threshold (:52 # 11)``;
val _ = r "min_normal" ``F`` ``1r / 2 pow 1022``;
val _ = r "max_subnormal_up" ``F`` ``1r / 2 pow 1022 - 1 / 2 pow 1076``;
val _ = r "big_odd" ``F`` ``&(2 EXP 60 + 2 EXP 7 + 1) : real``;
