(*
  Direct HOL-EVAL fixture for the choice-free branches of binary64 fp64_sqrt
  rendered in Flapjack/Misc/BinaryIeeeSqrt.lean
  (HOL/src/floating-point/binary_ieeeScript.sml:574-585): positive infinity
  and negative zero.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_sqrt_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val _ = print_eval "sqrt_zero_pinf" ``fp64_sqrt roundTowardZero (0x7FF0000000000000w : word64)``;
val _ = print_eval "sqrt_zero_nz" ``fp64_sqrt roundTowardZero (0x8000000000000000w : word64)``;
val _ = print_eval "sqrt_positive_pinf" ``fp64_sqrt roundTowardPositive (0x7FF0000000000000w : word64)``;
val _ = print_eval "sqrt_positive_nz" ``fp64_sqrt roundTowardPositive (0x8000000000000000w : word64)``;
val _ = print_eval "sqrt_negative_pinf" ``fp64_sqrt roundTowardNegative (0x7FF0000000000000w : word64)``;
val _ = print_eval "sqrt_negative_nz" ``fp64_sqrt roundTowardNegative (0x8000000000000000w : word64)``;
val _ = print_eval "sqrt_negative_flags_all_modes" ``FST (float_sqrt mode (fp64_to_float (0xC010000000000000w : word64))) = invalidop_flags``;
val _ = print_eval "sqrt_quiet_nan_flags_all_modes" ``FST (float_sqrt mode (fp64_to_float (0x7FF8000000000001w : word64))) = clear_flags``;
