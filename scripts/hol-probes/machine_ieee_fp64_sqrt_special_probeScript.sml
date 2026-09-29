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

val _ = print_eval "sqrt_pinf" ``fp64_sqrt roundTiesToEven (0x7FF0000000000000w : word64)``;
val _ = print_eval "sqrt_nz" ``fp64_sqrt roundTiesToEven (0x8000000000000000w : word64)``;
