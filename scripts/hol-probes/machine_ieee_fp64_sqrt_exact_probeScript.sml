(*
  Direct HOL-EVAL fixture for binary64 fp64_sqrt roundTiesToEven on exact
  squares (HOL/src/floating-point/binary_ieeeScript.sml:574-585), compared by
  Flapjack/Test/MachineIeeeSqrtExactParity.lean through the computable sqrt
  rounding proved equal to the rational-cut specification in
  Flapjack/Misc/BinaryIeeeSqrtFp64.lean.  isqrtLib's iSQRT_COMPUTE_CONV
  proves sqrt of exact squares (and quotients of them) from
  realTheory.POW_2_SQRT, so only exact-square inputs are probed.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "isqrtLib";
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

fun sq label w = print_eval label ``fp64_sqrt roundTiesToEven ^w``;

val _ = sq "sqrt_four" ``0x4010000000000000w : word64``;
val _ = sq "sqrt_quarter" ``0x3FD0000000000000w : word64``;
val _ = sq "sqrt_nine" ``0x4022000000000000w : word64``;
val _ = sq "sqrt_one" ``0x3FF0000000000000w : word64``;
val _ = sq "sqrt_pz" ``0x0w : word64``;
val _ = sq "sqrt_min_sub" ``0x1w : word64``;
val _ = sq "sqrt_2p1022" ``0x7FD0000000000000w : word64``;
