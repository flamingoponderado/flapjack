(*
  Direct HOL-EVAL fixture for rounded finite results of the binary64
  arithmetic rendered in Flapjack/Misc/BinaryIeeeArith.lean and the tagged
  fpSem fpfma (Flapjack/FpSemHOL.lean), checked through the computable
  roundTiesToEven equivalence (Flapjack/Misc/BinaryIeeeArithFp64.lean).
  binary_ieeeLib extends EVAL with the IEEE conversions.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "fpSemTheory";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory fpSemTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_add_def,
  fp64_sub_def, fp64_mul_def, fp64_div_def, fp64_mul_add_def, fpfma_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val tenth = ``0x3FB999999999999Aw : word64``;
val fifth = ``0x3FC999999999999Aw : word64``;
val one = ``0x3FF0000000000000w : word64``;
val two = ``0x4000000000000000w : word64``;
val three = ``0x4008000000000000w : word64``;
val ten = ``0x4024000000000000w : word64``;
val negone = ``0xBFF0000000000000w : word64``;
val pz = ``0x0w : word64``;
val nz = ``0x8000000000000000w : word64``;
val sub1 = ``0x1w : word64``;
val maxfin = ``0x7FEFFFFFFFFFFFFFw : word64``;
val eps = ``0x3CA0000000000000w : word64``;

val _ = print_eval "add_tenth_fifth" ``fp64_add roundTiesToEven ^tenth ^fifth``;
val _ = print_eval "add_one_halfulp" ``fp64_add roundTiesToEven ^one ^eps``;
val _ = print_eval "add_pz_nz" ``fp64_add roundTiesToEven ^pz ^nz``;
val _ = print_eval "add_nz_nz" ``fp64_add roundTiesToEven ^nz ^nz``;
val _ = print_eval "add_max_max" ``fp64_add roundTiesToEven ^maxfin ^maxfin``;
val _ = print_eval "sub_one_one" ``fp64_sub roundTiesToEven ^one ^one``;
val _ = print_eval "sub_nz_pz" ``fp64_sub roundTiesToEven ^nz ^pz``;
val _ = print_eval "sub_three_tenth" ``fp64_sub roundTiesToEven ^three ^tenth``;
val _ = print_eval "mul_tenth_three" ``fp64_mul roundTiesToEven ^tenth ^three``;
val _ = print_eval "mul_negone_pz" ``fp64_mul roundTiesToEven ^negone ^pz``;
val _ = print_eval "mul_max_two" ``fp64_mul roundTiesToEven ^maxfin ^two``;
val _ = print_eval "mul_sub1_half" ``fp64_mul roundTiesToEven ^sub1 0x3FE0000000000000w``;
val _ = print_eval "div_one_three" ``fp64_div roundTiesToEven ^one ^three``;
val _ = print_eval "div_one_ten" ``fp64_div roundTiesToEven ^one ^ten``;
val _ = print_eval "div_negone_three" ``fp64_div roundTiesToEven ^negone ^three``;
val _ = print_eval "div_sub1_two" ``fp64_div roundTiesToEven ^sub1 ^two``;
val _ = print_eval "fma_tenth_ten_negone" ``fpfma ^negone ^tenth ^ten``;
val _ = print_eval "fma_one_one_one" ``fpfma ^one ^one ^one``;
val _ = print_eval "fma_zero_sign" ``fpfma ^pz ^negone ^pz``;
val _ = print_eval "fma_cancel" ``fpfma ^negone ^one ^one``;
