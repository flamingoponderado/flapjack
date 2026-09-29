(*
  Direct HOL-EVAL fixture for the non-rounding branches of the binary64
  arithmetic rendered in Flapjack/Misc/BinaryIeeeArith.lean and the tagged
  fpSem fpfma (Flapjack/FpSemHOL.lean): infinity and zero-divisor cases of
  fp64_add/sub/mul/div and fpfma.  binary_ieeeLib extends EVAL with the IEEE
  conversions; the machine_ieee fp64 and fpSem definitions are added.
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

val one = ``0x3FF0000000000000w : word64``;
val two = ``0x4000000000000000w : word64``;
val negone = ``0xBFF0000000000000w : word64``;
val pz = ``0x0w : word64``;
val nz = ``0x8000000000000000w : word64``;
val pinf = ``0x7FF0000000000000w : word64``;
val ninf = ``0xFFF0000000000000w : word64``;

val _ = print_eval "add_pinf_one" ``fp64_add roundTiesToEven ^pinf ^one``;
val _ = print_eval "add_one_ninf" ``fp64_add roundTiesToEven ^one ^ninf``;
val _ = print_eval "add_pinf_pinf" ``fp64_add roundTiesToEven ^pinf ^pinf``;
val _ = print_eval "sub_one_pinf" ``fp64_sub roundTiesToEven ^one ^pinf``;
val _ = print_eval "sub_ninf_pinf" ``fp64_sub roundTiesToEven ^ninf ^pinf``;
val _ = print_eval "mul_pinf_negone" ``fp64_mul roundTiesToEven ^pinf ^negone``;
val _ = print_eval "mul_ninf_ninf" ``fp64_mul roundTiesToEven ^ninf ^ninf``;
val _ = print_eval "div_one_pinf" ``fp64_div roundTiesToEven ^one ^pinf``;
val _ = print_eval "div_negone_pinf" ``fp64_div roundTiesToEven ^negone ^pinf``;
val _ = print_eval "div_pinf_negone" ``fp64_div roundTiesToEven ^pinf ^negone``;
val _ = print_eval "div_one_pz" ``fp64_div roundTiesToEven ^one ^pz``;
val _ = print_eval "div_negone_pz" ``fp64_div roundTiesToEven ^negone ^pz``;
val _ = print_eval "div_one_nz" ``fp64_div roundTiesToEven ^one ^nz``;
val _ = print_eval "fma_pinf_product" ``fpfma ^one ^pinf ^two``;
val _ = print_eval "fma_ninf_addend" ``fpfma ^ninf ^one ^one``;
val _ = print_eval "fma_neg_inf_product" ``fpfma ^one ^ninf ^two``;
