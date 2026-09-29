(*
  Direct HOL-EVAL fixture for the binary64 comparison/sign operations rendered
  in Flapjack/Misc/BinaryIeee.lean and Flapjack/Misc/MachineIeee.lean
  (HOL/src/floating-point/binary_ieeeScript.sml, machine_ieeeScript.sml) and
  used by wordSem inst_def.  binary_ieeeLib extends EVAL with the IEEE
  conversions; the machine_ieee fp64 definitions are added to the compset.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_lessThan_def,
  fp64_lessEqual_def, fp64_equal_def, fp64_abs_def, fp64_negate_def];

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
val sub1 = ``0x1w : word64``;
val sub2 = ``0x2w : word64``;
val maxsub = ``0xFFFFFFFFFFFFFw : word64``;
val minnorm = ``0x10000000000000w : word64``;
val maxfin = ``0x7FEFFFFFFFFFFFFFw : word64``;
val pinf = ``0x7FF0000000000000w : word64``;
val ninf = ``0xFFF0000000000000w : word64``;
val qnan = ``0x7FF8000000000000w : word64``;
val snan = ``0x7FF0000000000001w : word64``;
val nqnan = ``0xFFF8000000000000w : word64``;

val _ = print_eval "lt_one_two" ``fp64_lessThan ^one ^two``;
val _ = print_eval "lt_two_one" ``fp64_lessThan ^two ^one``;
val _ = print_eval "lt_pz_nz" ``fp64_lessThan ^pz ^nz``;
val _ = print_eval "lt_nz_pz" ``fp64_lessThan ^nz ^pz``;
val _ = print_eval "lt_sub1_sub2" ``fp64_lessThan ^sub1 ^sub2``;
val _ = print_eval "lt_maxsub_minnorm" ``fp64_lessThan ^maxsub ^minnorm``;
val _ = print_eval "lt_ninf_sub1" ``fp64_lessThan ^ninf ^sub1``;
val _ = print_eval "lt_maxfin_pinf" ``fp64_lessThan ^maxfin ^pinf``;
val _ = print_eval "lt_pinf_pinf" ``fp64_lessThan ^pinf ^pinf``;
val _ = print_eval "lt_qnan_one" ``fp64_lessThan ^qnan ^one``;
val _ = print_eval "lt_one_snan" ``fp64_lessThan ^one ^snan``;
val _ = print_eval "lt_negone_pz" ``fp64_lessThan ^negone ^pz``;
val _ = print_eval "lt_pinf_ninf" ``fp64_lessThan ^pinf ^ninf``;
val _ = print_eval "le_pz_nz" ``fp64_lessEqual ^pz ^nz``;
val _ = print_eval "le_pinf_pinf" ``fp64_lessEqual ^pinf ^pinf``;
val _ = print_eval "le_qnan_qnan" ``fp64_lessEqual ^qnan ^qnan``;
val _ = print_eval "le_two_one" ``fp64_lessEqual ^two ^one``;
val _ = print_eval "le_ninf_ninf" ``fp64_lessEqual ^ninf ^ninf``;
val _ = print_eval "le_sub1_one" ``fp64_lessEqual ^sub1 ^one``;
val _ = print_eval "eq_pz_nz" ``fp64_equal ^pz ^nz``;
val _ = print_eval "eq_qnan_qnan" ``fp64_equal ^qnan ^qnan``;
val _ = print_eval "eq_one_one" ``fp64_equal ^one ^one``;
val _ = print_eval "eq_ninf_pinf" ``fp64_equal ^ninf ^pinf``;
val _ = print_eval "eq_sub1_sub2" ``fp64_equal ^sub1 ^sub2``;
val _ = print_eval "abs_negone" ``fp64_abs ^negone``;
val _ = print_eval "abs_nz" ``fp64_abs ^nz``;
val _ = print_eval "abs_nqnan" ``fp64_abs ^nqnan``;
val _ = print_eval "abs_ninf" ``fp64_abs ^ninf``;
val _ = print_eval "neg_one" ``fp64_negate ^one``;
val _ = print_eval "neg_pz" ``fp64_negate ^pz``;
val _ = print_eval "neg_qnan" ``fp64_negate ^qnan``;
val _ = print_eval "neg_sub1" ``fp64_negate ^sub1``;
