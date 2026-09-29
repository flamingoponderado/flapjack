(*
  Direct HOL-EVAL fixture for the source-syntax comparison table `fp_cmp`
  (`cakeml/semantics/fpSemScript.sml:24-31`), whose argument is the `ast$opb`
  type (`Lt | Gt | Leq | Geq`).  It keys the rendered machine_ieee `fp64_*`
  predicates exactly as the tagged Lean `fpSemFpCmp` does (bead
  flapjack-h29l.6.2.7).  binary_ieeeLib extends EVAL with the IEEE conversions.
*)
load "fpSemTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib fpSemTheory astTheory machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [fp_cmp_def, fp64_to_float_def, float_to_fp64_def,
  fp64_lessThan_def, fp64_lessEqual_def, fp64_greaterThan_def, fp64_greaterEqual_def];

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
val pinf = ``0x7FF0000000000000w : word64``;
val qnan = ``0x7FF8000000000000w : word64``;

val _ = print_eval "fp_cmp_lt_one_two" ``fp_cmp Lt ^one ^two``;
val _ = print_eval "fp_cmp_leq_two_one" ``fp_cmp Leq ^two ^one``;
val _ = print_eval "fp_cmp_gt_two_one" ``fp_cmp Gt ^two ^one``;
val _ = print_eval "fp_cmp_geq_one_one" ``fp_cmp Geq ^one ^one``;
val _ = print_eval "fp_cmp_lt_qnan_one" ``fp_cmp Lt ^qnan ^one``;
val _ = print_eval "fp_cmp_gt_pinf_one" ``fp_cmp Gt ^pinf ^one``;
