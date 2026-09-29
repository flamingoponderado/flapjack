(*
  Direct HOL-EVAL fixture for the binary64 rounding constants rendered in
  Flapjack/Misc/BinaryIeeeRound.lean (HOL/src/floating-point/
  binary_ieeeScript.sml:355-365): largest and threshold at (:52 # 11), and the
  value of float_top, which largest must equal.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val _ = print_eval "largest_fp64" ``largest (:52 # 11)``;
val _ = print_eval "threshold_fp64" ``threshold (:52 # 11)``;
val _ = print_eval "top_is_largest"
  ``float_to_real (float_top (:52 # 11)) = largest (:52 # 11)``;
