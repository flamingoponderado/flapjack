(* Typed statements of the HOL `machine_ieee` definitions ported in
   `Flapjack/Misc/MachineIeee*.lean`, from the built HOL4 core theory (no rebuild). *)
load "machine_ieeeTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "float_to_fp64_def_typed=" machine_ieeeTheory.float_to_fp64_def;
val _ = show_thm "fp64_abs_def_typed=" machine_ieeeTheory.fp64_abs_def;
val _ = show_thm "fp64_equal_def_typed=" machine_ieeeTheory.fp64_equal_def;
val _ = show_thm "fp64_greaterEqual_def_typed=" machine_ieeeTheory.fp64_greaterEqual_def;
val _ = show_thm "fp64_greaterThan_def_typed=" machine_ieeeTheory.fp64_greaterThan_def;
val _ = show_thm "fp64_isNan_def_typed=" machine_ieeeTheory.fp64_isNan_def;
val _ = show_thm "fp64_isSignallingNan_def_typed=" machine_ieeeTheory.fp64_isSignallingNan_def;
val _ = show_thm "fp64_lessEqual_def_typed=" machine_ieeeTheory.fp64_lessEqual_def;
val _ = show_thm "fp64_lessThan_def_typed=" machine_ieeeTheory.fp64_lessThan_def;
val _ = show_thm "fp64_negate_def_typed=" machine_ieeeTheory.fp64_negate_def;
val _ = show_thm "fp64_to_float_def_typed=" machine_ieeeTheory.fp64_to_float_def;
val _ = show_thm "fp64_add_def_typed=" machine_ieeeTheory.fp64_add_def;
val _ = show_thm "fp64_div_def_typed=" machine_ieeeTheory.fp64_div_def;
val _ = show_thm "fp64_mul_def_typed=" machine_ieeeTheory.fp64_mul_def;
val _ = show_thm "fp64_mul_add_def_typed=" machine_ieeeTheory.fp64_mul_add_def;
val _ = show_thm "fp64_sub_def_typed=" machine_ieeeTheory.fp64_sub_def;
val _ = show_thm "float_to_fp32_def_typed=" machine_ieeeTheory.float_to_fp32_def;
val _ = show_thm "fp32_to_float_def_typed=" machine_ieeeTheory.fp32_to_float_def;
val _ = show_thm "fp32_to_fp64_def_typed=" machine_ieeeTheory.fp32_to_fp64_def;
val _ = show_thm "fp32_to_fp64_with_flags_def_typed=" machine_ieeeTheory.fp32_to_fp64_with_flags_def;
val _ = show_thm "fp64_to_fp32_def_typed=" machine_ieeeTheory.fp64_to_fp32_def;
val _ = show_thm "fp64_to_fp32_with_flags_def_typed=" machine_ieeeTheory.fp64_to_fp32_with_flags_def;
val _ = show_thm "fp64_to_int_def_typed=" machine_ieeeTheory.fp64_to_int_def;
val _ = show_thm "int_to_fp64_def_typed=" machine_ieeeTheory.int_to_fp64_def;
val _ = show_thm "convert_def_typed=" machine_ieeeTheory.convert_def;
val _ = show_thm "real_to_fp32_with_flags_def_typed=" machine_ieeeTheory.real_to_fp32_with_flags_def;
val _ = show_thm "real_to_fp64_def_typed=" machine_ieeeTheory.real_to_fp64_def;
val _ = show_thm "real_to_fp64_with_flags_def_typed=" machine_ieeeTheory.real_to_fp64_with_flags_def;
val _ = show_thm "fp64_sqrt_def_typed=" machine_ieeeTheory.fp64_sqrt_def;
