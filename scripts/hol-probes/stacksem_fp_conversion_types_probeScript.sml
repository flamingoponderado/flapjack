(* Original full carrier types for the three StackSem inst_def FP conversion cases. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
load "machine_ieeeTheory";
open bossLib HolKernel Parse stackSemTheory machine_ieeeTheory;
fun typ label t = (print (label ^ "="); print_type (type_of t); print "\n");
val _ = typ "fp_inst_type" ``stackSem$inst``;
val _ = typ "fp_get_type" ``stackSem$get_fp_var``;
val _ = typ "fp_set_type" ``stackSem$set_fp_var``;
val _ = typ "fp_sqrt_type" ``machine_ieee$fp64_sqrt``;
val _ = typ "fp_to_int_type" ``machine_ieee$fp64_to_int``;
val _ = typ "fp_from_int_type" ``machine_ieee$int_to_fp64``;
val _ = typ "fp_oracle_type" ``(s:('a,'c,'ffi) stackSem$state).compile_oracle``;
