load "preamble"; load "clos_interpProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "every_Fn_vs_NONE_insert_interp_typed=" clos_interpProofTheory.every_Fn_vs_NONE_insert_interp;
val _ = show_thm "contains_App_SOME_insert_interp_typed=" clos_interpProofTheory.contains_App_SOME_insert_interp;
