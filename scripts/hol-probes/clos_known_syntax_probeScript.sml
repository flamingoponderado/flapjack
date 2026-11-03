(* Typed source precondition for closure known-function optimization. *)
load "clos_knownProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "syntax_ok_typed=" clos_knownProofTheory.syntax_ok_def;
val _ = show "bag_all_distinct_typed=" bagTheory.BAG_ALL_DISTINCT;
val _ = show "option_val_approx_spt_typed=" clos_knownTheory.option_val_approx_spt_def;
val _ = show "option_upd_val_spt_typed=" clos_knownTheory.option_upd_val_spt_def;
val _ = show "contains_closures_typed=" clos_knownTheory.contains_closures_def;
val _ = show "get_size_aux_typed=" clos_knownTheory.get_size_aux_def;
val _ = show "get_size_typed=" clos_knownTheory.get_size_def;
val _ = show "get_size_sc_aux_correct_typed=" clos_knownTheory.get_size_sc_aux_correct;
val _ = show "get_size_sc_some_typed=" clos_knownTheory.get_size_sc_SOME;
