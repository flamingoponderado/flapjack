(* Typed source statements for closure free-variable removal. *)
load "clos_fvsProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_sing_typed=" clos_fvsTheory.remove_fvs_sing_def;
val _ = show "remove_sing_eq_typed=" clos_fvsTheory.remove_fvs_sing_eq;
val _ = show "remove_length_typed=" clos_fvsTheory.LENGTH_remove_fvs;
val _ = show "compile_typed=" clos_fvsTheory.compile_def;
val _ = show "compile_inc_typed=" clos_fvsTheory.compile_inc_def;
val _ = show "value_rel_typed=" clos_fvsProofTheory.v_rel_rules;
val _ = show "state_rel_typed=" clos_fvsProofTheory.state_rel_def;
val _ = show "evaluate_remove_typed=" clos_fvsProofTheory.evaluate_remove_fvs;
val _ = show "semantics_compile_typed=" clos_fvsProofTheory.semantics_compile;
