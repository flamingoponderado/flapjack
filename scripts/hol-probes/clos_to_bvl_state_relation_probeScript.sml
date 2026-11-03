(* Typed source statements for the closure-to-BVL state relation. *)
load "clos_to_bvlProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "state_rel_typed=" clos_to_bvlProofTheory.state_rel_def;
val _ = show "state_rel_clock_typed=" clos_to_bvlProofTheory.state_rel_clock;
val _ = show "state_rel_refs_lookup_typed=" clos_to_bvlProofTheory.state_rel_refs_lookup;
val _ = show "cl_rel_rules_typed=" clos_to_bvlProofTheory.cl_rel_rules;
val _ = show "v_rel_rules_typed=" clos_to_bvlProofTheory.v_rel_rules;
val _ = show "env_rel_typed=" clos_to_bvlProofTheory.env_rel_def;
val _ = show "add_args_typed=" clos_to_bvlProofTheory.add_args_def;
val _ = show "get_num_args_typed=" clos_to_bvlProofTheory.get_num_args_def;
val _ = show "code_installed_typed=" clos_to_bvlProofTheory.code_installed_def;
val _ = show "closure_code_installed_typed=" clos_to_bvlProofTheory.closure_code_installed_def;
val _ = show "code_installed_subspt_typed=" clos_to_bvlProofTheory.code_installed_subspt;
val _ = show "init_code_rel_typed=" clos_to_bvlProofTheory.init_code_def;
val _ = show "compile_prog_semantics_typed=" clos_to_bvlProofTheory.compile_prog_semantics;
val _ = show "compile_exps_correct_typed=" clos_to_bvlProofTheory.compile_exps_correct;
