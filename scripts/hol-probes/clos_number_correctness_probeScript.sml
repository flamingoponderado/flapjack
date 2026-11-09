(* Typed source statements for closure numbering correctness. *)
load "clos_numberProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "renumber_def_typed=" clos_numberTheory.renumber_code_locs_def;
val _ = show "compile_inc_def_typed=" clos_numberTheory.compile_inc_def;
val _ = show "make_even_def_typed=" miscTheory.make_even_def;
val _ = show "ignore_table_def_typed=" clos_numberTheory.ignore_table_def;
val _ = show "v_rel_rules_typed=" clos_numberProofTheory.v_rel_rules;
val _ = show "ref_rel_def_typed=" closPropsTheory.ref_rel_def;
val _ = show "fmap_rel_def_typed=" finite_mapTheory.fmap_rel_def;
val _ = show "state_rel_typed=" clos_numberProofTheory.state_rel_def;
val _ = show "renumber_correct_typed=" clos_numberProofTheory.renumber_code_locs_correct;
val _ = show "renumber_code_locs_inc_typed=" clos_numberProofTheory.renumber_code_locs_inc;
val _ = show "renumber_code_locs_imp_inc_typed=" clos_numberProofTheory.renumber_code_locs_imp_inc;
val _ = show "renumber_code_locs_every_Fn_SOME_typed=" clos_numberProofTheory.renumber_code_locs_every_Fn_SOME;
val _ = show "semantics_number_typed=" clos_numberProofTheory.semantics_number;
