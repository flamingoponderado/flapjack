(* Typed source statements for closure annotation correctness. *)
load "clos_annotateProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "const_zero_typed=" clos_annotateTheory.const_0_def;
val _ = show "no_overlap_typed=" clos_annotateTheory.no_overlap_def;
val _ = show "alt_free_sing_typed=" clos_annotateTheory.alt_free_sing_def;
val _ = show "get_var_typed=" clos_annotateTheory.get_var_def;
val _ = show "shifted_env_typed=" clos_annotateTheory.shifted_env_def;
val _ = show "shift_sing_typed=" clos_annotateTheory.shift_sing_def;
val _ = show "annotate_sing_typed=" clos_annotateTheory.annotate_sing_def;
val _ = show "annotate_list_typed=" clos_annotateTheory.annotate_list_def;
val _ = show "annotate_sing_eq_typed=" clos_annotateTheory.annotate_sing_eq;
val _ = show "compile_def_typed=" clos_annotateTheory.compile_def;
val _ = show "compile_eq_typed=" clos_annotateTheory.compile_eq;
val _ = show "compile_inc_def_typed=" clos_annotateTheory.compile_inc_def;
val _ = show "compile_inc_eq_typed=" clos_annotateTheory.compile_inc_eq;
val _ = show "MAP_FST_compile_typed=" clos_annotateProofTheory.MAP_FST_compile;
val _ = show "semantics_annotate_typed=" clos_annotateProofTheory.semantics_annotate;
