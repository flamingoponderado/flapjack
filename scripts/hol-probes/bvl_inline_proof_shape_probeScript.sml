(* Typed statements for the BVL inlining proof's code-label and name-preservation results. *)
load "bvl_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "var_list_code_labels_imp_typed" bvl_inlineProofTheory.var_list_code_labels_imp;
val _ = show "let_op_code_labels_typed" bvl_inlineProofTheory.let_op_code_labels;
val _ = show "let_op_sing_code_labels_typed" bvl_inlineProofTheory.let_op_sing_code_labels;
val _ = show "remove_ticks_code_labels_typed" bvl_inlineProofTheory.remove_ticks_code_labels;
val _ = show "optimise_get_code_labels_typed" bvl_inlineProofTheory.optimise_get_code_labels;
val _ = show "tick_inline_code_labels_typed" bvl_inlineProofTheory.tick_inline_code_labels;
val _ = show "tick_inline_all_code_labels_typed" bvl_inlineProofTheory.tick_inline_all_code_labels;
val _ = show "compile_prog_get_code_labels_typed" bvl_inlineProofTheory.compile_prog_get_code_labels;
val _ = show "MAP_FST_MAP_optimise_typed" bvl_inlineProofTheory.MAP_FST_MAP_optimise;
val _ = show "compile_prog_names_typed" bvl_inlineProofTheory.compile_prog_names;
val _ = show "handle_ok_optimise_typed" bvl_inlineProofTheory.handle_ok_optimise;
val _ = show "compile_prog_handle_ok_typed" bvl_inlineProofTheory.compile_prog_handle_ok;
val _ = show "map_fromAList_typed" bvl_inlineProofTheory.map_fromAList;
val _ = show "state_cc_compile_inc_eq_typed" bvl_inlineProofTheory.state_cc_compile_inc_eq;
val _ = show "state_co_compile_inc_eq_typed" bvl_inlineProofTheory.state_co_compile_inc_eq;
val _ = show "compile_prog_semantics_typed" bvl_inlineProofTheory.compile_prog_semantics;
val _ = show "let_op_cc_def_typed" bvl_inlineProofTheory.let_op_cc_def;
val _ = show "let_opt_def_typed" bvl_inlineProofTheory.let_opt_def;
val _ = show "let_opt_remove_def_typed" bvl_inlineProofTheory.let_opt_remove_def;
