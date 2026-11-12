(* Typed statements for the BVL inlining proof's code-label results. *)
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
