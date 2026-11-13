(* Typed original source equations and label-preservation theorem. *)
load "bvi_inlineTheory";
load "bvi_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_ticks_exp_def_typed" bvi_inlineTheory.remove_ticks_exp_def;
val _ = show "remove_ticks_get_code_labels_typed" bvi_inlineProofTheory.remove_ticks_get_code_labels;
val _ = show "remove_ticks_prog_code_labels_typed" bvi_inlineProofTheory.remove_ticks_prog_code_labels;
val _ = show "MAP_FST_remove_ticks_prog_typed" bvi_inlineProofTheory.MAP_FST_remove_ticks_prog;
val _ = show "inline_all_def_typed" bvi_inlineTheory.inline_all_def;
val _ = show "compile_inc_def_typed" bvi_inlineTheory.compile_inc_def;
val _ = show "compile_inc_code_labels_typed" bvi_inlineProofTheory.compile_inc_code_labels;
val _ = show "inline_all_MAP_FST_typed" bvi_inlineProofTheory.inline_all_MAP_FST;
val _ = show "compile_inc_MAP_FST_typed" bvi_inlineProofTheory.compile_inc_MAP_FST;
val _ = show "inline_exp_def_typed" bvi_inlineTheory.inline_exp_def;
val _ = show "cache_code_labels_def_typed" bvi_inlineProofTheory.cache_code_labels_def;
val _ = show "lookup_cache_code_labels_typed" bvi_inlineProofTheory.lookup_cache_code_labels;
val _ = show "cache_code_labels_insert_typed" bvi_inlineProofTheory.cache_code_labels_insert;
val _ = show "bvi_mk_tick_get_code_labels_typed" bvi_inlineProofTheory.bvi_mk_tick_get_code_labels;
val _ = show "inline_exp_code_labels_typed" bvi_inlineProofTheory.inline_exp_code_labels;
val _ = show "compile_prog_def_typed" bvi_inlineTheory.compile_prog_def;
val _ = show "inline_all_code_labels_typed" bvi_inlineProofTheory.inline_all_code_labels;
val _ = show "compile_prog_code_labels_typed" bvi_inlineProofTheory.compile_prog_code_labels;
