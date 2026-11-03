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
val _ = show "merge_typed=" clos_knownTheory.merge_def;
val _ = show "known_op_typed=" clos_knownTheory.known_op_def;
val _ = show "get_size_aux_typed=" clos_knownTheory.get_size_aux_def;
val _ = show "get_size_typed=" clos_knownTheory.get_size_def;
val _ = show "get_size_sc_aux_typed=" clos_knownTheory.get_size_sc_aux_def;
val _ = show "get_size_sc_typed=" clos_knownTheory.get_size_sc_def;
val _ = show "clos_approx_typed=" clos_knownTheory.clos_approx_def;
val _ = show "clos_gen_noinline_typed=" clos_knownTheory.clos_gen_noinline_def;
val _ = show "mk_ticks_typed=" clos_knownTheory.mk_Ticks_def;
val _ = show "get_size_sc_aux_correct_typed=" clos_knownTheory.get_size_sc_aux_correct;
val _ = show "get_size_sc_some_typed=" clos_knownTheory.get_size_sc_SOME;
val _ = show "free_typed=" clos_knownTheory.free_def;
val _ = show "closed_typed=" clos_knownTheory.closed_def;
val _ = show "decide_inline_typed=" clos_knownTheory.decide_inline_def;
val _ = show "decide_inline_positive_typed=" clos_knownTheory.decide_inline_LetInline;
val _ = show "fv_max_def_typed=" clos_knownProofTheory.fv_max_def;
val _ = show "fv_max_smart_typed=" clos_knownProofTheory.fv_max_SmartOp;
val _ = show "fv_max_cons_typed=" clos_knownProofTheory.fv_max_cons;
val _ = show "fv_max_append_typed=" clos_knownProofTheory.fv_max_append;
val _ = show "fv_max_less_typed=" clos_knownProofTheory.fv_max_less;
val _ = show "fv_max_rw_typed=" clos_knownProofTheory.fv_max_rw;
val _ = show "fv_max_ticks_typed=" clos_knownProofTheory.fv_max_mk_Ticks;
