(* Typed identifier-set definitions used by compilerProof$type_config_ok. *)
load "inferPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "set_tids_def_typed" inferPropsTheory.set_tids_def;
val _ = show "unconvert_t_def_typed" inferPropsTheory.unconvert_t_def;
val _ = show "inf_set_tids_def_typed" inferPropsTheory.inf_set_tids_def;
val _ = show "inf_set_tids_subset_def_typed" inferPropsTheory.inf_set_tids_subset_def;
val _ = show "inf_set_tids_ienv_def_typed" inferPropsTheory.inf_set_tids_ienv_def;
val _ = show "inf_set_tids_unconvert_typed" inferPropsTheory.inf_set_tids_unconvert;
val _ = show "check_t_def_typed" inferTheory.check_t_def;
val _ = show "ienv_val_ok_def_typed" inferTheory.ienv_val_ok_def;
val _ = show "ienv_ok_def_typed" inferPropsTheory.ienv_ok_def;
val _ = show "infer_deBruijn_subst_id_typed" inferPropsTheory.infer_deBruijn_subst_id;
val _ = show "infer_deBruijn_subst_id2_typed" inferPropsTheory.infer_deBruijn_subst_id2;
val _ = show "check_t_infer_deBruijn_subst_typed" inferPropsTheory.check_t_infer_deBruijn_subst;
val _ = show "infer_deBruijn_subst_uncheck_typed" inferPropsTheory.infer_deBruijn_subst_uncheck;
val _ = show "check_t_more5_typed" inferPropsTheory.check_t_more5;
val _ = show "check_t_t_vars_typed" inferPropsTheory.check_t_t_vars;

(* Task 273: initial-state and empty-substitution facts. *)
val _ = show "hide_def_typed" inferPropsTheory.hide_def;
val _ = show "init_infer_state_next_uvar_typed" inferPropsTheory.init_infer_state_next_uvar;
val _ = show "init_infer_state_subst_typed" inferPropsTheory.init_infer_state_subst;
val _ = show "t_wfs_FEMPTY_typed" inferPropsTheory.t_wfs_FEMPTY;
val _ = show "t_wfs_init_infer_state_typed" inferPropsTheory.t_wfs_init_infer_state;

(* Task 273: pair/UNCURRY and namespace fold facts. *)
fun showWithHyps label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

val _ = show "remove_pair_lem_typed" inferPropsTheory.remove_pair_lem;
val _ = show "UNCURRY_rator_typed" inferPropsTheory.UNCURRY_rator;
val _ = show "nsMap_FOLDL_nsAppend_typed" inferPropsTheory.nsMap_FOLDL_nsAppend;
val _ = showWithHyps "nsAll_FOLDL_nsAppend_typed" inferPropsTheory.nsAll_FOLDL_nsAppend;
