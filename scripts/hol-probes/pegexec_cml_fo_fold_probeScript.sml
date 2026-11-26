(* Typed captures of the first-order PEG fold and constructor-application helpers. *)
load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "foldl_Eapp_aux_def_typed" pegexec_cml_foTheory.foldl_Eapp_aux_def;
val _ = show "foldl_DType_aux_def_typed" pegexec_cml_foTheory.foldl_DType_aux_def;
val _ = show "foldl_Eapp_fo_def_typed" pegexec_cml_foTheory.foldl_Eapp_fo_def;
val _ = show "foldl_DType_fo_def_typed" pegexec_cml_foTheory.foldl_DType_fo_def;
val _ = show "ptPapply0_fo_def_typed" pegexec_cml_foTheory.ptPapply0_fo_def;
val _ = show "ptPapply_fo_def_typed" pegexec_cml_foTheory.ptPapply_fo_def;

(* Task 273: list/option helpers and the location projection. *)
val _ = show "eval_fold_def_typed" pegexec_cml_foTheory.eval_fold_def;
val _ = show "in_set_def_typed" pegexec_cml_foTheory.in_set_def;
val _ = show "eval_combine_def_typed" pegexec_cml_foTheory.eval_combine_def;
val _ = show "merge_err_option_def_typed" pegexec_cml_foTheory.merge_err_option_def;
val _ = show "map_ptree_loc_def_typed" pegexec_cml_foTheory.map_ptree_loc_def;
val _ = show "map_ptree_loc_thm_typed" pegexec_cml_foTheory.map_ptree_loc_thm;

(* Task 273: the optional-tree-list pop and the non-alternative longid check. *)
val _ = show "poplist_aux_def_typed" pegexec_cml_foTheory.poplist_aux_def;
val _ = show "poplistval_def_typed" pegexec_cml_foTheory.poplistval_def;
val _ = show "eval_token_longid_check_def_typed" pegexec_cml_foTheory.eval_token_longid_check_def;
