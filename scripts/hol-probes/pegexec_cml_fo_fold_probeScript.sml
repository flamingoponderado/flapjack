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
