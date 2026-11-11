(* Typed source declarations for the value projection lemmas in
   cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml. *)
load "preamble";
load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_to_dataProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "data_to_bvi_v_def_typed" bvi_to_dataProofTheory.data_to_bvi_v_def;
val _ = show "data_to_bvi_v_Unit_typed" bvi_to_dataProofTheory.data_to_bvi_v_Unit;
val _ = show "data_to_bvi_v_Boolv_typed" bvi_to_dataProofTheory.data_to_bvi_v_Boolv;
val _ = show "data_to_bvi_ref_def_typed" bvi_to_dataProofTheory.data_to_bvi_ref_def;
val _ = show "v_to_bytes_eq_typed" bvi_to_dataProofTheory.v_to_bytes_eq;
val _ = show "v_to_words_eq_typed" bvi_to_dataProofTheory.v_to_words_eq;
val _ = show "data_to_bvi_v_list_to_v_Nil_typed" bvi_to_dataProofTheory.data_to_bvi_v_list_to_v_Nil;
