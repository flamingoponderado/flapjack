load "flat_patternProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "operator_global_flag=" flat_patternProofTheory.op_sets_globals_gbag;
val _ = show_thm "expression_global_flag=" flat_patternProofTheory.compile_exp_set_globals_FST_SND;
val _ = show_thm "tuple_global_flag=" flat_patternProofTheory.compile_exp_set_globals_tup;
val _ = show_thm "global_bag_list_empty=" flatPropsTheory.elist_globals_eq_empty;
val _ = show_thm "sum_string_ords=" flat_patternProofTheory.sum_string_ords_eq;
val _ = show_thm "generated_name_aux=" flat_patternProofTheory.dec_enc_aux;
val _ = show_thm "generated_name_roundtrip=" flat_patternProofTheory.dec_enc;
val _ = show_thm "generated_name_injective=" flat_patternProofTheory.enc_num_to_name_inj;
