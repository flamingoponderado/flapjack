load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "eval_state_ok=" source_to_flatProofTheory.init_eval_state_ok_def;
val _ = show_thm "type_entries=" source_to_flatProofTheory.init_genv_ty_els_def;
val _ = show_thm "constructor_entries=" source_to_flatProofTheory.init_genv_els_def;
val _ = show_thm "initial_env=" source_to_flatProofTheory.init_genv_def;
val _ = show_thm "initial_next=" source_to_flatProofTheory.init_genv_next;
val _ = show_thm "initial_global_inv=" source_to_flatProofTheory.init_global_env_inv_def;
val _ = show_thm "initial_global_imp=" source_to_flatProofTheory.init_global_env_inv_imp;
val _ = show_thm "initial_env_ok=" source_to_flatProofTheory.init_genv_ok;
val _ = show_thm "initial_types_ok=" source_to_flatProofTheory.init_genv_tys_ok;
val _ = show_thm "flat_initial_state=" flatSemTheory.initial_state_def;
val _ = show_thm "flat_semantics=" flatSemTheory.semantics_def;
val _ = show_thm "compile_flat=" source_to_flatTheory.compile_flat_def;
val _ = show_thm "compile=" source_to_flatTheory.compile_def;
val _ = show_thm "incremental_compile=" source_to_flatTheory.inc_compile_def;
val _ = show_eval "evaluated_entries=" ``source_to_flatProof$init_genv_els``;
val _ = show_eval "evaluated_next=" ``source_to_flatProof$init_genv_next``;
val _ = show_eval "incremental_empty=" ``SND (source_to_flat$inc_compile (0n,0n) source_to_flat$empty_config [])``;
