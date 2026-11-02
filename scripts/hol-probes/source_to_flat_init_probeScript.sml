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
val _ = show_thm "precondition1=" source_to_flatProofTheory.precondition1_def;
val _ = show_thm "precondition1_change_clock=" source_to_flatProofTheory.precondition1_change_clock;
val _ = show_thm "precondition=" source_to_flatProofTheory.precondition_def;
val _ = show_thm "source_compile_semantics=" source_to_flatProofTheory.compile_semantics;
val _ = show_thm "source_compile_prog=" source_to_flatTheory.compile_prog_def;
val _ = show_thm "source_glob_alloc=" source_to_flatTheory.glob_alloc_def;
val _ = show_thm "source_alloc_env_ref=" source_to_flatTheory.alloc_env_ref_def;
val _ = show_thm "source_lookup_env_id=" source_to_flatTheory.lookup_env_id_def;
val _ = show_thm "source_store_env_id=" source_to_flatTheory.store_env_id_def;
val _ = show_thm "source_inc_compile_prog=" source_to_flatTheory.inc_compile_prog_def;
val _ = show_thm "spt_from_list=" sptreeTheory.fromList_def;
val _ = show_thm "initial_env_ok=" source_to_flatProofTheory.init_genv_ok;
val _ = show_thm "initial_types_ok=" source_to_flatProofTheory.init_genv_tys_ok;
val _ = show_thm "keep_global_allocation=" source_to_flatProofTheory.keep_glob_alloc;
val _ = show_thm "elimination_keep=" flat_elimTheory.keep_def;
val _ = show_thm "incremental_nonempty=" source_to_flatProofTheory.inc_compile_prog_nonempty;
val _ = show_thm "flat_initial_state=" flatSemTheory.initial_state_def;
val _ = show_thm "flat_semantics=" flatSemTheory.semantics_def;
val _ = show_thm "compile_flat=" source_to_flatTheory.compile_flat_def;
val _ = show_thm "compile=" source_to_flatTheory.compile_def;
val _ = show_thm "incremental_compile=" source_to_flatTheory.inc_compile_def;
val _ = show_eval "evaluated_entries=" ``source_to_flatProof$init_genv_els``;
val _ = show_eval "evaluated_next=" ``source_to_flatProof$init_genv_next``;
val _ = show_eval "program_nonzero_next=" ``
  let c = source_to_flat$empty_config with
    next := (source_to_flat$empty_config.next with vidx := 4n) in
  let (c', code) = source_to_flat$compile_prog c [] in
    (c'.next.vidx, c'.envs.next, code)``;
val _ = show_eval "incremental_nonzero_next=" ``
  let c = source_to_flat$empty_config with
    next := (source_to_flat$empty_config.next with vidx := 4n) in
  let (c', code) = source_to_flat$inc_compile_prog (3n, 7n) c [] in
    (c'.next.vidx, c'.envs.next, code)``;
val _ = show_eval "incremental_empty=" ``SND (source_to_flat$inc_compile (0n,0n) source_to_flat$empty_config [])``;
