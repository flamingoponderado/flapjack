load "flatSemTheory"; load "flatPropsTheory"; load "preamble";
open preamble flatSemTheory;
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "do_app_const_typed=" flatSemTheory.do_app_const;
val _ = show_thm "do_app_state_unchanged_typed=" flatPropsTheory.do_app_state_unchanged;
val _ = show_thm "pmatch_state_typed=" flatPropsTheory.pmatch_state;
val _ = show_thm "pmatch_ignore_clock_typed=" flatPropsTheory.pmatch_ignore_clock;
val _ = show_thm "pmatch_rows_ignore_clock_typed=" flatPropsTheory.pmatch_rows_ignore_clock;
val _ = show_thm "pmatch_extend_typed=" flatPropsTheory.pmatch_extend;
val _ = show_thm "map_match_def_typed=" semanticPrimitivesPropsTheory.map_match_def;
val _ = show_thm "semantic_shift_lookup_def_typed=" semanticPrimitivesPropsTheory.shift_lookup_def;
val _ = show_thm "semantic_do_shift_def_typed=" semanticPrimitivesPropsTheory.do_shift_def;
val _ = show_thm "pmatch_append_typed=" flatPropsTheory.pmatch_append;
val _ = show_thm "pmatch_any_match_typed=" flatPropsTheory.pmatch_any_match;
val _ = show_thm "pmatch_any_no_match_typed=" flatPropsTheory.pmatch_any_no_match;
val _ = show_thm "pmatch_any_match_error_typed=" flatPropsTheory.pmatch_any_match_error;
val _ = show_thm "pmatch_list_pairwise_typed=" flatPropsTheory.pmatch_list_pairwise;
val _ = show_thm "pmatch_list_snoc_nil_typed=" flatPropsTheory.pmatch_list_snoc_nil;
val _ = show_thm "pmatch_list_append_typed=" flatPropsTheory.pmatch_list_append;
val _ = show_thm "pmatch_list_snoc_typed=" flatPropsTheory.pmatch_list_snoc;
val _ = show_thm "map_match_eq_case_typed=" flatPropsTheory.map_match_eq_case;
val _ = show_thm "pmatch_nil_typed=" flatPropsTheory.pmatch_nil;
val _ = show_thm "flat_build_rec_env_merge_typed=" flatPropsTheory.build_rec_env_merge;
val _ = show_thm "flat_evaluate_cons_typed=" flatPropsTheory.evaluate_cons;
val _ = show_thm "flat_evaluate_append_typed=" flatPropsTheory.evaluate_append;

val flat_build_rec_env_help = prove (
  ``∀funs env funs'.
      FOLDR (λ(f,x,e) env'. (f, flatSem$Recclosure env funs' f)::env') env' funs =
      MAP (λ(fn,n,e). (fn, flatSem$Recclosure env funs' fn)) funs ++ env'``,
  Induct >> srw_tac[][] >> PairCases_on `h` >> srw_tac[][]);
val _ = show_thm "flat_build_rec_env_help_typed=" flat_build_rec_env_help;

val flat_do_app_add_clock = prove (
  ``flatSem$do_app (s : ('a,'ffi) flatSem$state) op es = SOME (t,r) ⇒
     flatSem$do_app (s with clock := s.clock + k) op es = SOME (t with clock := t.clock + k,r)``,
  rw [Once flatSemTheory.do_app_def, AllCaseEqs(), semanticPrimitivesTheory.store_alloc_def] >> gvs []
  >> simp [flatSemTheory.do_app_def, semanticPrimitivesTheory.store_alloc_def]);
val _ = show_thm "flat_do_app_add_clock_typed=" flat_do_app_add_clock;
val flat_do_app_add_clock_none = prove (
  ``flatSem$do_app (s : ('a,'ffi) flatSem$state) op es = NONE ⇒
     flatSem$do_app (s with clock := s.clock + k) op es = NONE``,
  strip_tac >> Cases_on `op` >> TRY (Cases_on `o'`)
  >> gvs [flatSemTheory.do_app_def,AllCaseEqs(),semanticPrimitivesTheory.store_alloc_def]
  >> rw [] >> gvs []
  >> fs [IS_SOME_EXISTS,CaseEq"option",CaseEq"store_v"]);
val _ = show_thm "flat_do_app_add_clock_none_typed=" flat_do_app_add_clock_none;

val _ = show_thm "flat_with_clock_ffi_typed=" flatPropsTheory.with_clock_ffi;
val _ = show_thm "flat_evaluate_sing_typed=" flatPropsTheory.evaluate_sing;
val _ = show_thm "flat_evaluate_add_clock_typed=" flatPropsTheory.evaluate_add_to_clock;
val _ = show_thm "flat_evaluate_decs_add_clock_typed=" flatPropsTheory.evaluate_decs_add_to_clock;
val _ = show_thm "flat_do_app_io_events_mono_typed=" flatPropsTheory.do_app_io_events_mono;
val _ = show_thm "flat_evaluate_io_events_mono_typed=" flatPropsTheory.evaluate_io_events_mono;
val _ = show_thm "flat_evaluate_io_events_mono_imp_typed=" flatPropsTheory.evaluate_io_events_mono_IMP;
val _ = show_thm "flat_evaluate_dec_io_events_mono_typed=" flatPropsTheory.evaluate_dec_io_events_mono;
val _ = show_thm "flat_evaluate_decs_io_events_mono_typed=" flatPropsTheory.evaluate_decs_io_events_mono;

val _ = show_thm "flat_evaluate_add_clock_io_events_mono_typed=" flatPropsTheory.evaluate_add_to_clock_io_events_mono;
val _ = show_thm "flat_evaluate_dec_add_clock_io_events_mono_typed=" flatPropsTheory.evaluate_dec_add_to_clock_io_events_mono;
val _ = show_thm "flat_evaluate_decs_add_clock_io_events_mono_typed=" flatPropsTheory.evaluate_decs_add_to_clock_io_events_mono;

val _ = show_thm "flat_evaluate_map_var_local_typed=" flatPropsTheory.evaluate_MAP_Var_local;
val _ = show_thm "flat_bind_locals_list_def_typed=" flatPropsTheory.bind_locals_list_def;
val _ = show_thm "flat_evaluate_vars_typed=" flatPropsTheory.evaluate_vars;

val _ = show_thm "flat_pmatch_list_map_pvar_typed=" flatPropsTheory.pmatch_list_MAP_Pvar;

val flat_evaluate_decs_add_clock_initial = prove (
  ``r ≠ SOME (Rabort Rtimeout_error) ∧
    evaluate_decs (initial_state ffi k ec) decs = (s',r) ⇒
    evaluate_decs (initial_state ffi (ck + k) ec) decs =
      (s' with clock := s'.clock + ck,r)``,
  rw [initial_state_def] >> imp_res_tac flatPropsTheory.evaluate_decs_add_to_clock >> fs []);
val _ = show_thm "flat_evaluate_decs_add_clock_initial_typed=" flat_evaluate_decs_add_clock_initial;

val flat_evaluate_decs_add_clock_initial_events = prove (
  ``evaluate_decs (initial_state ffi k ec) prog = (s',r) ==>
    s'.ffi.io_events ≼
    (FST (evaluate_decs (initial_state ffi (k+ck) ec) prog)).ffi.io_events``,
  rw [initial_state_def]
  >> qmatch_assum_abbrev_tac `evaluate_decs s1 _ = _`
  >> qispl_then [`prog`,`s1`,`ck`] mp_tac flatPropsTheory.evaluate_decs_add_to_clock_io_events_mono
  >> fs [Abbr`s1`]);
val _ = show_thm "flat_evaluate_decs_add_clock_initial_events_typed=" flat_evaluate_decs_add_clock_initial_events;

val flat_initial_state_with_clock = prove (
  ``(initial_state ffi k ec with clock := (initial_state ffi k ec).clock + ck) =
    initial_state ffi (k + ck) ec``,
  rw [initial_state_def]);
val _ = show_thm "flat_initial_state_with_clock_typed=" flat_initial_state_with_clock;

val _ = show_thm "flat_imp_semantics_eq_typed=" flatPropsTheory.IMP_semantics_eq;

val _ = show_thm "flat_elist_globals_foldr_typed=" flatPropsTheory.elist_globals_FOLDR;
val _ = show_thm "flat_elist_globals_reverse_typed=" flatPropsTheory.elist_globals_REVERSE;
val _ = show_thm "flat_initial_state_clock_typed=" flatPropsTheory.initial_state_clock;

val _ = show_thm "flat_evaluate_decs_add_clock_io_events_mono_alt_typed=" flatPropsTheory.evaluate_decs_add_to_clock_io_events_mono_alt;

val _ = show_thm "flat_isClosure_simps_typed=" flatPropsTheory.isClosure_simps;

val flat_check_type_list_rel_same = prove (
  ``LIST_REL vr vs1 vs2 ∧
    EVERY (semanticPrimitives$check_type ty) (MAP flatSem$flat_to_v vs1) ∧
    flatProps$simple_val_rel vr ⇒ vs2 = vs1``,
  rw[LIST_REL_EL_EQN, EVERY_MAP, EVERY_EL]
  >> rw[LIST_EQ_REWRITE]
  >> gs[] >> first_x_assum drule
  >> first_x_assum drule
  >> Cases_on `ty` using semanticPrimitivesPropsTheory.prim_type_cases
  >> rw[semanticPrimitivesTheory.check_type_def]
  >> Cases_on `EL x vs1`
  >> gvs[flat_to_v_def,CaseEq"bool",semanticPrimitivesTheory.Boolv_def]
  >> gvs[flatSemTheory.Boolv_def]);
val _ = show_thm "flat_check_type_list_rel_same_typed=" flat_check_type_list_rel_same;

val _ = show_thm "flat_simple_do_app_typed=" flatPropsTheory.simple_do_app_thm;

val _ = show_thm "semantic_sv_rel_cases_typed=" semanticPrimitivesPropsTheory.sv_rel_cases;
val _ = show_thm "semantic_do_arith_check_type_typed=" semanticPrimitivesPropsTheory.do_arith_check_type;

val _ = show_thm "flat_evaluate_mat_typed=" flatPropsTheory.evaluate_Mat;
val _ = show_thm "flat_evaluate_handle_typed=" flatPropsTheory.evaluate_Handle;
val _ = show_thm "flat_evaluate_match_nil_typed=" flatPropsTheory.evaluate_match_NIL;
val _ = show_thm "flat_evaluate_match_cons_typed=" flatPropsTheory.evaluate_match_CONS;

val _ = show_thm "flat_evaluate_def_typed=" flatPropsTheory.flat_evaluate_def;
val _ = show_thm "flat_store_v_vs_def_typed=" flatPropsTheory.store_v_vs_def;
val _ = show_thm "flat_v_size_aux_typed=" flatPropsTheory.v_size_aux;
val _ = show_thm "flat_ctor_same_type_optrel_typed=" flatPropsTheory.ctor_same_type_OPTREL;
val _ = show_thm "flat_pats_bindings_flat_map_typed=" flatPropsTheory.pats_bindings_FLAT_MAP;
val _ = show_thm "semantic_do_conversion_check_type_typed=" semanticPrimitivesPropsTheory.do_conversion_check_type;
