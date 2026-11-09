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
