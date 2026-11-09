load "flatSemTheory"; load "flatPropsTheory";
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
