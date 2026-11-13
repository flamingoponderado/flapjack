load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "compile_sing=" bvi_to_dataTheory.compile_sing_def;
val _ = show "compile=" bvi_to_dataTheory.compile_def;
val _ = show "compile_sing_eq=" bvi_to_dataTheory.compile_sing_eq;
val _ = show "compile_LENGTH=" bvi_to_dataTheory.compile_LENGTH;
val _ = show "compile_LESS_EQ=" bvi_to_dataTheory.compile_LESS_EQ;
(* The original theorems are local; capture their literal typed statements. *)
val _ = (print "compile_RANGE_lemma_statement="; print_term
  ``!n env tail live xs.
      EVERY (\v. v < (SND (SND (bvi_to_data$compile n env tail live xs))))
        (FST (SND (bvi_to_data$compile n env tail live xs)))``; print "\n");
val _ = (print "compile_RANGE_statement="; print_term
  ``!n env tail live xs ys vs k.
    (bvi_to_data$compile n env tail live xs = (ys,vs,k)) ==>
      EVERY (\v. v < k) vs``; print "\n");
val _ = show "compile_exp_def=" bvi_to_dataTheory.compile_exp_def;
val _ = show "compile_exp_eq=" bvi_to_dataTheory.compile_exp_eq;
val _ = show "compile_part=" bvi_to_dataTheory.compile_part_def;
val _ = show "compile_prog=" bvi_to_dataTheory.compile_prog_def;
val _ = show "i_assign=" bvi_to_dataTheory.iAssign_def;
val _ = show "optimise=" bvi_to_dataTheory.optimise_def;
val _ = show "code_rel=" bvi_to_dataProofTheory.code_rel_def;
val _ = show "state_rel=" bvi_to_dataProofTheory.state_rel_def;
val _ = show "compile_correct=" bvi_to_dataProofTheory.compile_correct;
val _ = show "data_to_bvi_do_eq=" bvi_to_dataProofTheory.data_to_bvi_do_eq;
val _ = show "data_to_bvi_do_app=" bvi_to_dataProofTheory.data_to_bvi_do_app;
val _ = show "data_to_bvi_v_list_to_v_APPEND=" bvi_to_dataProofTheory.data_to_bvi_v_list_to_v_APPEND;
val _ = show "var_corr=" dataPropsTheory.var_corr_def;
val _ = show "get_vars_thm=" dataPropsTheory.get_vars_thm;
val _ = show "get_vars_append=" dataPropsTheory.get_vars_append;
val _ = show "get_vars_reverse=" dataPropsTheory.get_vars_reverse;
val _ = show "EVERY_get_vars=" dataPropsTheory.EVERY_get_vars;
val _ = show "get_vars_IMP_domain=" dataPropsTheory.get_vars_IMP_domain;
val _ = show "do_app_aux_err=" dataPropsTheory.do_app_aux_err;
val _ = show "do_app_err=" dataPropsTheory.do_app_err;
val _ = show "do_app_aux_const=" dataPropsTheory.do_app_aux_const;
val _ = show "do_app_const=" dataPropsTheory.do_app_const;
val _ = show "do_app_io_events_mono=" dataPropsTheory.do_app_io_events_mono;
val _ = show "do_app_stack_max=" dataPropsTheory.do_app_stack_max;
val _ = show "do_app_safe_for_space_mono=" dataPropsTheory.do_app_safe_for_space_mono;
val _ = show "evaluate_io_events_mono=" dataPropsTheory.evaluate_io_events_mono;
val _ = show "evaluate_safe_for_space_mono=" dataPropsTheory.evaluate_safe_for_space_mono;
val _ = show "evaluate_option_le_stack_max=" dataPropsTheory.evaluate_option_le_stack_max;
val _ = show "pop_env_const=" dataPropsTheory.pop_env_const;
val _ = show "pop_env_safe_for_space=" dataPropsTheory.pop_env_safe_for_space;
val _ = show "var_corr_map=" bvi_to_dataProofTheory.var_corr_map;
val _ = show "get_vars_lift_thm=" bvi_to_dataProofTheory.get_vars_lift_thm;
val _ = show "var_corr_inter=" bvi_to_dataProofTheory.var_corr_inter;
val _ = show "get_vars_mk_wf=" bvi_to_dataProofTheory.get_vars_mk_wf;
val _ = show "get_vars_inter=" bvi_to_dataProofTheory.get_vars_inter;
val _ = show "lookup_mk_wf=" sptreeTheory.lookup_mk_wf;
val _ = show "data_to_bvi_result=" bvi_to_dataProofTheory.data_to_bvi_result_def;
val _ = show "data_to_bvi_result_eq=" bvi_to_dataProofTheory.data_to_bvi_result_eq;
val _ = show "missing_var=" (EVAL ``bvi_to_data$compile_sing 4 [] F [] (bvi$Var 5)``);
val _ = show "tail_var=" (EVAL ``bvi_to_data$compile_sing 4 [7] T [] (bvi$Var 0)``);
val _ = show "tail_letcall=" (EVAL ``bvi_to_data$compile_sing 2 [] F []
  (bvi$LetCall 1 0 3 [] (bvi$Return [bvi$Var 0]))``);
val _ = show "FST_compile_part_typed=" bvi_to_dataProofTheory.FST_compile_part;
(* This theorem is local to the source script; replay its original proof. *)
val evaluate_return_range_replay = Q.prove
  (`∀rets ret_vs env s'.
      LENGTH ret_vs = rets ⇒
      bviSem$evaluate ([bvi$Return (GENLIST bvi$Var rets)], ret_vs ++ env, s') =
        (Rerr (Rraise (bviSem$Ret ret_vs)), s')`,
   rw [bviSemTheory.evaluate_def]
   \\ qspecl_then [`0`, `ret_vs ++ env`, `LENGTH ret_vs`, `s'`] mp_tac
       bviPropsTheory.evaluate_genlist_vars
   \\ simp [ETA_AX, rich_listTheory.TAKE_LENGTH_APPEND]);
val _ = show "evaluate_Return_GENLIST_Var_replay_typed=" evaluate_return_range_replay;
val _ = show "optimise_correct_typed=" bvi_to_dataProofTheory.optimise_correct;
val _ = show "jump_exc_peak_safe_typed=" bvi_to_dataProofTheory.jump_exc_peak_safe;
val _ = show "jump_exc_sfs_lss_peak_safe_typed=" bvi_to_dataProofTheory.jump_exc_sfs_lss_peak_safe;
val _ = show "jump_exc_lss_typed=" bvi_to_dataProofTheory.jump_exc_lss;
(* The lookup lemma is local to the original script; print its source statement with inferred types. *)
val _ = (print "find_code_lemma_statement_typed="; print_term
  ``bvi_to_dataProof$state_rel r t2 /\
    bvlSem$find_code dest (MAP bvi_to_dataProof$data_to_bvi_v a) r.code = SOME (args,exp)
    ==> ?args' ss. args = MAP bvi_to_dataProof$data_to_bvi_v args' /\
      dataSem$find_code dest a t2.code t2.stack_frame_sizes =
        SOME (args',bvi_to_data$compile_exp (LENGTH args') exp,ss)``; print "\n");
val _ = show "state_rel_dest_thunk_typed=" bvi_to_dataProofTheory.state_rel_dest_thunk;
val _ = show "MAP_FST_compile_prog_typed=" bvi_to_dataProofTheory.MAP_FST_compile_prog;
val _ = show "state_rel_peak_safe_typed=" bvi_to_dataProofTheory.state_rel_peak_safe;
val _ = show "bvi_evaluate_ind_typed=" bviSemTheory.evaluate_ind;
val _ = show "compile_exp_correct_typed=" bvi_to_dataProofTheory.compile_exp_correct;
(* This theorem is local to the source script; replay its original proof. *)
val state_rel_dec_clock_replay = Q.prove
  (`bvi_to_dataProof$state_rel s1 t1 ⇒
    bvi_to_dataProof$state_rel (bviSem$dec_clock 1 s1) (dataSem$dec_clock t1)`,
   srw_tac[][bvi_to_dataProofTheory.state_rel_def,
     bviSemTheory.dec_clock_def, dataSemTheory.dec_clock_def]);
val _ = show "state_rel_dec_clock_replay_typed=" state_rel_dec_clock_replay;
val _ = show "compile_part_evaluate_typed=" bvi_to_dataProofTheory.compile_part_evaluate;
val _ = show "compile_prog_evaluate_typed=" bvi_to_dataProofTheory.compile_prog_evaluate;
val _ = show "compile_prog_semantics_typed=" bvi_to_dataProofTheory.compile_prog_semantics;
val _ = show "get_code_labels_iAssign_typed=" bvi_to_dataProofTheory.get_code_labels_iAssign;
val _ = show "get_code_labels_compile_typed=" bvi_to_dataProofTheory.get_code_labels_compile;
