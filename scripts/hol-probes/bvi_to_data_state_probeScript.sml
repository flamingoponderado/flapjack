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
val _ = show "compile_prog_good_code_labels_typed=" bvi_to_dataProofTheory.compile_prog_good_code_labels;
(* This original FFI-error theorem is local; capture its literal typed statement. *)
val _ = (print "state_rel_do_app_FFI_err_statement_typed="; print_term
  ``∀i z r t x.
      bvi_to_dataProof$state_rel r t ∧
      bviSem$do_app (closLang$FFI i) (MAP bvi_to_dataProof$data_to_bvi_v z) r =
        Rerr (Rabort (Rffi_error x)) ⇒
      dataSem$do_app (closLang$FFI i) z t = Rerr (Rabort (Rffi_error x))``;
  print "\n");

(* Replay the original local FFI-error proof with its inferred types. *)
load "preamble";
open preamble bvi_to_dataProofTheory;
val state_rel_do_app_ffi_err_replay = Q.prove
 (`∀i z r t x.
    bvi_to_dataProof$state_rel r t ∧
    bviSem$do_app (closLang$FFI i) (MAP bvi_to_dataProof$data_to_bvi_v z) r =
      Rerr (Rabort (Rffi_error x)) ⇒
    dataSem$do_app (closLang$FFI i) z t = Rerr (Rabort (Rffi_error x))`,
  rpt strip_tac
  \\ qpat_x_assum `bviSem$do_app (FFI i) _ r = _` mp_tac
  \\ simp[bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
          bvlSemTheory.do_app_def,bviSemTheory.bvi_to_bvl_def,AllCaseEqs(),PULL_EXISTS]
  \\ rw[]
  \\ rename1 `MAP data_to_bvi_v z = [RefPtr b1 p1; RefPtr b2 p2]`
  \\ `z = [RefPtr b1 p1; RefPtr b2 p2]` by
       (Cases_on `z` \\ gvs[] \\ Cases_on `t'` \\ gvs[] \\ Cases_on `t''` \\ gvs[]
        \\ Cases_on `h` \\ gvs[] \\ Cases_on `h'` \\ gvs[])
  \\ `lookup p1 t.refs = SOME (ByteArray T cws) ∧
      lookup p2 t.refs = SOME (ByteArray F ws) ∧ t.ffi = r.ffi` by
       (fs[state_rel_def]
        \\ first_assum (qspec_then `p1` mp_tac)
        \\ first_x_assum (qspec_then `p2` mp_tac)
        \\ simp[sptreeTheory.lookup_map]
        \\ Cases_on `lookup p1 t.refs` \\ Cases_on `lookup p2 t.refs` \\ gvs[]
        \\ rpt (rename1 `data_to_bvi_ref rr = _` \\ Cases_on `rr` \\ gvs[]))
  \\ gvs[dataSemTheory.do_app_def,dataSemTheory.do_app_aux_def,dataSemTheory.do_space_def,
         dataLangTheory.op_space_reset_def,data_spaceTheory.op_space_req_def,
         dataSemTheory.do_stack_def]);
val _ = show "state_rel_do_app_FFI_err_replay_typed=" state_rel_do_app_ffi_err_replay;

(* Replay the original local sparse-set lemmas and their inferred types. *)
open sptreeTheory;
val domain_list_insert2 = Q.prove
 (`domain (list_insert xs t) = set xs UNION domain t`,
  ASM_SET_TAC[domain_list_insert]);
val domain_list_to_num_set2 = Q.prove
 (`domain (list_to_num_set xs) = set xs`,
  ASM_SET_TAC[domain_list_to_num_set]);
val list_insert_list_to_num_set_replay = Q.prove
 (`list_insert xs (list_to_num_set (xs ++ ys ++ zs)) =
   list_to_num_set (xs ++ ys ++ zs)`,
  DEP_REWRITE_TAC [spt_eq_thm] >>
  CONJ_TAC >- (simp[] >>
   `!xs A. wf A ==> wf (list_insert xs A)` by
     (Induct_on `xs` >> rw[list_insert_def] >>
      metis_tac[wf_insert ]) >> fs[]) >>
  rw[] >>
  qmatch_goalsub_abbrev_tac `lookup n A = lookup n B` >>
  Cases_on `lookup n A` >>
  Cases_on `lookup n B` >>
  fs[] >> UNABBREV_ALL_TAC >>
  MAP_EVERY imp_res_tac [lookup_NONE_domain ,domain_lookup] >>
  fs[domain_list_insert2,domain_list_to_num_set2] >> metis_tac[]);
val _ = show "domain_list_insert2_replay_typed=" domain_list_insert2;
val _ = show "domain_list_to_num_set2_replay_typed=" domain_list_to_num_set2;
val _ = show "list_insert_list_to_num_set_replay_typed=" list_insert_list_to_num_set_replay;
val _ = show "data_to_bvi_do_app_typed=" bvi_to_dataProofTheory.data_to_bvi_do_app;
val _ = show "data_to_bvi_finalise_cons_typed=" bvi_to_dataProofTheory.data_to_bvi_finalise_cons;
(* Replay the local boolean-projection implication from the original proof. *)
val data_to_bvi_v_Boolv_IMP_replay = Q.prove
  (`bvi_to_dataProof$data_to_bvi_v x0 = bvlSem$Boolv b ⇒ dataSem$dest_Boolv x0 = SOME b`,
   rw [bvlSemTheory.Boolv_def,dataSemTheory.dest_Boolv_def]
   \\ Cases_on `b` \\ simp [] \\ EVAL_TAC);
val _ = show "data_to_bvi_v_Boolv_IMP_replay_typed=" data_to_bvi_v_Boolv_IMP_replay;
val _ = show "do_build_thm_typed=" bvi_to_dataProofTheory.do_build_thm;

(* Replay the original local least-unused-reference proof. *)
open finite_mapTheory;
val refs_rel_LEAST_eq_replay = Q.prove
 (`∀s1 s2.
    (∀n. FLOOKUP s1 n = lookup n (sptree$map data_to_bvi_ref s2)) ⇒
    (LEAST ptr. ptr ∉ FDOM s1) = LEAST ptr. ptr ∉ domain s2`,
  rw []
  \\ `∀x. (x ∈ FDOM s1) = (x ∈ domain s2)`
     by (rw [] \\ EQ_TAC \\ rw [FDOM_FLOOKUP,domain_lookup,lookup_map])
  \\ rw []);
val _ = show "refs_rel_LEAST_eq_replay_typed=" refs_rel_LEAST_eq_replay;
val _ = show "data_to_bvi_do_eq_typed=" bvi_to_dataProofTheory.data_to_bvi_do_eq;
