(* Typed source precondition for closure known-function optimization. *)
load "clos_knownProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "syntax_ok_typed=" clos_knownProofTheory.syntax_ok_def;
val _ = show "unique_set_globals_subexps_typed=" clos_knownProofTheory.unique_set_globals_subexps;
val _ = show "unique_set_globals_typed=" clos_knownProofTheory.unique_set_globals_def;
val _ = show "unique_set_globals_shift_seq_typed=" clos_knownProofTheory.unique_set_globals_shift_seq;
val _ = show "unique_set_globals_distinct_typed=" clos_knownProofTheory.unique_set_globals_IMP_es_distinct_elist_globals;
val _ = show "nil_unique_set_globals_typed=" clos_knownProofTheory.nil_unique_set_globals;
val _ = show "mglobals_disjoint_rw_typed=" clos_knownProofTheory.mglobals_disjoint_rw;
val _ = show "mglobals_disjoint_typed=" clos_knownProofTheory.mglobals_disjoint_def;
val _ = show "gapprox_extend_typed=" clos_knownProofTheory.gapprox_extend_def;
val _ = show "state_globals_approx_disjoint_extends_typed=" clos_knownProofTheory.state_globals_approx_disjoint_extends;
val _ = show "state_globals_approx_known_op_evaluate_typed=" clos_knownProofTheory.state_globals_approx_known_op_evaluate;
val _ = show "mglobals_disjoint_evaluate_typed=" clos_knownProofTheory.mglobals_disjoint_evaluate;
val _ = show "bag_all_distinct_typed=" bagTheory.BAG_ALL_DISTINCT;
val _ = show "option_val_approx_spt_typed=" clos_knownTheory.option_val_approx_spt_def;
val _ = show "option_upd_val_spt_typed=" clos_knownTheory.option_upd_val_spt_def;
val _ = show "contains_closures_typed=" clos_knownTheory.contains_closures_def;
val _ = show "merge_typed=" clos_knownTheory.merge_def;
val _ = show "known_ind_typed=" clos_knownTheory.known_ind;
val _ = show "known_correct_approx_typed=" clos_knownProofTheory.known_correct_approx;
val _ = show "known_exp_rel_typed=" clos_knownProofTheory.exp_rel_def;
val _ = show "known_exp_rel_dec_typed=" clos_knownProofTheory.exp_rel_dec_inline_factor;
val _ = show "known_exp_rel_update_typed=" clos_knownProofTheory.exp_rel_upd_inline_factor;
val _ = show "known_f_rel_typed=" clos_knownProofTheory.f_rel_def;
val _ = show "known_f_rel_update_typed=" clos_knownProofTheory.f_rel_upd_inline_factor;
val _ = show "known_v_rel_typed=" clos_knownProofTheory.v_rel_def;
val _ = show "known_v_rel_app_typed=" clos_knownProofTheory.v_rel_app_def;
val _ = show "known_v_rel_app_none_typed=" clos_knownProofTheory.v_rel_app_NONE;
val _ = show "known_v_rel_subspt_typed=" clos_knownProofTheory.v_rel_subspt;
val _ = show "known_v_rel_list_subspt_typed=" clos_knownProofTheory.v_rel_LIST_REL_subspt;
val _ = show "known_v_rel_update_typed=" clos_knownProofTheory.v_rel_upd_inline_factor;
val _ = show "known_v_rel_block_typed=" clos_knownProofTheory.v_rel_Block;
val _ = show "known_v_rel_bool_typed=" clos_knownProofTheory.v_rel_Boolv;
val _ = show "known_v_rel_unit_typed=" clos_knownProofTheory.v_rel_Unit;
val _ = show "known_ref_rel_rules_typed=" clos_knownProofTheory.ref_rel_rules;
val _ = show "known_ref_rel_subspt_typed=" clos_knownProofTheory.ref_rel_subspt;
val _ = show "known_ref_rel_update_typed=" clos_knownProofTheory.ref_rel_upd_inline_factor;
val _ = show "known_loptrel_typed=" clos_knownProofTheory.loptrel_def;
val _ = show "known_next_g_typed=" clos_knownProofTheory.next_g_def;
val _ = show "known_compile_inc_typed=" clos_knownTheory.compile_inc_def;
val _ = show "known_state_rel_typed=" clos_knownProofTheory.state_rel_def;
val _ = show "known_state_rel_subspt_typed=" clos_knownProofTheory.state_rel_subspt;
val _ = show "known_state_rel_update_typed=" clos_knownProofTheory.state_rel_upd_inline_factor;
val _ = show "known_state_rel_get_global_typed=" clos_knownProofTheory.state_rel_get_global_IMP;
val _ = show "known_state_oracle_safety_typed=" clos_knownProofTheory.oracle_state_sgc_free_def;
val _ = show "known_state_oracle_safety_shift_typed=" clos_knownProofTheory.oracle_state_sgc_free_shift_seq;
val _ = show "known_oracle_subspt_typed=" clos_knownProofTheory.oracle_gapprox_subspt_def;
val _ = show "known_oracle_subspt_add_typed=" clos_knownProofTheory.oracle_gapprox_subspt_add;
val _ = show "known_oracle_subspt_alt_typed=" clos_knownProofTheory.oracle_gapprox_subspt_alt;
val _ = show "known_oracle_subspt_shift_typed=" clos_knownProofTheory.oracle_gapprox_subspt_shift_seq;
val _ = show "known_oracle_subspt_evaluate_typed=" clos_knownProofTheory.oracle_gapprox_subspt_evaluate;
val _ = show "known_op_subspt_typed=" clos_knownProofTheory.known_op_subspt;
val _ = show "known_subspt_typed=" clos_knownProofTheory.known_subspt;
val _ = show "known_subspt_composition_typed=" clos_knownProofTheory.subspt_known_elist_globals;
val _ = show "known_subspt_op_composition_typed=" clos_knownProofTheory.subspt_known_op_elist_globals;
val _ = show "known_state_oracle_disjoint_typed=" clos_knownProofTheory.state_oracle_mglobals_disjoint_def;
val _ = show "known_state_oracle_disjoint_evaluate_typed=" clos_knownProofTheory.state_oracle_mglobals_disjoint_evaluate_suff;
val _ = show "known_co_fn_none_typed=" clos_knownProofTheory.co_every_Fn_vs_NONE_def;
val _ = show "known_co_fn_none_shift_typed=" clos_knownProofTheory.co_every_Fn_vs_NONE_shift_seq;
val _ = show "known_state_rel_co_globals_typed=" clos_knownProofTheory.state_rel_co_elist_globals;
val _ = show "known_state_rel_first_n_typed=" clos_knownProofTheory.state_rel_first_n_exps;
val _ = show "known_state_rel_unique_typed=" clos_knownProofTheory.state_rel_unique_set_globals;
val known_compile_inc_update_replay = Q.prove(
  `clos_known$compile_inc ((c:clos_known$config) with inline_factor := k) = clos_known$compile_inc c`,
  simp [clos_knownTheory.compile_inc_def, FUN_EQ_THM, pairTheory.FORALL_PROD,
        clos_knownTheory.reset_inline_factor_def]);
val _ = show "known_compile_inc_update_replay_typed=" known_compile_inc_update_replay;
val _ = show "known_evaluate_app_exact_typed=" clos_knownProofTheory.evaluate_app_exact_rw;
val _ = show "mk_ticks_set_globals_typed=" clos_knownProofTheory.mk_Ticks_set_globals;
val _ = show "known_preserves_esgc_free_0_typed=" clos_knownProofTheory.known_preserves_esgc_free_0;
val _ = show "known_elglobals_dont_grow_typed=" clos_knownProofTheory.known_elglobals_dont_grow;
val _ = show "known_preserves_esgc_free_typed=" clos_knownProofTheory.known_preserves_esgc_free;
val _ = show "known_changed_globals_typed=" clos_knownProofTheory.known_changed_globals;
val _ = show "known_unchanged_globals_typed=" clos_knownProofTheory.known_unchanged_globals;
val _ = show "known_changed_globals_alt_set_typed=" clos_knownProofTheory.known_changed_globals_alt_set;
val _ = show "state_globals_approx_known_mglobals_disjoint_typed=" clos_knownProofTheory.state_globals_approx_known_mglobals_disjoint;
val _ = show "evaluate_IMP_shift_seq_typed=" clos_knownProofTheory.evaluate_IMP_shift_seq;
val _ = show "unique_set_globals_evaluate_typed=" clos_knownProofTheory.unique_set_globals_evaluate;
val _ = show "oracle_gapprox_disjoint_evaluate_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_evaluate;
val _ = show "oracle_gapprox_disjoint_lemma_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_lemma;
val _ = show "gapprox_disjoint_def_typed=" clos_knownProofTheory.gapprox_disjoint_def;
val _ = show "gapprox_disjoint_rw_typed=" clos_knownProofTheory.gapprox_disjoint_rw;
val _ = show "oracle_gapprox_disjoint_def_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_def;
val _ = show "oracle_gapprox_disjoint_shift_seq_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_shift_seq;
val _ = show "oracle_gapprox_disjoint_first_n_exps_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_first_n_exps;
val _ = show "elist_globals_first_n_exps_lemma_typed=" clos_knownProofTheory.elist_globals_first_n_exps_lemma;
val _ = show "elist_globals_first_n_exps_exists_typed=" clos_knownProofTheory.elist_globals_first_n_exps_exists;
val _ = show "oracle_gapprox_disjoint_shift_seq_unique_set_globals_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_shift_seq_unique_set_globals;
val _ = show "oracle_gapprox_disjoint_Install_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_Install;
val _ = show "oracle_gapprox_disjoint_subspt_typed=" clos_knownProofTheory.oracle_gapprox_disjoint_subspt;
val _ = show "elist_globals_first_n_exps_shift_seq_lemma_typed=" clos_knownProofTheory.elist_globals_first_n_exps_shift_seq_lemma;
val _ = show "state_globals_approx_evaluate_typed=" clos_knownProofTheory.state_globals_approx_evaluate;
val _ = show "known_changed_globals_cases_typed=" clos_knownProofTheory.known_changed_globals_cases;
val _ = show "known_op_typed=" clos_knownTheory.known_op_def;
val _ = show "get_size_aux_typed=" clos_knownTheory.get_size_aux_def;
val _ = show "get_size_typed=" clos_knownTheory.get_size_def;
val _ = show "get_size_sc_aux_typed=" clos_knownTheory.get_size_sc_aux_def;
val _ = show "get_size_sc_typed=" clos_knownTheory.get_size_sc_def;
val _ = show "clos_approx_typed=" clos_knownTheory.clos_approx_def;
val _ = show "clos_gen_noinline_typed=" clos_knownTheory.clos_gen_noinline_def;
val _ = show "mk_ticks_typed=" clos_knownTheory.mk_Ticks_def;
val _ = show "evaluate_mk_ticks_typed=" clos_knownProofTheory.evaluate_mk_Ticks_rw;
val _ = show "get_size_sc_aux_correct_typed=" clos_knownTheory.get_size_sc_aux_correct;
val _ = show "get_size_sc_some_typed=" clos_knownTheory.get_size_sc_SOME;
val _ = show "free_typed=" clos_knownTheory.free_def;
val _ = show "closed_typed=" clos_knownTheory.closed_def;
val _ = show "decide_inline_typed=" clos_knownTheory.decide_inline_def;
val _ = show "decide_inline_positive_typed=" clos_knownTheory.decide_inline_LetInline;
val _ = show "fv_max_def_typed=" clos_knownProofTheory.fv_max_def;
val _ = show "fv_max_smart_typed=" clos_knownProofTheory.fv_max_SmartOp;
val _ = show "fv_max_cons_typed=" clos_knownProofTheory.fv_max_cons;
val _ = show "fv_max_append_typed=" clos_knownProofTheory.fv_max_append;
val _ = show "fv_max_less_typed=" clos_knownProofTheory.fv_max_less;
val _ = show "fv_max_rw_typed=" clos_knownProofTheory.fv_max_rw;
val _ = show "fv_max_ticks_typed=" clos_knownProofTheory.fv_max_mk_Ticks;
val _ = show "val_approx_val_rules_typed=" clos_knownProofTheory.val_approx_val_rules;
val _ = show "val_approx_merge_left_typed=" clos_knownProofTheory.val_approx_val_merge_I_lemma;
val _ = show "val_approx_merge_typed=" clos_knownProofTheory.val_approx_val_merge_I;
val _ = show "known_merge_comm_typed=" clos_knownPropsTheory.merge_comm;
val _ = show "state_globals_approx_typed=" clos_knownProofTheory.state_globals_approx_def;
val _ = show "state_globals_clock_typed=" clos_knownProofTheory.state_globals_approx_clock_fupd;
val _ = show "state_globals_dec_clock_typed=" clos_knownProofTheory.state_globals_approx_dec_clock;
val _ = show "state_globals_refs_typed=" clos_knownProofTheory.state_globals_approx_refsfupd;
val _ = show "state_globals_ffi_typed=" clos_knownProofTheory.state_globals_approx_ffifupd;
val _ = show "state_globals_code_typed=" clos_knownProofTheory.state_globals_approx_codeupd;
val _ = show "state_globals_oracle_typed=" clos_knownProofTheory.state_globals_approx_coupd;
val _ = show "known_op_correct_approx_typed=" clos_knownProofTheory.known_op_correct_approx;
val _ = show "val_approx_sgc_free_typed=" clos_knownProofTheory.val_approx_sgc_free_def;
val _ = show "val_approx_sgc_free_merge_typed=" clos_knownProofTheory.val_approx_sgc_free_merge;
val _ = show "globals_approx_sgc_free_typed=" clos_knownProofTheory.globals_approx_sgc_free_def;
val _ = show "known_op_preserves_esgc_free_typed=" clos_knownProofTheory.known_op_preserves_esgc_free;
val _ = show "elist_globals_empty_typed=" clos_knownProofTheory.elist_globals_empty;
val _ = show "clos_gen_noinline_safe_typed=" clos_knownProofTheory.clos_gen_noinline_val_approx_sgc_free;
val _ = show "decide_inline_imp_clos_typed=" clos_knownProofTheory.decide_inline_LetInline_IMP_Clos;
val _ = show "decide_inline_imp_clos_lopt_typed=" clos_knownProofTheory.decide_inline_LetInline_IMP_Clos_lopt;
val _ = show "known_def_typed=" clos_knownTheory.known_def;
val _ = show "known_length_typed=" clos_knownTheory.known_LENGTH;
val _ = show "known_length_eq_typed=" clos_knownTheory.known_LENGTH_EQ_E;
val _ = show "known_sing_typed=" clos_knownTheory.known_sing;
val _ = show "known_sing_eq_typed=" clos_knownTheory.known_sing_EQ_E;
val _ = show "mapped_globals_typed=" clos_knownProofTheory.mapped_globals_def;
val _ = show "mglobals_extend_typed=" clos_knownProofTheory.mglobals_extend_def;
val _ = show "mglobals_extend_refl_typed=" clos_knownProofTheory.mglobals_extend_refl;
val _ = show "mglobals_extend_trans_typed=" clos_knownProofTheory.mglobals_extend_trans;
val _ = show "mglobals_extend_subset_typed=" clos_knownProofTheory.mglobals_extend_SUBSET;
val _ = show "state_globals_approx_subspt_typed=" clos_knownProofTheory.state_globals_approx_subspt;
val _ = show "known_op_changed_globals_typed=" clos_knownProofTheory.known_op_changed_globals;
val _ = show "known_op_changed_globals_cases_typed=" clos_knownProofTheory.known_op_changed_globals_cases;
val _ = show "known_op_changed_globals_alt_set_typed=" clos_knownProofTheory.known_op_changed_globals_alt_set;
val _ = show "do_app_ssgc_typed=" clos_knownProofTheory.do_app_ssgc;
val _ = show "evaluate_changed_globals_typed=" clos_knownProofTheory.evaluate_changed_globals;
val _ = show "evaluate_app_changed_globals_typed=" clos_knownProofTheory.evaluate_app_changed_globals;
val _ = show "evaluate_ind_typed=" closSemTheory.evaluate_ind;
val _ = show "simple_val_rel_do_app_rev_typed=" closPropsTheory.simple_val_rel_do_app_rev;
val _ = show "simple_val_rel_do_app_typed=" closPropsTheory.simple_val_rel_do_app;

(* Typed replay of the source-local known-optimizer primitive lemma. *)
val _ = (print "known_do_app_lemma_statement_typed="; print_term
 ``!c g (s:(clos_known$val_approx sptree$num_map#'c,'ffi) closSem$state) t xs ys opp.
   clos_knownProof$state_rel c g s t /\ LIST_REL (clos_knownProof$v_rel c g) xs ys ==>
   case closSem$do_app opp xs s of
   | Rerr err1 => ?err2. closSem$do_app opp ys t = Rerr err2 /\ exc_rel (clos_knownProof$v_rel c g) err1 err2
   | Rval (x,s1) => ?y t1. clos_knownProof$v_rel c g x y /\ clos_knownProof$state_rel c g s1 t1 /\
                           closSem$do_app opp ys t = Rval (y,t1)``; print "\n");

(* Typed replays of source-local decoder preservation statements. *)
val _ = (print "known_v_rel_bytes_statement_typed="; print_term
 ``clos_knownProof$v_rel c g x y ==> closSem$v_to_bytes y = closSem$v_to_bytes x``; print "\n");
val _ = (print "known_v_rel_words_statement_typed="; print_term
 ``clos_knownProof$v_rel c g x y ==> closSem$v_to_words y = closSem$v_to_words x``; print "\n");

(* The local optimizer simulation statement with both conjuncts and inferred types. *)
val _ = (print "known_correct0_statement_typed="; print_term
 ``(!xs env1full (s0:(clos_known$val_approx sptree$num_map#'c,'ffi) closSem$state) res1 s env1 xenv1
     env2 xenv2 t0 c g0 g aenv eas.
      closSem$evaluate (xs, env1full, s0) = (res1, s) /\
      clos_known$known c xs aenv g0 = (eas, g) /\
      clos_knownProof$state_rel c (clos_knownProof$next_g s0) s0 t0 /\
      closProps$every_Fn_vs_NONE xs /\
      clos_knownProof$co_every_Fn_vs_NONE s0.compile_oracle /\
      clos_knownProof$mglobals_disjoint s0.globals xs /\
      clos_knownProof$oracle_gapprox_disjoint (clos_knownProof$next_g s0) s0.compile_oracle /\
      clos_knownProof$state_oracle_mglobals_disjoint s0 /\
      EVERY closProps$esgc_free xs /\ closProps$ssgc_free s0 /\
      EVERY closProps$vsgc_free env1full /\
      LIST_REL clos_knownProof$val_approx_val aenv env1 /\
      clos_knownProof$oracle_state_sgc_free s0.compile_oracle /\
      clos_knownProof$globals_approx_sgc_free g0 /\
      EVERY clos_knownProof$val_approx_sgc_free aenv /\
      clos_knownProof$state_globals_approx s0 (clos_knownProof$next_g s0) /\
      sptree$subspt g0 g /\ sptree$subspt g (clos_knownProof$next_g s0) /\
      clos_knownProof$oracle_gapprox_subspt s0.compile_oracle /\
      clos_knownProof$fv_max (LENGTH env1) xs /\
      LIST_REL (clos_knownProof$v_rel c (clos_knownProof$next_g s0)) env1 env2 /\
      clos_knownProof$unique_set_globals xs s0.compile_oracle /\
      backendProps$is_state_oracle (clos_known$compile_inc c) s0.compile_oracle /\
      env1full = env1 ++ xenv1 /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        closSem$evaluate (MAP FST eas, env2 ++ xenv2, t0) = (res2, t) /\
        semanticPrimitivesProps$result_rel (LIST_REL (clos_knownProof$v_rel c (clos_knownProof$next_g s))) (clos_knownProof$v_rel c (clos_knownProof$next_g s)) res1 res2 /\
        clos_knownProof$state_rel c (clos_knownProof$next_g s) s t /\
        clos_knownProof$state_globals_approx s (clos_knownProof$next_g s) /\
        backendProps$is_state_oracle (clos_known$compile_inc c) s.compile_oracle /\
        clos_knownProof$oracle_gapprox_disjoint (clos_knownProof$next_g s) s.compile_oracle) /\
   (!lopt1 f1 args1 (s0:(clos_known$val_approx sptree$num_map#'c,'ffi) closSem$state) res1 s lopt2 f2 args2 t0 c argsopt.
      closSem$evaluate_app lopt1 f1 args1 s0 = (res1, s) /\
      clos_knownProof$v_rel_app c (clos_knownProof$next_g s0) f1 f2 argsopt /\
      clos_knownProof$oracle_gapprox_disjoint (clos_knownProof$next_g s0) s0.compile_oracle /\
      clos_knownProof$state_oracle_mglobals_disjoint s0 /\
      closProps$ssgc_free s0 /\ closProps$vsgc_free f1 /\ EVERY closProps$vsgc_free args1 /\
      clos_knownProof$oracle_state_sgc_free s0.compile_oracle /\
      clos_knownProof$co_every_Fn_vs_NONE s0.compile_oracle /\
      clos_knownProof$unique_set_globals [] s0.compile_oracle /\
      backendProps$is_state_oracle (clos_known$compile_inc c) s0.compile_oracle /\
      LIST_REL (clos_knownProof$v_rel c (clos_knownProof$next_g s0)) args1 args2 /\
      clos_knownProof$state_rel c (clos_knownProof$next_g s0) s0 t0 /\
      clos_knownProof$state_globals_approx s0 (clos_knownProof$next_g s0) /\
      clos_knownProof$oracle_gapprox_subspt s0.compile_oracle /\
      clos_knownProof$loptrel f2 (LENGTH args1) lopt1 lopt2 /\
      (IS_SOME argsopt ==> argsopt = SOME args1 /\ args1 <> [] /\ ?exp env. closSem$dest_closure s0.max_app lopt1 f1 args1 = SOME (Full_app exp env [])) /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        closSem$evaluate_app lopt2 f2 args2 t0 = (res2, t) /\
        semanticPrimitivesProps$result_rel (LIST_REL (clos_knownProof$v_rel c (clos_knownProof$next_g s))) (clos_knownProof$v_rel c (clos_knownProof$next_g s)) res1 res2 /\
        clos_knownProof$state_rel c (clos_knownProof$next_g s) s t /\
        clos_knownProof$state_globals_approx s (clos_knownProof$next_g s) /\
        backendProps$is_state_oracle (clos_known$compile_inc c) s.compile_oracle /\
        clos_knownProof$oracle_gapprox_disjoint (clos_knownProof$next_g s) s.compile_oracle)``; print "\n");

(* Local theorem: replay the original statement with explicit theory qualifiers. *)
val _ = (print "evaluate_changed_globals_0_statement_typed="; print_term
 ``(!es env (s0:('c,'ffi) closSem$state) res s.
      closSem$evaluate (es, env, s0) = (res, s) /\
      closProps$ssgc_free s0 /\ EVERY closProps$esgc_free es /\
      EVERY closProps$vsgc_free env ==>
        closProps$ssgc_free s /\ closProps$rsgc_free res /\
        ?n. s.compile_oracle = shift_seq n s0.compile_oracle /\
          clos_knownProof$mglobals_extend s0.globals
            (SET_OF_BAG (closProps$elist_globals es) UNION
             SET_OF_BAG (closProps$elist_globals (FLAT (clos_knownProof$first_n_exps s0.compile_oracle n)))) s.globals) /\
   (!loc_opt f args (s0:('c,'ffi) closSem$state) res s.
      closSem$evaluate_app loc_opt f args s0 = (res, s) /\
      closProps$ssgc_free s0 /\ closProps$vsgc_free f /\ EVERY closProps$vsgc_free args ==>
        closProps$ssgc_free s /\ closProps$rsgc_free res /\
        ?n. s.compile_oracle = shift_seq n s0.compile_oracle /\
          clos_knownProof$mglobals_extend s0.globals
            (SET_OF_BAG (closProps$elist_globals (FLAT (clos_knownProof$first_n_exps s0.compile_oracle n)))) s.globals)``; print "\n");

val _ = show "dest_closure_full_sgc_free_typed=" clos_knownProofTheory.dest_closure_Full_sgc_free;
(* The theorem is local in the source; print its source statement with inferred types. *)
val _ = (print "update_thunk_ssgc_free_statement_typed="; print_term
  ``closProps$ssgc_free s ∧
    EVERY closProps$vsgc_free vs ∧
    closSem$update_thunk [closSem$RefPtr v ptr] s.refs vs = SOME refs ⇒
    closProps$ssgc_free (s with refs := refs)``; print "\n");
val _ = show "first_n_exps_typed=" clos_knownProofTheory.first_n_exps_def;
val _ = show "first_n_exps_shift_seq_typed=" clos_knownProofTheory.first_n_exps_shift_seq;
val _ = show "mem_first_n_exps_typed=" clos_knownProofTheory.MEM_first_n_exps;
val _ = show "shift_seq_zero_typed=" clos_knownProofTheory.shift_seq_zero;
val _ = show "shift_seq_add_typed=" clos_knownProofTheory.shift_seq_add;
val _ = show "ssgc_free_co_shift_seq_typed=" clos_knownProofTheory.ssgc_free_co_shift_seq;
val _ = show "ssgc_free_do_install_typed=" clos_knownProofTheory.ssgc_free_do_install;
val _ = show "do_install_ssgc_typed=" clos_knownProofTheory.do_install_ssgc;
val _ = show "set_globals_empty_esgc_free_typed=" closPropsTheory.set_globals_empty_esgc_free;
val _ = show "vsgc_free_typed=" closPropsTheory.vsgc_free_def;
val _ = show "rsgc_free_typed=" closPropsTheory.rsgc_free_def;
val _ = show "ssgc_free_typed=" closPropsTheory.ssgc_free_def;
val _ = show "vsgc_free_unit_typed=" closPropsTheory.vsgc_free_Unit;
val _ = show "vsgc_free_bool_typed=" closPropsTheory.vsgc_free_Boolv;
val _ = show "ssgc_free_clock_typed=" closPropsTheory.ssgc_free_clockupd;
val _ = show "ssgc_free_dec_clock_typed=" closPropsTheory.ssgc_free_dec_clock;

(* Local theorem: replay its statement with inferred source and target types. *)
val _ = (print "rel_update_thunk_statement_typed="; print_term
  ``clos_knownProof$state_rel c g s1 s2 ∧
    LIST_REL (clos_knownProof$v_rel c g) vs ys ⇒
      (closSem$update_thunk [closSem$RefPtr v ptr] s1.refs vs = SOME refs1 ⇒
       ∃refs2. closSem$update_thunk [closSem$RefPtr v ptr] s2.refs ys = SOME refs2 ∧
         clos_knownProof$state_rel c g (s1 with refs := refs1) (s2 with refs := refs2))``; print "\n");

val _ = show "dest_closure_none_loc_typed=" closPropsTheory.dest_closure_none_loc;
