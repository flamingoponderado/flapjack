load "bossLib";
load "preamble";
load "lab_filterProofTheory";
open bossLib HolKernel Parse preamble labSemTheory labPropsTheory lab_filterTheory lab_filterProofTheory lprefix_lubTheory llistTheory;
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = temp_delsimps ["NORMEQ_CONV"];
val th = prove (``!s t. state_rel s t ==> semantics s = semantics t``,
srw_tac[][labSemTheory.semantics_def] >- (
    DEEP_INTRO_TAC some_intro >>
    full_simp_tac(srw_ss())[FST_EQ_EQUIV] >>
    `state_rel (s with clock := k) (t with clock := k)` by
      fs[state_rel_def,state_component_equality]>>
    `¬(t with clock := k).failed` by full_simp_tac(srw_ss())[state_rel_def] >>
    imp_res_tac filter_correct >> full_simp_tac(srw_ss())[] >>
    metis_tac[] )
  >- (
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    `state_rel (s with clock := k) (t with clock := k)` by
      fs[state_rel_def,state_component_equality]>>
    drule (REWRITE_RULE[GSYM CONJ_ASSOC](ONCE_REWRITE_RULE[CONJ_COMM]filter_correct)) >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    impl_tac >- full_simp_tac(srw_ss())[state_rel_def] >>
    simp[FST_EQ_EQUIV,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    full_simp_tac(srw_ss())[FST_EQ_EQUIV] >>
    imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
    metis_tac[FST,PAIR] )
  >- (
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
      conj_tac >- (
        srw_tac[][] >>
        qhdtm_x_assum`evaluate`mp_tac >>
        drule filter_correct >>
        disch_then(qspec_then`t with clock := k`mp_tac) >>
        impl_tac >-
          fs[state_rel_def,state_component_equality] >>
        strip_tac >> full_simp_tac(srw_ss())[] >> strip_tac >>
        rename1`t with clock := a + b`>>
        rename1`t with clock := c`>>
        qabbrev_tac`d = a+b` >>
        qspecl_then[`c`,`d`]mp_tac LESS_EQ_CASES >>
        simp[LESS_EQ_EXISTS] >> strip_tac >>
        qmatch_assum_rename_tac`k = y + p` >>
        qspecl_then[`p`,`t with clock := y`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
        simp[] >> fsrw_tac[ARITH_ss][] >>
        every_case_tac >> full_simp_tac(srw_ss())[] >>
        imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
        srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
        rpt(first_x_assum(qspec_then`p`mp_tac))>>simp[]>>
        srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
      drule filter_correct >>
      disch_then(qspec_then`t with clock := k`mp_tac) >>
      impl_tac >-
        fs[state_rel_def,state_component_equality] >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      qexists_tac`k+k'`>>simp[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Q.ISPEC_THEN`s with clock := k`mp_tac filter_correct >>
      simp[] >>
      qexists_tac`t with clock := k` >>
      simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
      conj_tac >-
        fs[state_rel_def,state_component_equality] >>
      conj_tac >-
        fs[state_rel_def,state_component_equality] >>
      srw_tac[][] >>
      first_x_assum(qspec_then`k`mp_tac) >>
      srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
      qspecl_then[`k'`,`t with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[ffiTheory.ffi_state_component_equality] ) >>
    strip_tac >>
    qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
    `lprefix_chain l1 ∧ lprefix_chain l2` by (
      unabbrev_all_tac >>
      conj_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      metis_tac[
        labPropsTheory.evaluate_add_clock_io_events_mono
        |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
        LESS_EQ_EXISTS]) >>
    `equiv_lprefix_chain l1 l2` by (
      simp[equiv_lprefix_chain_thm] >>
      unabbrev_all_tac >> simp[PULL_EXISTS] >>
      ntac 2 (pop_assum kall_tac) >>
      simp[LNTH_fromList,PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM] >>
      rpt gen_tac >>
      Q.ISPEC_THEN `s with clock := k` mp_tac filter_correct >>
      Cases_on`evaluate (s with clock := k)`>>full_simp_tac(srw_ss())[] >>
      disch_then(qspec_then`t with clock := k`mp_tac) >>
      impl_tac >-
        fs[state_rel_def,state_component_equality]>>
      simp[] >> strip_tac >>
      conj_tac >> strip_tac >- (
        rev_full_simp_tac(srw_ss())[] >> qexists_tac`k+k'`>>simp[] ) >>
      qspecl_then[`k'`,`s with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      qspecl_then[`k'`,`t with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >> full_simp_tac(srw_ss())[] >>
      qexists_tac`k+k'`>>simp[EL_APPEND1] ) >>
    metis_tac[build_lprefix_lub_thm,unique_lprefix_lub,lprefix_lub_new_chain]));
val _ = show_types := true;
val _ = print "state_rel_IMP_sem_EQ_sem=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "state_rel_IMP_sem_EQ_sem_types=";
val _ = app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";")) (fst (strip_forall (concl th)) @ free_vars (concl th));
val _ = print "\n";
val _ = print ("state_rel_IMP_sem_EQ_sem_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n");
val _ = show_types := false;
val _ = print "state_rel_IMP_sem_EQ_sem_proved=";
val _ = print_term (rhs (concl (EQT_INTRO (prove (concl th, ACCEPT_TAC th)))));
val _ = print "\n";
