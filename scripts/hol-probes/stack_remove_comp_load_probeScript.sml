load "preamble";
load "helperLib";
open helperLib;
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val evaluate_upshift = GEN_ALL (prove(``  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(upshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w + word_offset n)))``,
  ho_match_mp_tac upshift_ind>>rw[]>>
  simp[Once upshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w+word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]));
val cl = prove(``!s res s2 t1 k off jump r n.
  stackSem$evaluate ((stackLang$StackLoad r n : 'a stackLang$prog),(s:('a,'b,'c)stackSem$state)) = (res,s2) /\ res <> SOME stackSem$Error /\
  state_rel jump off k s t1 /\ reg_bound (stackLang$StackLoad r n : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackLoad r n : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (res,t2) /\
    (case res of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >>
simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
    >-
      (simp[wordLangTheory.word_op_def]
      \\ simp[mem_load_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ `set_var r h t1 with clock := t1.clock = set_var r h t1` by full_simp_tac(srw_ss())[set_var_def]
      \\ full_simp_tac(srw_ss())[] \\ match_mp_tac state_rel_set_var
      \\ full_simp_tac(srw_ss())[reg_bound_def])
    >>
      fs[stack_load_def,evaluate_def]>>
      qpat_abbrev_tac`t = (set_var r _ _) with clock:= _`>>
      `FLOOKUP t.regs r = SOME(Word (c + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t`,set_var_def,FLOOKUP_UPDATE]>>
      old_drule evaluate_upshift>>
      disch_then (qspec_then `n` assume_tac)>>
      simp[inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>fs[Abbr`t`,set_var_def]>>
      simp[mem_load_def]
      \\ fsrw_tac[ARITH_ss][NOT_LESS]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]>>
      simp[GSYM set_var_def]>>
      match_mp_tac state_rel_set_var>>
      full_simp_tac(srw_ss())[reg_bound_def]);
val _ = print("cl_statement=" ^ term_to_string(concl cl) ^ "\n");
val _ = print("cl_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cl))) ^ "\n");
