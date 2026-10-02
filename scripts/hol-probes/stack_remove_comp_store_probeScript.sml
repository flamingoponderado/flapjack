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
val state_rel_get_var = GEN_ALL (prove(``  state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]));
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
val evaluate_downshift = GEN_ALL (prove(``  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(downshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w - word_offset n)))``,
  ho_match_mp_tac downshift_ind>>rw[]>>
  simp[Once downshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w - 1w * word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  simp[]>>
  FULL_SIMP_TAC std_ss [GSYM WORD_LEFT_ADD_DISTRIB]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]));
val cs = prove(``!s res s2 t1 k off jump r n.
  stackSem$evaluate ((stackLang$StackStore r n : 'a stackLang$prog),(s:('a,'b,'c)stackSem$state)) = (res,s2) /\ res <> SOME stackSem$Error /\
  state_rel jump off k s t1 /\ reg_bound (stackLang$StackStore r n : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackStore r n : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (res,t2) /\
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
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ qexists_tac`0` \\ simp[]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    >-
      (simp[inst_def]
      \\ full_simp_tac(srw_ss())[]
      \\ simp[word_exp_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac (GEN_ALL state_rel_stack_store)
      \\ simp[])
    >>
      simp[stack_store_def,evaluate_def]>>
      fs[get_var_def]>>
      old_drule evaluate_upshift >> disch_then(qspec_then`n` assume_tac)>>
      simp[inst_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>
      fs[get_var_def,FLOOKUP_UPDATE,set_var_def]>>
      simp[mem_store_def]>>
      full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ qpat_abbrev_tac`t' = t1 with <|regs:=_ ; memory := _|>`>>
      `FLOOKUP t'.regs k = SOME (Word (c + bytes_in_word * n2w n + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t'`,FLOOKUP_UPDATE]>>
      old_drule evaluate_downshift>>disch_then(qspec_then`n` assume_tac)>>
      fs[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`t'`]>>
      qmatch_goalsub_abbrev_tac `t1 with <| regs:= R ; memory := M|>`>>
      `t1 with <|regs:=R;memory:=M|> = t1 with memory := M` by
        (simp[state_component_equality,Abbr`R`]>>
        match_mp_tac FUPDATE_ELIM>>
        qpat_x_assum`FLOOKUP _ k = SOME w` kall_tac>>
        qpat_x_assum`FLOOKUP _ k = SOME w` mp_tac>>
        simp[FDOM_FLOOKUP,Once FLOOKUP_DEF])>>
      simp[Abbr`M`]>>
      match_mp_tac (GEN_ALL state_rel_stack_store)>>
      simp[]);
val _ = print("cs_statement=" ^ term_to_string(concl cs) ^ "\n");
val _ = print("cs_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cs))) ^ "\n");
