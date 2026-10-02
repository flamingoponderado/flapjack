load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val su = GEN_ALL (prove(``  ∀r n st w.
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
val _ = print("su_statement=" ^ term_to_string(concl su) ^ "\n");
val _ = print("su_proved=" ^ term_to_string(rhs(concl(EQT_INTRO su))) ^ "\n");
val sd = GEN_ALL (prove(``  ∀r n st w.
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
val _ = print("sd_statement=" ^ term_to_string(concl sd) ^ "\n");
val _ = print("sd_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sd))) ^ "\n");
