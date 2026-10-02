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
val word_shift_def = backend_commonTheory.word_shift_def;
val css = prove(``!s res s2 t1 k off jump r.
  stackSem$evaluate ((stackLang$StackSetSize r : 'a stackLang$prog),(s:('a,'b,'c)stackSem$state)) = (res,s2) /\ res <> SOME stackSem$Error /\
  state_rel jump off k s t1 /\ reg_bound (stackLang$StackSetSize r : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackSetSize r : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (res,t2) /\
    (case res of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >>
simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ `word_shift (:'a) MOD dimword (:'a) = word_shift (:'a)` by
         (fs[state_rel_def,good_dimindex_def,word_shift_def,dimword_def])
    \\ simp[wordLangTheory.word_sh_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[])
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp [set_var_def,FLOOKUP_UPDATE]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[set_var_def,FLOOKUP_UPDATE]
    \\ rev_full_simp_tac(srw_ss())[lsl_word_shift]
    \\ fs[]
    \\ metis_tac[]);
val _ = print("css_statement=" ^ term_to_string(concl css) ^ "\n");
val _ = print("css_proved=" ^ term_to_string(rhs(concl(EQT_INTRO css))) ^ "\n");
