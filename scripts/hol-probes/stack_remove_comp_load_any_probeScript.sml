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
val cla = prove(``!s res s2 t1 k off jump r n.
  stackSem$evaluate ((stackLang$StackLoadAny r n : 'a stackLang$prog),(s:('a,'b,'c)stackSem$state)) = (res,s2) /\ res <> SOME stackSem$Error /\
  state_rel jump off k s t1 /\ reg_bound (stackLang$StackLoadAny r n : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackLoadAny r n : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (res,t2) /\
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
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k` by fs[]
    \\ simp[wordLangTheory.word_op_def]
    \\ fs[FLOOKUP_UPDATE]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[mem_load_def]
    \\ rpt(qpat_x_assum`∀x. _`kall_tac)
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND])
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[GSYM set_var_def]);
val _ = print("cla_statement=" ^ term_to_string(concl cla) ^ "\n");
val _ = print("cla_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cla))) ^ "\n");
