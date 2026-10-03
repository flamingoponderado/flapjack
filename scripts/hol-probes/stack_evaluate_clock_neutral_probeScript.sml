load "preamble"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble wordsTheory stackLangTheory stackPropsTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val inst_clock_neutral = GEN_ALL (prove(``
  (inst i s = SOME t ==> inst i (s with clock := k) = SOME (t with clock := k)) /\
    (inst i s = NONE ==> inst i (s with clock := k) = NONE)``,
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,set_fp_var_def]
  \\ srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality]));
val full = GEN_ALL (prove(concl evaluate_clock_neutral,
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with clock := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]));
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = (print "neutral_clock_full_statement="; print_term(concl full));
val _ = print("neutral_clock_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
val _ = (print "neutral_clock_skip="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Skip:64 stackLang$prog)``))));
val _ = (print "neutral_clock_halt="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Halt 0:64 stackLang$prog)``))));
val _ = (print "neutral_clock_inst="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Inst asm$Skip:64 stackLang$prog)``))));
val _ = (print "neutral_clock_seq="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Seq stackLang$Skip (stackLang$Halt 0):64 stackLang$prog)``))));
val _ = (print "neutral_clock_nested="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Seq (stackLang$Seq stackLang$Skip (stackLang$Inst asm$Skip)) (stackLang$Halt 0):64 stackLang$prog)``))));
val _ = (print "neutral_clock_tick="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Tick:64 stackLang$prog)``))));
val _ = (print "neutral_clock_loop="; print_term(rhs(concl(EVAL ``clock_neutral (stackLang$Loop stackLang$Skip:64 stackLang$prog)``))));
