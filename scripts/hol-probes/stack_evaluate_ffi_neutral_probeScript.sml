load "preamble"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble wordsTheory stackLangTheory stackPropsTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val inst_clock_neutral_ffi = GEN_ALL (prove(``
  (inst i s = SOME t ==> inst i (s with ffi := k) = SOME (t with ffi := k)) /\
    (inst i s = NONE ==> inst i (s with ffi := k) = NONE)``,
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,state_component_equality,set_fp_var_def]>>
  reverse full_case_tac>>fs[]>>
  TRY
    (qmatch_goalsub_abbrev_tac`get_vars _ _`>>
    fs[get_vars_def,get_var_def]>>
    rpt (BasicProvers.TOP_CASE_TAC>>fs[state_component_equality]))
  \\ rpt (srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality])));
val full = GEN_ALL (prove(concl evaluate_ffi_neutral,
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[empty_env_def])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral_ffi \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with ffi := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]));
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = (print "neutral_ffi_full_statement="; print_term(concl full));
val _ = print("neutral_ffi_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
