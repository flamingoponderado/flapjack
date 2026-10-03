load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val sa = GEN_ALL (prove(``   !xs ys a.
      word_list a (xs ++ ys) =
      word_list a xs * word_list (a + bytes_in_word * n2w (LENGTH xs)) ys``,
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,GSYM word_add_n2w]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]));
val _ = print("sa_statement=" ^ term_to_string(concl sa) ^ "\n");
val _ = print("sa_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sa))) ^ "\n");
