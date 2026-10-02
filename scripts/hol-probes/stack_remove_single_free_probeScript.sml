load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val sf = GEN_ALL (prove(``state_rel jump off k s t1 ∧
   ((r,s2) = (NONE, s with stack_space := s.stack_space + n)) ∧
   ¬(LENGTH s.stack < s.stack_space + n) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_free k n,t1 with clock := t1.clock + ck) = (r,t2) ∧ state_rel jump off k s2 t2``,
  simp[single_stack_free_def,evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[wordSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ simp[FLOOKUP_UPDATE]
  \\ rw[] >> TRY (metis_tac[])
  \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ simp[RIGHT_ADD_DISTRIB,GSYM word_add_n2w]));
val _ = print("sf_statement=" ^ term_to_string(concl sf) ^ "\n");
val _ = print("sf_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sf))) ^ "\n");
