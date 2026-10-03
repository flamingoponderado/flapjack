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
open helperLib;
val stack_write = GEN_ALL (prove(``   ∀stack base p m d a v.
   (word_list base stack * p) (fun2set (m,d)) ∧ a < LENGTH stack ⇒
   (word_list base (LUPDATE v a stack) * p) (fun2set ((base + bytes_in_word * (n2w a) =+ v) m,d))``,
  Induct \\ simp[word_list_def] \\ srw_tac[][]
  \\ Cases_on`a`\\full_simp_tac(srw_ss())[LUPDATE_def]
  \\ full_simp_tac(srw_ss())[word_list_def] >- SEP_W_TAC
  \\ SEP_F_TAC
  \\ disch_then old_drule
  \\ simp[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ srw_tac[star_ss][]));
val _ = print("sw_statement=" ^ term_to_string(concl stack_write) ^ "\n");
val _ = print("sw_proved=" ^ term_to_string(rhs(concl(EQT_INTRO stack_write))) ^ "\n");
val state_rel_stack_store = GEN_ALL (prove(``   state_rel jump off k s t ∧ st = s.stack ∧
   FLOOKUP t.regs k = SOME (Word b) ∧
   s.stack_space + n < LENGTH st ∧
   b + bytes_in_word * n2w n = a
   ⇒
   state_rel jump off k (s with stack := LUPDATE x (n + s.stack_space) st)
     (t with memory := (a =+ x) t.memory)``,
  simp[state_rel_def]
  \\ strip_tac
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq
  \\ REWRITE_TAC[GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ REWRITE_TAC[Once STAR_COMM]
  \\ REWRITE_TAC[Once ADD_COMM]
  \\ match_mp_tac stack_write
  \\ fsrw_tac[star_ss][AC ADD_COMM ADD_ASSOC]));
val _ = print("srw_statement=" ^ term_to_string(concl state_rel_stack_store) ^ "\n");
val _ = print("srw_proved=" ^ term_to_string(rhs(concl(EQT_INTRO state_rel_stack_store))) ^ "\n");
