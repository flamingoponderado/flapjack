load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory miscTheory set_sepTheory;
val _ = Globals.linewidth := 20000;
val word_list_exists_replay = prove(``(word_list_exists a 0 = emp) /\
    (word_list_exists a (SUC n) =
     SEP_EXISTS w. one (a,w) * word_list_exists (a + bytes_in_word) n)``,
  full_simp_tac(srw_ss())[word_list_exists_def,LENGTH_NIL,FUN_EQ_THM,ADD1,
          SEP_EXISTS_THM,cond_STAR,word_list_def,SEP_CLAUSES]
  \\ srw_tac[][] \\ eq_tac \\ srw_tac[][]
  THEN1
   (Cases_on `xs` \\ full_simp_tac(srw_ss())[ADD1]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ qexists_tac `h` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `t` \\ full_simp_tac(srw_ss())[SEP_CLAUSES])
  \\ qexists_tac `w::xs`
  \\ full_simp_tac(srw_ss())[word_list_def,ADD1,STAR_ASSOC,cond_STAR]);
val _ = print("word_list_exists_statement=" ^ term_to_string(concl word_list_exists_replay) ^ "\n");
val _ = print("word_list_exists_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_list_exists_replay))) ^ "\n");
