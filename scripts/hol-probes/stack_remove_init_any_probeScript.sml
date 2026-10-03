load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory set_sepTheory
 miscTheory wordsTheory listTheory addressTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;

(* Local originals 2727-2737, replayed unchanged. *)
val MOD_EQ_IMP_MULT = prove(
  ``!n d. n MOD d = 0 /\ d <> 0 ==> ?k. n = d * k``,
  rw [] \\ fs [MOD_EQ_0_DIVISOR] \\ metis_tac []);
val _ = (print "MOD_EQ_IMP_MULT_statement="; print_term (concl (GEN_ALL MOD_EQ_IMP_MULT)); print "\n");
val _ = print ("MOD_EQ_IMP_MULT_proved=" ^ term_to_string (rhs (concl (EQT_INTRO MOD_EQ_IMP_MULT))) ^ "\n");
val _ = print ("MOD_EQ_IMP_MULT_hypotheses=" ^ Int.toString (length (hyp MOD_EQ_IMP_MULT)) ^ "\n");

val star_move_lemma = prove(
  ``p0 * p1 * p1' * p2 * p3 * p4 = p2 * (p1 * p1' * STAR p3 (p4 * p0))``,
  fs [AC STAR_COMM STAR_ASSOC]);
val _ = (print "star_move_lemma_statement="; print_term (concl (GEN_ALL star_move_lemma)); print "\n");
val _ = print ("star_move_lemma_proved=" ^ term_to_string (rhs (concl (EQT_INTRO star_move_lemma))) ^ "\n");
val _ = print ("star_move_lemma_hypotheses=" ^ Int.toString (length (hyp star_move_lemma)) ^ "\n");

(* Local prerequisite 2756-2768 and original 2776-2803, replayed unchanged. *)
val IN_addresses = prove(
  ``!n a x. x IN addresses a n <=>
            ?i. i < n /\ x = a + n2w i * bytes_in_word``,
  Induct \\ fs [addresses_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i`
         \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ metis_tac []);
val memory_addresses = prove(
  ``!n (a:'a word) (m:'a word -> 'a word_loc).
      n * (dimindex (:'a) DIV 8) < dimword (:'a) /\ good_dimindex (:'a) ==>
      memory m (addresses a n) = word_list a (read_mem a m n)``,
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ fs [addresses_def,read_mem_def,word_list_def]
  THEN1 (fs [memory_def,FUN_EQ_THM,fun2set_def,emp_def])
  \\ simp [memory_def,Once FUN_EQ_THM,one_STAR]
  \\ rw []
  \\ fs [MULT_CLAUSES]
  \\ `n * (dimindex (:α) DIV 8) < dimword (:α)` by decide_tac
  \\ res_tac \\ fs []
  \\ fs [fun2set_def,memory_def]
  \\ fs [EXTENSION,FORALL_PROD]
  \\ fs [IN_addresses]
  \\ eq_tac \\ fs [] \\ strip_tac \\ fs [] THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ fs []
  \\ rw [] \\ fs []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL,
       bytes_in_word_def,word_add_n2w,word_mul_n2w]
  \\ sg `i * (dimindex (:α) DIV 8) + dimindex (:α) DIV 8 < dimword (:α)`
  \\ fs[]
  \\ fs [good_dimindex_def,dimword_def]
  \\ fs [good_dimindex_def,dimword_def]);
val _ = (print "memory_addresses_statement="; print_term (concl (GEN_ALL memory_addresses)); print "\n");
val _ = print ("memory_addresses_proved=" ^ term_to_string (rhs (concl (EQT_INTRO memory_addresses))) ^ "\n");
val _ = print ("memory_addresses_hypotheses=" ^ Int.toString (length (hyp memory_addresses)) ^ "\n");

(* Exported originals 4100-4157, stored theorems printed in full. *)
val _ = (print "make_init_any_bitmaps_statement="; print_term (concl (GEN_ALL make_init_any_bitmaps)); print "\n");
val _ = print ("make_init_any_bitmaps_hypotheses=" ^ Int.toString (length (hyp make_init_any_bitmaps)) ^ "\n");
val _ = (print "make_init_any_use_stack_statement="; print_term (concl (GEN_ALL make_init_any_use_stack)); print "\n");
val _ = print ("make_init_any_use_stack_hypotheses=" ^ Int.toString (length (hyp make_init_any_use_stack)) ^ "\n");
val _ = (print "make_init_any_use_store_statement="; print_term (concl (GEN_ALL make_init_any_use_store)); print "\n");
val _ = print ("make_init_any_use_store_hypotheses=" ^ Int.toString (length (hyp make_init_any_use_store)) ^ "\n");
val _ = (print "make_init_any_use_alloc_statement="; print_term (concl (GEN_ALL make_init_any_use_alloc)); print "\n");
val _ = print ("make_init_any_use_alloc_hypotheses=" ^ Int.toString (length (hyp make_init_any_use_alloc)) ^ "\n");
val _ = (print "make_init_any_code_statement="; print_term (concl (GEN_ALL make_init_any_code)); print "\n");
val _ = print ("make_init_any_code_hypotheses=" ^ Int.toString (length (hyp make_init_any_code)) ^ "\n");
val _ = (print "make_init_any_stack_limit_statement="; print_term (concl (GEN_ALL make_init_any_stack_limit)); print "\n");
val _ = print ("make_init_any_stack_limit_hypotheses=" ^ Int.toString (length (hyp make_init_any_stack_limit)) ^ "\n");
val _ = (print "make_init_any_compile_oracle_statement="; print_term (concl (GEN_ALL make_init_any_compile_oracle)); print "\n");
val _ = print ("make_init_any_compile_oracle_hypotheses=" ^ Int.toString (length (hyp make_init_any_compile_oracle)) ^ "\n");
