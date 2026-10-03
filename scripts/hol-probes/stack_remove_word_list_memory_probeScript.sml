load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory set_sepTheory
 miscTheory wordsTheory listTheory addressTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;

(* stack_removeProofScript.sml:2631-2634 *)
val _ = (print "mem_val_def_statement="; print_term (concl mem_val_def); print "\n");
val _ = print ("mem_val_def_type=" ^ type_to_string (type_of ``mem_val``) ^ "\n");

(* 2811-2815 *)
val MAP_mem_val_MAP_INL = prove(
  ``!ws f. MAP (mem_val f) (MAP INL ws) = MAP Word ws``,
  Induct \\ fs [mem_val_def]);
val _ = (print "MAP_mem_val_MAP_INL_statement="; print_term (concl (GEN_ALL MAP_mem_val_MAP_INL)); print "\n");
val _ = print ("MAP_mem_val_MAP_INL_proved=" ^ term_to_string (rhs (concl (EQT_INTRO MAP_mem_val_MAP_INL))) ^ "\n");
val _ = print ("MAP_mem_val_MAP_INL_hypotheses=" ^ Int.toString (length (hyp MAP_mem_val_MAP_INL)) ^ "\n");

(* 2827-2835 *)
val word_list_and_rev_join_lemma = prove(
  ``(b = a + n2w (LENGTH xs + LENGTH ys) * bytes_in_word) /\
    (p * word_list a (xs ++ REVERSE ys) * q) ss /\ b1 ==>
    (p * word_list a xs * word_list_rev b ys * q) ss /\ b1``,
  fs [word_list_APPEND,WORD_LEFT_ADD_DISTRIB]
  \\ fs [word_list_EQ_rev] \\ rw []
  \\ fs [AC STAR_COMM STAR_ASSOC,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);
val _ = (print "word_list_and_rev_join_lemma_statement="; print_term (concl (GEN_ALL word_list_and_rev_join_lemma)); print "\n");
val _ = print ("word_list_and_rev_join_lemma_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_and_rev_join_lemma))) ^ "\n");
val _ = print ("word_list_and_rev_join_lemma_hypotheses=" ^ Int.toString (length (hyp word_list_and_rev_join_lemma)) ^ "\n");

(* 2846-2850 *)
val INSERT_DELETE_EQ_DELETE = prove(
  ``(x INSERT s) DELETE x = s DELETE x``,
  fs [EXTENSION] \\ metis_tac []);
val _ = (print "INSERT_DELETE_EQ_DELETE_statement="; print_term (concl (GEN_ALL INSERT_DELETE_EQ_DELETE)); print "\n");
val _ = print ("INSERT_DELETE_EQ_DELETE_proved=" ^ term_to_string (rhs (concl (EQT_INTRO INSERT_DELETE_EQ_DELETE))) ^ "\n");
val _ = print ("INSERT_DELETE_EQ_DELETE_hypotheses=" ^ Int.toString (length (hyp INSERT_DELETE_EQ_DELETE)) ^ "\n");

(* Local original prerequisite 2756-2768, replayed unchanged. *)
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

(* 2852-2871 *)
val word_list_exists_addresses_replay = prove(
  ``!n a. (dimindex(:'a) DIV 8) * n < dimword (:'a) /\
          good_dimindex (:'a) ==>
          word_list_exists a n (fun2set (m1,addresses (a:'a word) n))``,
  Induct
  THEN1 (fs [word_list_exists_thm,fun2set_def,emp_def,addresses_def])
  \\ fs [word_list_exists_thm,emp_def,addresses_def,INSERT_DELETE_EQ_DELETE,
         SEP_EXISTS_THM,MULT_CLAUSES,set_sepTheory.one_fun2set]
  \\ rw [] \\ imp_res_tac (DECIDE ``m+n<k:num ==> m < k``) \\ res_tac
  \\ sg `addresses (a + bytes_in_word) n DELETE a =
      addresses (a + bytes_in_word) n` \\ fs []
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ fs []
  \\ fs [IN_addresses,PULL_EXISTS]
  \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ sg `(i * (dimindex (:'a) DIV 8) + dimindex (:'a) DIV 8)
      < dimword (:'a)` \\ fs []
  \\ fs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs []);
val _ = (print "word_list_exists_addresses_statement="; print_term (concl (GEN_ALL word_list_exists_addresses_replay)); print "\n");
val _ = print ("word_list_exists_addresses_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_exists_addresses_replay))) ^ "\n");
val _ = print ("word_list_exists_addresses_hypotheses=" ^ Int.toString (length (hyp word_list_exists_addresses_replay)) ^ "\n");

(* 2995-3015 *)
val word_list_wrap_replay = prove(
  ``good_dimindex (:'a) ∧
  dimword(:'a) DIV (dimindex(:'a) DIV 8) < LENGTH ls ⇒
  ∃x xs y ys b.
  word_list (a:'a word) ls = word_list a (x::xs) * word_list b (y::ys)  ∧
  b = a``,
  rw[]>>
  `∃r.r < LENGTH ls ∧ 0 < r ∧ a + bytes_in_word * n2w r = a` by
    (fs[addressTheory.WORD_EQ_ADD_CANCEL,bytes_in_word_def,word_mul_n2w]>>
    `0 <dimword(:'a)` by fs[good_dimindex_def] >>
    old_drule (GEN_ALL MOD_EQ_0_DIVISOR)>>fs[]>>disch_then kall_tac>>
    fs[good_dimindex_def,dimword_def,PULL_EXISTS]>>rfs[]>>
    asm_exists_tac>>fs[])>>
  Q.ISPECL_THEN [`TAKE r ls`,`DROP r ls`,`a`] assume_tac word_list_APPEND>>
  fs[]>>
  `0 < LENGTH (DROP r ls)` by fs[]>>
  Cases_on`DROP r ls`>>fs[]>>
  Cases_on`ls`>>fs[]>>
  metis_tac[]);
val _ = (print "word_list_wrap_statement="; print_term (concl (GEN_ALL word_list_wrap_replay)); print "\n");
val _ = print ("word_list_wrap_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_wrap_replay))) ^ "\n");
val _ = print ("word_list_wrap_hypotheses=" ^ Int.toString (length (hyp word_list_wrap_replay)) ^ "\n");

(* 3041-3046 *)
val fmap_simp_lemma1 = prove(
  ``g |+ (0n,x) |+ (5,y) |+ (0,z) = g |+ (0,z) |+ (5,y)``,
  fs [fmap_EXT] \\ rw [] \\ fs [EXTENSION,FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [] \\ metis_tac []);
val _ = (print "fmap_simp_lemma1_statement="; print_term (concl (GEN_ALL fmap_simp_lemma1)); print "\n");
val _ = print ("fmap_simp_lemma1_proved=" ^ term_to_string (rhs (concl (EQT_INTRO fmap_simp_lemma1))) ^ "\n");
val _ = print ("fmap_simp_lemma1_hypotheses=" ^ Int.toString (length (hyp fmap_simp_lemma1)) ^ "\n");

(* 3101-3164, 3166-3178, 3180-3199, 3201-3222: exported theorems, checked
   against the stored theory and printed in full. *)
val _ = (print "word_list_set_statement="; print_term (concl (GEN_ALL word_list_set)); print "\n");
val _ = print ("word_list_set_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_set))) ^ "\n");
val _ = print ("word_list_set_hypotheses=" ^ Int.toString (length (hyp word_list_set)) ^ "\n");
val _ = (print "word_list_seteq_statement="; print_term (concl (GEN_ALL word_list_seteq)); print "\n");
val _ = print ("word_list_seteq_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_seteq))) ^ "\n");
val _ = print ("word_list_seteq_hypotheses=" ^ Int.toString (length (hyp word_list_seteq)) ^ "\n");
val _ = (print "word_list_EL_in_memory_statement="; print_term (concl (GEN_ALL word_list_EL_in_memory)); print "\n");
val _ = print ("word_list_EL_in_memory_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_EL_in_memory))) ^ "\n");
val _ = print ("word_list_EL_in_memory_hypotheses=" ^ Int.toString (length (hyp word_list_EL_in_memory)) ^ "\n");
val _ = (print "word_list_in_memory_statement="; print_term (concl (GEN_ALL word_list_in_memory)); print "\n");
val _ = print ("word_list_in_memory_proved=" ^ term_to_string (rhs (concl (EQT_INTRO word_list_in_memory))) ^ "\n");
val _ = print ("word_list_in_memory_hypotheses=" ^ Int.toString (length (hyp word_list_in_memory)) ^ "\n");
val _ = print ("word_list_exists_addresses_matches_theory=" ^
  (if aconv (concl word_list_exists_addresses_replay) (concl word_list_exists_addresses)
   then "T" else "F") ^ "\n");
val _ = print ("word_list_wrap_matches_theory=" ^
  (if aconv (concl word_list_wrap_replay) (concl word_list_wrap) then "T" else "F") ^ "\n");
