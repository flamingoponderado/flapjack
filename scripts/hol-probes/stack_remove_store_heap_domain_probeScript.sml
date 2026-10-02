load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val sd = prove(``  MEM name store_list ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
        word_list_exists
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪
           word_shift (:α) +
           bytes_in_word *
           n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
          s.data_buffer.space_left * word_store c s.store *
        word_list c s.stack) (fun2set (t1.memory,(t1:('a,'c,'b) stackSem$state).mdomain)) ⇒
  c+store_offset name ∈ t1.mdomain
``,
  strip_tac >>
  old_drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  old_drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  pop_assum mp_tac>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  (* ntac 47 *) rpt (
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac>>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def]
);
val _ = print("sd_statement=" ^ term_to_string(concl sd) ^ "\n");
val _ = print("sd_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (free_vars(concl sd))) ^ "\n");
val _ = print("sd_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sd))) ^ "\n");
