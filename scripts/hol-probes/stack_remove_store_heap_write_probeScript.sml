load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val assoc_lem = prove(``(A:(('a -> bool) -> bool) * B) * C = (B * C) * A``,
  metis_tac [STAR_ASSOC,STAR_COMM]);
val write_fun2set2 = write_fun2set |> SIMP_RULE std_ss [GSYM STAR_COMM];
val st = GEN_ALL (prove(``  MEM name store_list ∧
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
        word_list c s.stack) (fun2set (m,d)) ⇒
  (memory s.memory s.mdomain *
      word_list
        (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
        (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
      word_list_exists
        (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α) +
         bytes_in_word *
         n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
        s.data_buffer.space_left * word_store c (s.store |+ (name,x)) *
      word_list c s.stack) (fun2set ((c + store_offset name =+ x) m,d))
``,
  strip_tac>>
  pop_assum mp_tac>>
  qmatch_goalsub_abbrev_tac`A * B * C`>>
  `A * B * C = B * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qmatch_goalsub_abbrev_tac`A * B' * C`>>
  `A * B' * C = B' * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qabbrev_tac`Z = (A*C)`>>
  fs[Abbr`B`,Abbr`B'`]>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
      ,word_store_def,GSYM word_mul_n2w, store_list_def
      ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC)
  >>
  (* ntac 42 *) rpt (
  qpat_x_assum` _ (fun2set _)` mp_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC))>>
  fs[store_list_def]
));
val _ = print("st_statement=" ^ term_to_string(concl st) ^ "\n");
val _ = print("st_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl st)))) ^ "\n");
val _ = print("st_proved=" ^ term_to_string(rhs(concl(EQT_INTRO st))) ^ "\n");
