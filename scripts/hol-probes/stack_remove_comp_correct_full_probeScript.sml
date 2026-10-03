load "preamble";
load "helperLib";
open helperLib;
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory byteTheory miscTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory semanticsPropsTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val word_shift_def = backend_commonTheory.word_shift_def;
val _ = overload_on ("num_stubs", ``stack_num_stubs``);
val state_rel_get_var = prove(``  state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]);
val state_rel_IMP = prove(``  state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]);
val state_rel_with_clock = prove(``  state_rel jump off k s t1 ==>
    state_rel jump off k (s with clock := c) (t1 with clock := c)``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]);
val find_code_lemma = prove(``  state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest s.regs s.code = SOME x ==>
    find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k``,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);
val find_code_lemma2 = prove(``  state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest (s.regs \\ x1) s.code = SOME x ==>
    find_code dest (t1.regs \\ x1) t1.code = SOME (comp jump off k x) /\ reg_bound x k``,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ fs[DOMSUB_FLOOKUP_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);
val word_store_CurrHeap = prove(``  word_store base (s.store |+ (CurrHeap,x)) = word_store base s.store``,
  full_simp_tac(srw_ss())[word_store_def,store_list_def,FLOOKUP_UPDATE]);
val memory_fun2set_IMP_read = prove(``  (memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
    a IN d1 /\ m1 a = m a``,
  simp [Once STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS]);
val state_rel_read = prove(``  state_rel jump off k s t /\ a IN s.mdomain ==>
    a IN t.mdomain /\ (t.memory a = s.memory a)``,
  full_simp_tac(srw_ss())[state_rel_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC] \\ metis_tac [memory_fun2set_IMP_read]);
val mem_load_32_IMP = prove(``  state_rel jump off k s t /\
    mem_load_32 s.memory s.mdomain s.be a = SOME x ==>
    mem_load_32 t.memory t.mdomain t.be a = SOME x``,
   full_simp_tac(srw_ss())[wordSemTheory.mem_load_32_alt] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ ntac 5 (FULL_CASE_TAC >> fs[]) >> gvs[]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val mem_load_byte_aux_IMP = prove(``  state_rel jump off k s t /\
    mem_load_byte_aux s.memory s.mdomain s.be a = SOME x ==>
    mem_load_byte_aux t.memory t.mdomain t.be a = SOME x``,
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val read_bytearray_IMP_read_bytearray = prove(``  !n a k s t x.
      state_rel jump off k s t /\
      read_bytearray a n (mem_load_byte_aux s.memory s.mdomain s.be) = SOME x ==>
      read_bytearray a n (mem_load_byte_aux t.memory t.mdomain t.be) = SOME x``,
  Induct \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac mem_load_byte_aux_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val write_bytearray_IGNORE_non_aligned = prove(``  !new_bytes a.
      (!x. b <> byte_align x) ==>
      write_bytearray a new_bytes m d be b = m b``,
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]);
val write_bytearray_IGNORE = prove(``  !new_bytes a x xx.
      d1 SUBSET d /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x /\ xx ∉ d1 ==>
      write_bytearray a new_bytes m d be xx = m xx``,
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ rpt gen_tac \\ every_case_tac
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val write_bytearray_EQ = prove(``  !new_bytes a m1 m y x.
      d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME y /\ m1 x = m x ==>
      write_bytearray a new_bytes m1 d1 be x =
      write_bytearray a new_bytes m d be x``,
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ rpt gen_tac \\ ntac 2 BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ Cases_on `m1 (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ `byte_align a IN d` by full_simp_tac(srw_ss())[SUBSET_DEF] \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xx ==> yy` mp_tac \\ impl_tac THEN1 (metis_tac [])
  \\ srw_tac[][]
  \\ `write_bytearray (a + 1w) new_bytes m1 d1 be (byte_align a) =
      write_bytearray (a + 1w) new_bytes m d be (byte_align a)` by
    (first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][]);
val write_bytearray_lemma = prove(``  !new_bytes a m1 d1 be x p m d.
      (memory m1 d1 * p) (fun2set (m,d)) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x ==>
      (memory (write_bytearray a new_bytes m1 d1 be) d1 * p)
        (fun2set (write_bytearray a new_bytes m d be,d))``,
  simp [STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS] \\ srw_tac[][]
  \\ `d1 SUBSET d` by full_simp_tac(srw_ss())[SUBSET_DEF]
  THEN1 (res_tac \\ full_simp_tac(srw_ss())[] \\ imp_res_tac write_bytearray_EQ \\ full_simp_tac(srw_ss())[])
  \\ qpat_x_assum `p xx` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x=y)==>x==>y``) \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[EXTENSION] \\ srw_tac[][] \\ EQ_TAC \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `xx IN d`
  \\ Cases_on `xx IN d1` \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_IGNORE \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_EQ \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ metis_tac []);
val state_rel_get_fp_var = prove(``  state_rel jump off k s t ⇒
  get_fp_var n s = get_fp_var n t``,
  fs[state_rel_def,get_fp_var_def]);
val state_rel_set_fp_var = prove(``  state_rel jump off k s t ⇒
  state_rel jump off k (set_fp_var n v s) (set_fp_var n v t)``,
  rw[state_rel_def,set_fp_var_def]>>rfs[]>>
  res_tac >> fs[]);
val get_labels_stack_free = prove(``  !k n. get_labels (stack_free k n) = {}``,
  recInduct stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_free_def] \\ rw []
  \\ fs [get_labels_def,single_stack_free_def]);
val get_labels_stack_alloc = prove(``  !jump k n. get_labels (stack_alloc jump k n) = {}``,
  recInduct stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_alloc_def] \\ rw []
  \\ fs [get_labels_def,single_stack_alloc_def]
  \\ IF_CASES_TAC \\ fs[get_labels_def,halt_inst_def]);
val get_labels_upshift = prove(``  !n n0. get_labels (upshift n n0) = {}``,
  recInduct upshift_ind \\ rw []
  \\ once_rewrite_tac [upshift_def] \\ rw []
  \\ fs [get_labels_def]);
val get_labels_downshift = prove(``  !n n0. get_labels (downshift n n0) = {}``,
  recInduct downshift_ind \\ rw []
  \\ once_rewrite_tac [downshift_def] \\ rw []
  \\ fs [get_labels_def]);
val evaluate_upshift = prove(``  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(upshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w + word_offset n)))``,
  ho_match_mp_tac upshift_ind>>rw[]>>
  simp[Once upshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w+word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]);
val evaluate_downshift = prove(``  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(downshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w - word_offset n)))``,
  ho_match_mp_tac downshift_ind>>rw[]>>
  simp[Once downshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w - 1w * word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  simp[]>>
  FULL_SIMP_TAC std_ss [GSYM WORD_LEFT_ADD_DISTRIB]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]);
val name_cases = prove(``    !name. name <> CurrHeap ==> MEM name store_list``,
  Cases_on `name` \\ fs [store_list_def]
  \\ CCONTR_TAC \\ fs [] \\ Cases_on `c`
  \\ full_simp_tac std_ss [n2w_11,EVAL ``dimword (:5)``]
  \\ ntac 16 (Cases_on `n` \\ full_simp_tac std_ss [ADD1]
              \\ Cases_on `n'` \\ full_simp_tac std_ss [ADD1,GSYM ADD_ASSOC])
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac) \\ decide_tac);
val mem_load_lemma = prove(``  MEM name store_list ∧
  FLOOKUP (s:('a,'c,'b)stackSem$state).store name = SOME x ∧
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
  mem_load (c+store_offset name) t1 = SOME x``,
  strip_tac >>
  old_drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  old_drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  ntac 2 (pop_assum mp_tac)>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  strip_tac>>
  (* ntac 47 *) rpt (
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac
  >-
    simp[Abbr`P`,Abbr`Q`,mem_load_def]
  >>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def]);
val mem_load_lemma2 = prove(``  MEM name store_list ∧
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
  c+store_offset name ∈ t1.mdomain``,
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
  fs[store_list_def]);
val write_fun2set2 = write_fun2set |> SIMP_RULE std_ss [GSYM STAR_COMM];
val assoc_lem = prove(``  (A:(('a -> bool) -> bool) * B) * C =
  (B * C) * A``,
  metis_tac[STAR_ASSOC,STAR_COMM]);
val store_write_lemma = prove(``  MEM name store_list ∧
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
      word_list c s.stack) (fun2set ((c + store_offset name =+ x) m,d))``,
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
  fs[store_list_def]);
val cc_full = prove(``  !p s1 r s2 t1 k off jump.
     evaluate (p,s1) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s1 t1 /\ reg_bound p k ==>
     ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2))``,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def] \\ rpt var_eq_tac
    \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[])
  THEN1 (* Halt *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0`
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (* Alloc *)
   (fs [comp_def,evaluate_def] \\ fs [state_rel_def])
  THEN1 (* StoreConsts *)
   (fs [comp_def]
    \\ ‘¬s.use_alloc’ by fs [state_rel_def]
    \\ gvs [stackSemTheory.evaluate_def,list_Seq_def,AllCaseEqs()]
    \\ full_simp_tac(srw_ss())[reg_bound_def,GSYM NOT_LESS] \\ srw_tac[][]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def] \\ Cases_on `x`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def])
    \\ `inst (Mem Load t2 (Addr (k + 1) (store_offset BitmapBase))) t1' =
          SOME (set_var t2 (Word ww) t1')` by
     (qpat_x_assum `state_rel jump off k s t1'` mp_tac
      \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
      \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c + store_offset BitmapBase) t1' = SOME (Word ww)` by
        (match_mp_tac (GEN_ALL mem_load_lemma)>>fs[store_list_def]>>
          asm_exists_tac>> simp[])
      \\ simp[])
    \\ fs [] \\ pop_assum kall_tac
    \\ fs [inst_def,assign_def,word_exp_def,set_var_def,FLOOKUP_UPDATE]
    \\ gvs [store_const_sem_def,AllCaseEqs(),get_var_def]
    \\ ‘FLOOKUP t1'.regs 3 = SOME (Word off') ∧
        FLOOKUP t1'.regs 2 = SOME (Word a) ∧
        FLOOKUP t1'.regs 1 = SOME (Word i)’ by (rpt strip_tac \\ fs [state_rel_def])
    \\ ‘shift (:α) < dimindex (:α)’ by
       fs [state_rel_def,good_dimindex_def,backend_commonTheory.word_shift_def]
    \\ `shift (:'a) MOD dimword (:'a) = shift (:'a)` by
       fs [state_rel_def,good_dimindex_def,backend_commonTheory.word_shift_def,dimword_def]
    \\ fs [wordLangTheory.word_sh_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]
    \\ qpat_x_assum ‘state_rel jump off k s _’ mp_tac
    \\ rename [‘state_rel jump off k s t6’]
    \\ simp [Once state_rel_def]
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs [the_SOME_Word_def]
    \\ strip_tac
    \\ qabbrev_tac ‘r2 = t6.regs |+ (t2,Word (i ≪ shift (:α) + ww ≪ shift (:α)))’
    \\ old_drule (GEN_ALL copy_loop_thm) \\ fs []
    \\ disch_then (qspecl_then [‘t2’,‘t1’] mp_tac) \\ fs []
    \\ fs [word_list_APPEND]
    \\ qpat_x_assum ‘_ (fun2set _)’ mp_tac
    \\ fs [GSYM STAR_ASSOC]
    \\ qmatch_goalsub_abbrev_tac ‘(_ * (_ * rest)) (fun2set _)’
    \\ fs [lsl_word_shift]
    \\ strip_tac
    \\ disch_then (qspecl_then [‘rest’,‘ww * bytes_in_word’,‘t6 with regs := r2’] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
      \\ gvs [lsl_word_shift]
      \\ imp_res_tac memory_fun2set_SUBSET
      \\ fs [AC STAR_COMM STAR_ASSOC])
    \\ strip_tac \\ qexists_tac ‘ck’ \\ gvs []
    \\ Cases_on ‘b’ \\ fs [FLOOKUP_UPDATE]
    \\ fs [state_rel_def,set_var_def,FLOOKUP_UPDATE,Abbr‘r2’,the_SOME_Word_def]
    \\ fs [word_list_APPEND]
    \\ gvs [lsl_word_shift,Abbr‘rest’,AC STAR_COMM STAR_ASSOC]
    \\ rw [] \\ res_tac \\ fs [])
  THEN1 (* Inst *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ old_drule (GEN_ALL state_rel_inst)
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ disch_then old_drule
    \\ disch_then old_drule
    \\ strip_tac
    \\ simp[]
    \\ imp_res_tac inst_const
    \\ qexists_tac`0` \\ simp[]
    \\ metis_tac[with_same_clock])
  THEN1 (* Get *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF]
    THEN1 (`FLOOKUP t1.regs (k + 2) = SOME x` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def]
    \\ `mem_load (c + store_offset name) t1 = SOME x` by
     (old_drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma])
    \\ fs[] \\ res_tac
    \\ fs[] \\ match_mp_tac state_rel_set_var
    \\ fs[state_rel_def]
    \\ metis_tac[])
  THEN1 (* Set *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF,get_var_def]
    THEN1 (
      fs[state_rel_def,set_var_def,set_store_def,FLOOKUP_UPDATE] \\
      rfs[] \\ fs[] \\ fs[word_store_def,word_store_CurrHeap] \\
      metis_tac[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ fs[wordLangTheory.word_op_def,mem_store_def]
    \\ `c + store_offset name IN t1.mdomain` by
     (old_drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma2])
    \\ fs[]
    \\ fs[state_rel_def,set_store_def,FLOOKUP_UPDATE]
    \\ rfs[]
    \\ conj_tac >- metis_tac[]
    \\ full_simp_tac(srw_ss())[AC MULT_COMM MULT_ASSOC]
    \\ Q.ABBREV_TAC `m = t1.memory`
    \\ Q.ABBREV_TAC `d = t1.mdomain`
    \\ old_drule name_cases
    \\ metis_tac[store_write_lemma])
  THEN1 (* OpCurrHeap *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ gvs [AllCaseEqs(),word_exp_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ fs [inst_def,assign_def,word_exp_def]
    \\ gvs [AllCaseEqs(),word_exp_def,PULL_EXISTS]
    \\ rename [‘FLOOKUP s.regs src = SOME (Word c1)’]
    \\ rename [‘FLOOKUP s.store CurrHeap = SOME (Word c2)’]
    \\ qsuff_tac ‘FLOOKUP t1.regs src = SOME (Word c1) ∧
                  FLOOKUP t1.regs (k + 2) = SOME (Word c2)’ THEN1 fs []
    \\ fs [state_rel_def])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ `s.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac state_rel_IMP \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def,LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `res = NONE`) \\ full_simp_tac(srw_ss())[]
    >- (rpt var_eq_tac
      \\ first_x_assum old_drule >> simp[]
      \\ strip_tac >> full_simp_tac(srw_ss())[]
      \\ pop_assum mp_tac >> CASE_TAC
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ qexists_tac`ck`\\simp[])
    \\ first_x_assum old_drule >> simp[] >> strip_tac
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ ntac 2 (pop_assum mp_tac)
    \\ old_drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck'`mp_tac)
    \\ simp[] \\ ntac 3 strip_tac
    \\ qexists_tac`ck+ck'`\\simp[])
  THEN1 (* Return *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  >~ [‘Break’] >-
   (gvs [comp_def,evaluate_def] \\ gvs [state_rel_def,SF SFY_ss])
  >~ [‘Continue’] >-
   (gvs [comp_def,evaluate_def] \\ gvs [state_rel_def,SF SFY_ss])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[])
  >~ [‘Loop’] >-
   (simp [Once comp_def]
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [Once evaluate_def,get_var_def]
    \\ pairarg_tac \\ gvs []
    \\ reverse IF_CASES_TAC
    >-
     (gvs [] \\ strip_tac \\ gvs []
      \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
      \\ first_x_assum drule_all
      \\ strip_tac \\ simp [Once evaluate_def]
      \\ qexists ‘ck’ \\ simp []
      \\ Cases_on ‘res’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ rw [] \\ gvs [])
    \\ IF_CASES_TAC
    >-
     (gvs [] \\ strip_tac \\ gvs []
      \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
      \\ first_x_assum drule_all
      \\ strip_tac \\ simp [Once evaluate_def]
      \\ qexists ‘ck’ \\ simp []
      \\ Cases_on ‘res’ \\ gvs [] \\ gvs [state_rel_def]
      \\ Cases_on ‘x’ \\ gvs [state_rel_def])
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
    \\ first_x_assum drule_all \\ strip_tac
    \\ ‘state_rel jump off k s1 t2’ by (imp_res_tac cont_loop_IMP \\ gvs [])
    \\ ‘state_rel jump off k (dec_clock s1) (dec_clock t2)’ by
     (pop_assum mp_tac \\ simp [state_rel_def,dec_clock_def,SF SFY_ss]
      \\ rw [] \\ gvs [])
    \\ gvs [STOP_def,reg_bound_def]
    \\ first_x_assum drule_all
    \\ strip_tac \\ fs [dec_clock_def]
    \\ simp [Once evaluate_def]
    \\ qpat_x_assum ‘evaluate _ = (res,t2)’ assume_tac
    \\ ‘res ≠ SOME TimeOut’ by (CCONTR_TAC \\ gvs [])
    \\ drule_all evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ ‘t2.clock ≠ 0’ by gvs [state_rel_def]
    \\ qexists_tac ‘ck+ck'’ \\ gvs []
    \\ gvs [STOP_def,dec_clock_def]
    \\ qpat_x_assum ‘evaluate (comp _ _ _ (Loop _), _) = _’ mp_tac
    \\ simp [Once comp_def])
  THEN1 (* JumpLower *)
   (simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[find_code_def]
    \\ Cases_on `get_var r1 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_var r2 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `word_cmp Lower c c'`) \\ full_simp_tac(srw_ss())[] THEN1 (
      srw_tac[][] \\ qexists_tac`0`\\simp[])
    \\ Cases_on `lookup dest s.code` \\ full_simp_tac(srw_ss())[]
    \\ `lookup dest t1.code = SOME (comp jump off k x) /\
        reg_bound x k /\ s.clock = t1.clock` by
     (qpat_x_assum `bb ==> bbb` (K all_tac)
      \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `t1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (srw_tac[][] \\ qexists_tac`t1.clock` \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
    \\ split_pair_case_tac \\ gvs[CaseEq"bool"]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac`ck`
    \\ fsrw_tac[ARITH_ss][get_var_def,dec_clock_def]
    \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[])
  THEN1 (* RawCall *)
   (simp [Once comp_def]
    \\ fs [evaluate_def,CaseEq"option",PULL_EXISTS]
    \\ old_drule (GEN_ALL (find_code_lemma |> Q.INST [`dest`|->`INL d`]))
    \\ fs [find_code_def]
    \\ disch_then old_drule \\ strip_tac \\ fs []
    \\ Cases_on `prog` \\ fs [dest_Seq_def] \\ rveq \\ fs []
    \\ once_rewrite_tac [comp_def] \\ fs [dest_Seq_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def]
    \\ fs [CaseEq"bool",pair_case_eq,CaseEq"option"] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ fs [] \\ fs [state_rel_def])
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
          (fs [state_rel_def,dec_clock_def] \\ metis_tac [])
    \\ first_x_assum old_drule \\ fs [dec_clock_def]
    \\ disch_then match_mp_tac
    \\ pop_assum kall_tac
    \\ fs [state_rel_def]
    \\ res_tac \\ fs [reg_bound_def])
  THEN1 (* Call *)
   (Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[evaluate_def]
      \\ Cases_on `find_code dest s.regs s.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] THEN1
       (qexists_tac`0`
        \\ full_simp_tac(srw_ss())[evaluate_def,Once comp_def,reg_bound_def]
        \\ imp_res_tac find_code_lemma \\ full_simp_tac(srw_ss())[] \\ pop_assum (K all_tac)
        \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
      \\ Cases_on `evaluate (x,dec_clock s)` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `bad_fun_return q` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ simp [evaluate_def,Once comp_def,reg_bound_def]
      \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ `find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k` by
           (match_mp_tac find_code_lemma \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ `t1.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
       (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ rev_full_simp_tac(srw_ss())[] \\ metis_tac [])
      \\ first_x_assum old_drule \\ full_simp_tac(srw_ss())[]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac`ck`
      \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def])
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ simp[Once comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[Once evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL find_code_lemma2)
    \\ disch_then old_drule
    \\ disch_then old_drule
    \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ qexists_tac`0`\\simp[]
      \\ `t1.clock = 0` by fs[state_rel_def]
      \\ simp[] \\ fs[state_rel_def] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[Once evaluate_def]
    \\ `t1.clock = s.clock` by fs[state_rel_def]
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_rename_tac`_ = (SOME res,_)`
    \\ Cases_on`res = TimeOut` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃w. res = Halt w` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃l. res = Result l` \\ fs[]
    >- (
      BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
      \\ qabbrev_tac`ss = dec_clock sss`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule \\ simp[] \\ strip_tac
      \\ first_x_assum old_drule \\ simp[] \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
      \\ old_drule (GEN_ALL evaluate_add_clock)
      \\ disch_then(qspec_then`ck2`mp_tac)
      \\ simp[] \\ ntac 2 strip_tac
      \\ qexists_tac`ck' + ck2` \\  simp[] )
    \\ Cases_on`∃f. res = FinalFFI f` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[] \\ rfs[]
    \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
    \\ qabbrev_tac`ss = dec_clock sss`
    \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
    >- (
      simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
      \\ match_mp_tac state_rel_with_clock
      \\ match_mp_tac state_rel_set_var
      \\ simp[] )
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ fs[dec_clock_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
    \\ old_drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck2`mp_tac)
    \\ simp[] \\ ntac 2 strip_tac
    \\ qexists_tac`ck' + ck2` \\  simp[] )
  THEN1 ( (* Install *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def]
    \\ ntac 8 (TOP_CASE_TAC \\ fs[])
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rveq
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rewrite_tac[GSYM MAP]
    \\ qmatch_goalsub_abbrev_tac`fromAList code`
    \\ simp[prog_comp_eta]
    \\ TOP_CASE_TAC \\ fs[]
    \\ simp[shift_seq_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ conj_tac >- (
      simp[FUN_EQ_THM,prog_comp_eta] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      simp[FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] )
    \\ conj_tac >- (
      qhdtm_x_assum`code_rel`mp_tac \\
      simp[code_rel_def,lookup_union,lookup_fromAList] \\
      strip_tac >>
      conj_tac>-(
        ntac 2 strip_tac \\
        reverse TOP_CASE_TAC >- (
          strip_tac  \\ rveq \\
          res_tac \\ simp[] ) \\
        strip_tac \\ imp_res_tac ALOOKUP_MEM \\
        simp[ALOOKUP_MAP_2] \\
        last_x_assum(qspec_then`0` mp_tac)>>simp[]>>
        disch_then old_drule>>strip_tac>>simp[]>>
        CASE_TAC>>fs[EXTENSION,domain_lookup,PULL_EXISTS]>>
        first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
        fs[backend_commonTheory.stack_num_stubs_def])>>
     simp[domain_union,domain_fromAList,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]>>
     metis_tac[UNION_COMM,UNION_ASSOC])
    \\ conj_tac >- simp[lookup_union]
    \\ conj_tac >- (
      simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] \\
      rfs[] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      fs[wordSemTheory.buffer_flush_def]
      \\ rveq \\ fs[GSYM bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w] )
    \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ conj_tac >- metis_tac[]
    \\ fs[wordSemTheory.buffer_flush_def]
    \\ rveq \\ fs[])
  THEN1 ( (* ShMemOp *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def,word_exp_def,IS_SOME_EXISTS,
         wordLangTheory.word_op_def]>>
    ntac 2 (FULL_CASE_TAC>>fs[])
    \\ fs[CaseEq"bool"]
    >- (imp_res_tac state_rel_IMP>>
        gvs[empty_env_def,state_rel_def]>>
        TRY (qexists_tac`0`)>>gvs[])>>
    qexists_tac ‘0’>>gs[]>>
    imp_res_tac state_rel_IMP
    \\ Cases_on ‘op’
    \\ fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
          sh_mem_load32_def,sh_mem_store32_def,
          sh_mem_load16_def,sh_mem_store16_def,
          sh_mem_load_byte_def,sh_mem_store_byte_def,get_var_def]
    \\ imp_res_tac state_rel_get_var >> fs[get_var_def]
    \\ ntac 2 (TOP_CASE_TAC>>fs[]) >>TRY (ntac 2 (CASE_TAC>>fs[]))>>
    rveq>>simp[]>>
    fs[state_rel_def,state_component_equality,FLOOKUP_UPDATE,dec_clock_def]>>rfs[]>>
    metis_tac[])
  THEN1 ( (* CodeBufferWrite *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def]
    \\ ntac 5 (TOP_CASE_TAC \\ fs[])
    \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ metis_tac[])
  THEN1 ( (* DataBufferWrite *)
    rw[comp_def]
    \\ fs[reg_bound_def]
    \\ fs[evaluate_def]
    \\ fs[case_eq_thms] \\ rveq \\ fs[]
    \\ simp[PULL_EXISTS]
    \\ simp[inst_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var
    \\ fs[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ simp[case_eq_thms]
    \\ simp[mem_store_def]
    \\ qexists_tac`0`
    \\ qhdtm_x_assum`state_rel`mp_tac
    \\ simp[state_rel_def] \\ strip_tac
    \\ qhdtm_x_assum`option_CASE`mp_tac
    \\ TOP_CASE_TAC \\ simp[]
    \\ TOP_CASE_TAC \\ simp[]
    \\ strip_tac
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ fs[wordSemTheory.buffer_write_def]
    \\ rveq \\ fs[]
    \\ conj_tac
    >- (
      fs[word_list_APPEND,GSYM word_add_n2w] \\
      qmatch_asmsub_abbrev_tac`fun2set (m,dm)` \\
      Cases_on`s.data_buffer.space_left` \\ fs[word_list_exists_thm] \\
      fs[SEP_CLAUSES,SEP_EXISTS_THM] \\
      qmatch_asmsub_abbrev_tac`one (aa,_)` \\
      qmatch_abbrev_tac`bb ∈ dm` \\
      `aa = bb` by (
        simp[Abbr`aa`,Abbr`bb`,GSYM bytes_in_word_def] \\
        simp[WORD_LEFT_ADD_DISTRIB] ) \\
      rveq \\ SEP_R_TAC )
    \\ conj_tac >- metis_tac[]
    \\ fs[word_list_APPEND,word_list_def]
    \\ Cases_on`s.data_buffer.space_left` \\ fs[word_list_exists_thm] \\
    fs[SEP_CLAUSES,SEP_EXISTS_THM] \\
    qmatch_asmsub_abbrev_tac`fun2set (m,dm)` \\
    qmatch_goalsub_abbrev_tac`(aa =+ ww) m` \\
    qmatch_goalsub_abbrev_tac`one (bb,_)` \\
    `aa = bb` by (simp[Abbr`aa`,Abbr`bb`,GSYM bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]) \\
    rveq \\
    SEP_W_TAC \\
    fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\
    fsrw_tac[star_ss][])
  THEN1 (* FFI *)
   (simp [Once comp_def]
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `xxx = (r,s2)` mp_tac
    \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac read_bytearray_IMP_read_bytearray \\ full_simp_tac(srw_ss())[]
    \\ pop_assum kall_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ full_simp_tac(srw_ss())[]
    \\ `t1.ffi = s.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DRESTRICT]
    \\ rev_full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ fs[GSYM STAR_ASSOC]
    \\ match_mp_tac write_bytearray_lemma \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac call_FFI_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* LocValue *)
   (full_simp_tac(srw_ss())[evaluate_def,Once comp_def] \\ srw_tac[][]
    \\ last_x_assum mp_tac \\ IF_CASES_TAC \\ rw[] \\ rw[]
    \\ reverse CASE_TAC
    THEN1 (fs [state_rel_def] \\ imp_res_tac code_rel_loc_check \\ fs [])
    \\ fs[state_rel_def,set_var_def,FLOOKUP_UPDATE,reg_bound_def]
    \\ `r <> k /\ r <> k+1 /\ r <> k+2` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ rw[] \\ fs[] \\ res_tac \\ fs[] \\ rfs[])
  THEN1 (* StackAlloc *) (
    simp[comp_def]
    \\ old_drule evaluate_stack_alloc
    \\ simp[]
    \\ disch_then old_drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] )
  THEN1 (* StackFree *) (
    simp[comp_def]
    \\ old_drule evaluate_stack_free
    \\ simp[]
    \\ disch_then old_drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_def]
    \\ every_case_tac \\ fs[])
  THEN1 (* StackLoad *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
    >-
      (simp[wordLangTheory.word_op_def]
      \\ simp[mem_load_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ `set_var r h t1 with clock := t1.clock = set_var r h t1` by full_simp_tac(srw_ss())[set_var_def]
      \\ full_simp_tac(srw_ss())[] \\ match_mp_tac state_rel_set_var
      \\ full_simp_tac(srw_ss())[reg_bound_def])
    >>
      fs[stack_load_def,evaluate_def]>>
      qpat_abbrev_tac`t = (set_var r _ _) with clock:= _`>>
      `FLOOKUP t.regs r = SOME(Word (c + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t`,set_var_def,FLOOKUP_UPDATE]>>
      old_drule evaluate_upshift>>
      disch_then (qspec_then `n` assume_tac)>>
      simp[inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>fs[Abbr`t`,set_var_def]>>
      simp[mem_load_def]
      \\ fsrw_tac[ARITH_ss][NOT_LESS]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]>>
      simp[GSYM set_var_def]>>
      match_mp_tac state_rel_set_var>>
      full_simp_tac(srw_ss())[reg_bound_def])
  THEN1 (* StackLoadAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k` by fs[]
    \\ simp[wordLangTheory.word_op_def]
    \\ fs[FLOOKUP_UPDATE]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[mem_load_def]
    \\ rpt(qpat_x_assum`∀x. _`kall_tac)
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND])
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[GSYM set_var_def])
  THEN1 (* StackStore *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ qexists_tac`0` \\ simp[]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    >-
      (simp[inst_def]
      \\ full_simp_tac(srw_ss())[]
      \\ simp[word_exp_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac (GEN_ALL state_rel_stack_store)
      \\ simp[])
    >>
      simp[stack_store_def,evaluate_def]>>
      fs[get_var_def]>>
      old_drule evaluate_upshift >> disch_then(qspec_then`n` assume_tac)>>
      simp[inst_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>
      fs[get_var_def,FLOOKUP_UPDATE,set_var_def]>>
      simp[mem_store_def]>>
      full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ qpat_abbrev_tac`t' = t1 with <|regs:=_ ; memory := _|>`>>
      `FLOOKUP t'.regs k = SOME (Word (c + bytes_in_word * n2w n + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t'`,FLOOKUP_UPDATE]>>
      old_drule evaluate_downshift>>disch_then(qspec_then`n` assume_tac)>>
      fs[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`t'`]>>
      qmatch_goalsub_abbrev_tac `t1 with <| regs:= R ; memory := M|>`>>
      `t1 with <|regs:=R;memory:=M|> = t1 with memory := M` by
        (simp[state_component_equality,Abbr`R`]>>
        match_mp_tac FUPDATE_ELIM>>
        qpat_x_assum`FLOOKUP _ k = SOME w` kall_tac>>
        qpat_x_assum`FLOOKUP _ k = SOME w` mp_tac>>
        simp[FDOM_FLOOKUP,Once FLOOKUP_DEF])>>
      simp[Abbr`M`]>>
      match_mp_tac (GEN_ALL state_rel_stack_store)>>
      simp[])
  THEN1 (* StackStoreAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ qexists_tac`0`\\simp[]
    \\ simp[inst_def,assign_def,word_exp_def,GSYM get_var_def]
    \\ imp_res_tac state_rel_get_var_k \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ simp[wordLangTheory.word_op_def]
    \\ REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp[get_var_set_var]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[mem_store_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[set_var_def,get_var_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[DECIDE ``n<m:num ==> n<>m``]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ strip_tac \\ strip_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE,DECIDE ``n<m:num ==> n<>m``]
    \\ rev_full_simp_tac(srw_ss())[ADD1,AC ADD_COMM ADD_ASSOC,word_list_def,word_list_APPEND]
    \\ fs[WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ CONJ_TAC >- metis_tac[]
    \\ qabbrev_tac `m = t1.memory`
    \\ qabbrev_tac `dm = t1.mdomain`
    \\ fs[word_list_APPEND]
    \\ SEP_WRITE_TAC)
  THEN1 (* StackGetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+1` by fs[reg_bound_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ `word_shift (:'a) MOD dimword (:'a) = word_shift (:'a)` by
         (fs[state_rel_def,good_dimindex_def,word_shift_def,dimword_def])
    \\ simp[wordLangTheory.word_sh_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[] )
    \\ simp[]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ dep_rewrite.DEP_REWRITE_TAC[bytes_in_word_word_shift]
    \\ qhdtm_x_assum`reg_bound`mp_tac \\simp[reg_bound_def]
    \\ strip_tac
    \\ qpat_x_assum`¬_`kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+2` by fs[] \\ rfs[]
    \\ `s.stack_space MOD dimword (:'a) ≤ LENGTH s.stack`
    by (
      `0 < dimword (:'a)` by simp[]
      \\ metis_tac[MOD_LESS_EQ,LESS_EQ_TRANS] )
    \\ reverse CONJ_TAC>- metis_tac[]
    \\ qmatch_assum_abbrev_tac`(a:num) + b * d < dw`
    \\ qmatch_abbrev_tac`d * f < dw`
    \\ `f ≤ s.stack_space ∧ f ≤ b` by
      (unabbrev_all_tac>>
      CONJ_ASM1_TAC>>fs[]>>
      match_mp_tac MOD_LESS_EQ>>
      fs[good_dimindex_def,dimword_def])
    \\ `d * f ≤ d * b ` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ decide_tac)
  THEN1 (* StackSetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ `word_shift (:'a) MOD dimword (:'a) = word_shift (:'a)` by
         (fs[state_rel_def,good_dimindex_def,word_shift_def,dimword_def])
    \\ simp[wordLangTheory.word_sh_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[])
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp [set_var_def,FLOOKUP_UPDATE]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[set_var_def,FLOOKUP_UPDATE]
    \\ rev_full_simp_tac(srw_ss())[lsl_word_shift]
    \\ fs[]
    \\ metis_tac[])
  THEN1 (* BitmapLoad *)
   (full_simp_tac(srw_ss())[stackSemTheory.evaluate_def] \\ every_case_tac
    \\ full_simp_tac(srw_ss())[reg_bound_def,GSYM NOT_LESS] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[comp_def,list_Seq_def,stackSemTheory.evaluate_def]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[is_SOME_Word_def])
    \\ `inst (Mem Load r (Addr (k + 1) (store_offset BitmapBase))) t1 =
          SOME (set_var r (Word ww) t1)` by
     (qpat_x_assum `state_rel jump off k s t1` mp_tac
      \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
      \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c' + store_offset BitmapBase) t1 = SOME (Word ww)` by
        (
          match_mp_tac (GEN_ALL mem_load_lemma)>>fs[store_list_def]>>
          asm_exists_tac>> simp[])
      \\ simp[])
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[LET_THM,stackSemTheory.inst_def,stackSemTheory.assign_def,
           word_exp_def,set_var_def,FLOOKUP_UPDATE,get_var_def]
    \\ `FLOOKUP t1.regs v = SOME (Word c)` by metis_tac [state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ `word_shift (:'a) MOD dimword (:'a) = word_shift (:'a)` by
         (fs[state_rel_def,good_dimindex_def,word_shift_def,dimword_def])
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def]
    \\ `mem_load (c << word_shift (:'a) + ww << word_shift (:'a)) t1 =
        SOME (Word (EL (w2n c) s.bitmaps))` by
     (fs[state_rel_def] \\ ntac 2 (qpat_x_assum `xx = SOME yy` kall_tac)
      \\ every_case_tac \\ full_simp_tac(srw_ss())[good_dimindex_def,word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[WORD_MUL_LSL, the_SOME_Word_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ rev_full_simp_tac(srw_ss())[bytes_in_word_def]
      \\ pop_assum (fn th => simp [GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[rich_listTheory.EL_LENGTH_APPEND,word_list_def]
      \\ full_simp_tac(srw_ss())[mem_load_def]  \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[])
    \\ `good_dimindex(:'a)` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[good_dimindex_def,word_shift_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[mem_load_def] \\ full_simp_tac(srw_ss())[GSYM mem_load_def] \\ full_simp_tac(srw_ss())[GSYM set_var_def]));
val _ = if null(hyp cc_full) andalso null(free_vars(concl cc_full)) then () else raise Fail "open theorem";
val _ = print("cc_full_statement=" ^ term_to_string(concl cc_full) ^ "\n");
val _ = print("cc_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_full))) ^ "\n");
