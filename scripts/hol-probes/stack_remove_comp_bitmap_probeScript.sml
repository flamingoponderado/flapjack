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
val state_rel_get_var = GEN_ALL (prove(``  state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]));
val mem_load_lemma = GEN_ALL (prove(``  MEM name store_list ∧
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
  fs[store_list_def]));
val word_shift_def = backend_commonTheory.word_shift_def;
val cbl = prove(``!s res s2 t1 k off jump r v.
  stackSem$evaluate ((stackLang$BitmapLoad r v : 'a stackLang$prog),(s:('a,'b,'c)stackSem$state)) = (res,s2) /\ res <> SOME stackSem$Error /\
  state_rel jump off k s t1 /\ reg_bound (stackLang$BitmapLoad r v : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$BitmapLoad r v : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (res,t2) /\
    (case res of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >>
full_simp_tac(srw_ss())[stackSemTheory.evaluate_def] \\ every_case_tac
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
    \\ full_simp_tac(srw_ss())[mem_load_def] \\ full_simp_tac(srw_ss())[GSYM mem_load_def] \\ full_simp_tac(srw_ss())[GSYM set_var_def]);
val _ = print("cbl_statement=" ^ term_to_string(concl cbl) ^ "\n");
val _ = print("cbl_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cbl))) ^ "\n");
