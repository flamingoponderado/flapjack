load "preamble";
load "helperLib";
open helperLib;
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory byteTheory miscTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val state_rel_get_var = GEN_ALL (prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
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
val cc_storeconsts = prove(``!t1 t2 stub s r s2 t1' k off jump.
 evaluate (StoreConsts t1 t2 stub,s) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k s t1' /\ reg_bound (StoreConsts t1 t2 stub) k ==>
 ?ck t2'. evaluate (comp jump off k (StoreConsts t1 t2 stub),t1' with clock := ck + t1'.clock) = (r,t2') /\
 (case r of SOME (Halt _) => t2'.ffi = s2.ffi
 | SOME TimeOut => t2'.ffi = s2.ffi
 | SOME (FinalFFI _) => t2'.ffi = s2.ffi
 | _ => state_rel jump off k s2 t2')``,
 rpt strip_tac >>
fs [comp_def]
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
    \\ rw [] \\ res_tac \\ fs [] );
val _ = if null(hyp cc_storeconsts) andalso null(free_vars(concl cc_storeconsts)) then () else raise Fail "open theorem";
val _ = print("cc_storeconsts_statement=" ^ term_to_string(concl cc_storeconsts) ^ "\n");
val _ = print("cc_storeconsts_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_storeconsts))) ^ "\n");
