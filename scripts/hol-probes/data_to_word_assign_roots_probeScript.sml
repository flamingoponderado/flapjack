load "preamble";
load "helperLib";
load "data_to_word_gcProofTheory";
load "data_to_word_memoryProofTheory";
load "data_to_word_assignProofTheory";
load "data_to_word_bignumProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  if null (hyp th) then (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has unexpected hypotheses");
val _ = emit "word_ml_inv_get_vars_IMP_lemma_typed"
  data_to_word_gcProofTheory.word_ml_inv_get_vars_IMP_lemma;
val _ = emit "memory_rel_lookup_var_IMP_typed"
  data_to_word_assignProofTheory.memory_rel_lookup_var_IMP;
val _ = emit "get_real_offset_lemma_typed"
  data_to_word_assignProofTheory.get_real_offset_lemma;
val _ = emit "get_real_byte_offset_lemma_typed"
  data_to_word_assignProofTheory.get_real_byte_offset_lemma;
val _ = emit "reorder_lemma_typed" data_to_word_assignProofTheory.reorder_lemma;
val _ = emit "reorder_2_lemma_typed" data_to_word_assignProofTheory.reorder_2_lemma;
val _ = emit "word_ml_inv_num_typed" data_to_word_memoryProofTheory.word_ml_inv_num;
val _ = emit "word_ml_inv_neg_num_typed" data_to_word_memoryProofTheory.word_ml_inv_neg_num;
val _ = emit "word_ml_inv_zero_typed" data_to_word_memoryProofTheory.word_ml_inv_zero;
val _ = emit "memory_rel_Deref_prime_typed" data_to_word_memoryProofTheory.memory_rel_Deref';
val _ = emit "get_real_addr_lemma_typed" data_to_word_bignumProofTheory.get_real_addr_lemma;
val _ = emit "memcopy_def_typed" data_to_word_assignProofTheory.memcopy_def;
val _ = emit "MemCopy_thm_typed" data_to_word_assignProofTheory.MemCopy_thm;
val _ = emit "memory_rel_IMP_free_space_typed" data_to_word_assignProofTheory.memory_rel_IMP_free_space;
val _ = emit "store_list_def_typed" data_to_word_memoryProofTheory.store_list_def;
val _ = emit "IMP_store_list_SOME_typed" data_to_word_assignProofTheory.IMP_store_list_SOME;

val _ = emit "get_vars_cut_env_typed" data_to_word_assignProofTheory.get_vars_cut_env;
val _ = emit "get_vars_IMP_domain_typed" data_to_word_assignProofTheory.get_vars_IMP_domain;
val _ = emit "assign_ConsExtend_def_typed" data_to_wordTheory.assign_ConsExtend_def;
val _ = emit "assign_ConsExtend_expand_typed" data_to_word_assignProofTheory.assign_ConsExtend_expand;
val _ = emit "assign_CopyByte_def_typed" data_to_wordTheory.assign_CopyByte_def;
val _ = emit "assign_ListAppend_def_typed" data_to_wordTheory.assign_ListAppend_def;
val _ = emit "assign_FromList_def_typed" data_to_wordTheory.assign_FromList_def;
val _ = emit "assign_RefArray_def_typed" data_to_wordTheory.assign_RefArray_def;
val _ = emit "assign_Ref_def_typed" data_to_wordTheory.assign_Ref_def;
val _ = emit "assign_AllocThunk_def_typed" data_to_wordTheory.assign_AllocThunk_def;
val _ = emit "assign_RefByte_def_typed" data_to_wordTheory.assign_RefByte_def;
val _ = emit "assign_ConfigGC_def_typed" data_to_wordTheory.assign_ConfigGC_def;
val _ = emit "assign_Cons_def_typed" data_to_wordTheory.assign_Cons_def;
val _ = emit "assign_MutCons_def_typed" data_to_wordTheory.assign_MutCons_def;
val _ = emit "SmallLsr_def_typed" data_to_wordTheory.SmallLsr_def;
val _ = emit "assign_XorByte_def_typed" data_to_wordTheory.assign_XorByte_def;
val _ = emit "SmallLsr_zero_eval" (EVAL ``data_to_word$SmallLsr (wordLang$Load (wordLang$Var 3)) 0 : 32 wordLang$exp``);
val _ = emit "SmallLsr_one_eval" (EVAL ``data_to_word$SmallLsr (wordLang$Load (wordLang$Var 3)) 1 : 32 wordLang$exp``);
val _ = emit "assign_Build_def_typed" data_to_wordTheory.assign_Build_def;
val _ = emit "assign_Install_def_typed" data_to_wordTheory.assign_Install_def;
val _ = emit "assign_EqualConst_def_typed" data_to_wordTheory.assign_EqualConst_def;
val _ = emit "assign_FFI_def_typed" data_to_wordTheory.assign_FFI_def;
val _ = emit "assign_WordTest_def_typed" data_to_wordTheory.assign_WordTest_def;
val _ = emit "assign_WordOpW8_def_typed" data_to_wordTheory.assign_WordOpW8_def;
val _ = emit "assign_WordShiftW8_def_typed" data_to_wordTheory.assign_WordShiftW8_def;
val _ = emit "assign_FP_cmp_def_typed" data_to_wordTheory.assign_FP_cmp_def;
val _ = emit "assign_FP_bop_def_typed" data_to_wordTheory.assign_FP_bop_def;
val _ = emit "assign_FP_uop_def_typed" data_to_wordTheory.assign_FP_uop_def;
val _ = emit "assign_FP_top_def_typed" data_to_wordTheory.assign_FP_top_def;
val _ = emit "assign_Add_def_typed" data_to_wordTheory.assign_Add_def;
val _ = emit "assign_Sub_def_typed" data_to_wordTheory.assign_Sub_def;
val _ = emit "assign_Mult_def_typed" data_to_wordTheory.assign_Mult_def;
val _ = emit "assign_Div_def_typed" data_to_wordTheory.assign_Div_def;
val _ = emit "assign_Mod_def_typed" data_to_wordTheory.assign_Mod_def;
val _ = emit "assign_def_typed" data_to_wordTheory.assign_def;
val _ = emit "comp_def_typed" data_to_wordTheory.comp_def;
val _ = emit "compile_part_def_typed" data_to_wordTheory.compile_part_def;
val _ = emit "assign_SetGlobalsPtr_typed" data_to_word_assignProofTheory.assign_SetGlobalsPtr;
val _ = emit "stubs_def_typed" data_to_wordTheory.stubs_def;
val _ = emit "code_rel_def_typed" data_to_word_gcProofTheory.code_rel_def;
val _ = emit "assign_Const_typed" data_to_word_assignProofTheory.assign_Const;
val _ = emit "assign_GlobalsPtr_typed" data_to_word_assignProofTheory.assign_GlobalsPtr;
val _ = emit "assign_Global_typed" data_to_word_assignProofTheory.assign_Global;
val _ = emit "assign_SetGlobal_typed" data_to_word_assignProofTheory.assign_SetGlobal;
val _ = emit "assign_BoolNot_typed" data_to_word_assignProofTheory.assign_BoolNot;
val _ = emit "assign_BoolTest_typed" data_to_word_assignProofTheory.assign_BoolTest;
val _ = emit "assign_Label_typed" data_to_word_assignProofTheory.assign_Label;
val _ = emit "assign_FFI_typed" data_to_word_assignProofTheory.assign_FFI;
val _ = emit "assign_FFI_final_typed" data_to_word_assignProofTheory.assign_FFI_final;
val _ = emit "getWords_acc_typed" data_to_word_assignProofTheory.getWords_acc;
val _ = emit "getWords_thm_typed" data_to_word_assignProofTheory.getWords_thm;
val _ = emit "word_cond_add_def_typed" data_to_word_memoryProofTheory.word_cond_add_def;
val _ = emit "store_list_word_cond_add_IMP_typed" data_to_word_assignProofTheory.store_list_word_cond_add_IMP;
val _ = emit "good_loc_def_typed" data_to_word_memoryProofTheory.good_loc_def;
val _ = emit "store_list_APPEND_typed" data_to_word_assignProofTheory.store_list_APPEND;
val _ = emit "evaluate_StoreAnyConsts_typed" data_to_word_assignProofTheory.evaluate_StoreAnyConsts;
val _ = emit "do_build_const_IMP_SOME_typed" data_to_word_assignProofTheory.do_build_const_IMP_SOME;
val _ = emit "bignum_size_typed" data_to_word_assignProofTheory.bignum_size;
val _ = emit "LESS_EQ_num_size_typed" data_to_word_memoryProofTheory.LESS_EQ_num_size;
val _ = emit "part_to_words_LENGTH_typed" data_to_word_memoryProofTheory.part_to_words_LENGTH;
val _ = emit "const_parts_to_words_LENGTH_typed" data_to_word_memoryProofTheory.const_parts_to_words_LENGTH;
val _ = emit "const_parts_to_words_good_loc_typed" data_to_word_memoryProofTheory.const_parts_to_words_good_loc;
val _ = emit "make_cons_ptr_def_typed" data_to_wordTheory.make_cons_ptr_def;
val _ = emit "build_part_words_def_typed" data_to_word_memoryProofTheory.build_part_words_def;
val _ = emit "build_words_def_typed" data_to_word_memoryProofTheory.build_words_def;
val _ = emit "do_part_SOME_IMP_SOME_typed" data_to_word_memoryProofTheory.do_part_SOME_IMP_SOME;
val _ = emit "least_notin_domain_typed" data_to_word_memoryProofTheory.least_notin_domain;
val _ = emit "byte_aligned_bytes_in_word_typed" data_to_word_memoryProofTheory.byte_aligned_bytes_in_word;
val _ = emit "byte_align_mult_bytes_in_word_typed" data_to_word_memoryProofTheory.byte_align_mult_bytes_in_word;
val _ = emit "word_and_lsr_0_typed" data_to_word_memoryProofTheory.word_and_lsr_0;
val _ = emit "byte_aligned_IMP_shift_typed" data_to_word_memoryProofTheory.byte_aligned_IMP_shift;
val _ = emit "make_cons_ptr_add_typed" data_to_word_memoryProofTheory.make_cons_ptr_add;
val _ = emit "make_ptr_add_typed" data_to_word_memoryProofTheory.make_ptr_add;
val _ = emit "all_ones_bit_typed" data_to_word_memoryProofTheory.all_ones_bit;
val _ = emit "maxout_bits_bit_typed" data_to_word_memoryProofTheory.maxout_bits_bit;
val _ = emit "maxout_bits_IMP_typed" data_to_word_memoryProofTheory.maxout_bits_IMP;
val _ = emit "get_lowerbits_ptrbits_typed" data_to_word_memoryProofTheory.get_lowerbits_ptrbits;
val _ = emit "make_cons_ptr_thm_typed" data_to_word_memoryProofTheory.make_cons_ptr_thm;
(* Replay the local exact data-lookup consequence of heap_store_rel. *)
val heap_store_rel_lemma_replay = let
  open preamble helperLib gc_sharedTheory data_to_word_memoryProofTheory
in
  Q.prove (`heap_store_rel h1 h2 /\ (heap_lookup n h1 = SOME (DataElement ys l d)) ==>
    (heap_lookup n h2 = SOME (DataElement ys l d))`,
    simp_tac std_ss [heap_store_rel_def,isSomeDataElement_def] \\ metis_tac [])
end;
val _ = emit "heap_store_rel_lemma_typed" heap_store_rel_lemma_replay;
(* Replay the original local functional list-relation theorem. *)
val EVERY2_f_EQ_replay = let open preamble in
  Q.prove (`!rs ws f. EVERY2 (\v w. f v = w) rs ws <=> MAP f rs = ws`,
    Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs [])
end;
val _ = emit "EVERY2_f_EQ_typed" EVERY2_f_EQ_replay;
(* Replay the local header decoding theorem with its local power bounds. *)
val encode_header_IMP_replay = let
  open preamble helperLib wordsTheory alignmentTheory data_to_wordTheory word_gcFunctionsTheory data_to_word_memoryProofTheory
  val good_dimindex_def = miscTheory.good_dimindex_def
  val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]
  val _ = diminish_srw_ss ["ABBREV"]
  val _ = set_trace "BasicProvers.var_eq_old" 1
  val LESS_EXO_SUB = Q.prove (`n < 2 ** (k - m) ==> n < 2n ** k`,
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs []
  )
  val LESS_EXO_SUB_ALT = Q.prove (`m <= k ==> n < 2 ** (k - m) ==> n * 2 ** m < 2n ** k`,
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** (k - m) * 2 ** m`
  \\ fs [GSYM EXP_ADD]
  )
  val less_pow_dimindex_sub_imp = Q.prove (`n < 2 ** (dimindex (:'a) - k) ==> n < dimword (:'a)`,
  fs [dimword_def] \\ metis_tac [LESS_EXO_SUB]
  )
  val encode_header_IMP = Q.prove (`encode_header c tag len = SOME (hd:'a word) /\
    c.len_size + 5 < dimindex (:'a) /\ good_dimindex (:'a) ==>
    len < 2 ** (dimindex (:'a) - 4) /\
    decode_length c hd = n2w len`,
  fs [encode_header_def] \\ rw [make_header_def] \\ fs [decode_length_def]
  \\ `3w >>> (dimindex (:α) − c.len_size) = 0w:'a word` by
      (match_mp_tac n2w_lsr_eq_0
       \\ fs [good_dimindex_def,dimword_def]
       \\ fs [DIV_EQ_X]
       \\ match_mp_tac LESS_LESS_EQ_TRANS
       \\ qexists_tac `2 ** 2`
       \\ strip_tac \\ TRY (EVAL_TAC \\ NO_TAC)
       \\ simp_tac std_ss [EXP_BASE_LE_IFF] \\ fs [])
  \\ `n2w tag << 2 ⋙ (dimindex (:α) - c.len_size) = 0w:'a word` by
      (fs [WORD_MUL_LSL,word_mul_n2w]
       \\ match_mp_tac n2w_lsr_eq_0
       \\ rpt strip_tac \\ TRY (match_mp_tac LESS_DIV_EQ_ZERO)
       \\ `2 ** (dimindex (:α) − c.len_size) =
           2n ** 2 * 2 ** (dimindex (:α) − (c.len_size + 2))` by
              (full_simp_tac std_ss [GSYM EXP_ADD] \\ fs []) \\ fs []
       \\ `4 * tag = tag * 2 ** 2` by fs []
       \\ asm_rewrite_tac [dimword_def]
       \\ match_mp_tac (MP_CANON LESS_EXO_SUB_ALT)
       \\ full_simp_tac std_ss [SUB_PLUS |> ONCE_REWRITE_RULE [ADD_COMM]]
       \\ imp_res_tac LESS_EXO_SUB \\ fs [])
  \\ fs [] \\ match_mp_tac lsl_lsr
  \\ imp_res_tac less_pow_dimindex_sub_imp \\ fs []
  \\ `dimword (:'a) = 2 ** c.len_size * 2 ** (dimindex (:α) − c.len_size)`
        suffices_by fs []
  \\ fs [GSYM EXP_ADD,dimword_def]
  )
in encode_header_IMP end;
val _ = emit "encode_header_IMP_typed" encode_header_IMP_replay;
(* Replay the three local data-lookup lemmas used by the allocation proof. *)
val (lookup_unused_replay, lookup_expand_replay, lookup_cons_replay) = let
  open preamble helperLib gc_sharedTheory
  val lemma1 = Q.prove (`isSomeDataElement (heap_lookup n (Unused k :: xs)) <=>
    k < n /\ isSomeDataElement (heap_lookup (n-(k+1)) xs)`,
    srw_tac [] [heap_lookup_def,isSomeDataElement_def,el_length_def,NOT_LESS]
    THEN1 (DISJ1_TAC \\ DECIDE_TAC)
    \\ `k < n` by DECIDE_TAC \\ full_simp_tac std_ss [])
  val lemma2 = Q.prove (`isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) <=>
    k <= n /\ isSomeDataElement (heap_lookup (n-k) xs)`,
    srw_tac [] [heap_expand_def,lemma1]
    \\ imp_res_tac (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
    \\ full_simp_tac std_ss []
    \\ Cases_on `isSomeDataElement (heap_lookup (n - k) xs)`
    \\ full_simp_tac std_ss [] \\ DECIDE_TAC)
  val lemma3 = Q.prove (`n <> 0 ==>
    (isSomeDataElement (heap_lookup n (x::xs)) <=>
     el_length x <= n /\ isSomeDataElement (heap_lookup (n - el_length x) xs))`,
    srw_tac [] [heap_expand_def,heap_lookup_def,isSomeDataElement_def]
    \\ Cases_on `n < el_length x` THEN srw_tac [] []
    THEN1 (DISJ1_TAC \\ DECIDE_TAC)
    \\ `el_length x <= n` by DECIDE_TAC \\ full_simp_tac std_ss [])
in (lemma1, lemma2, lemma3) end;
val _ = emit "isSomeDataElement_heap_lookup_lemma1_typed" lookup_unused_replay;
val _ = emit "isSomeDataElement_heap_lookup_lemma2_typed" lookup_expand_replay;
val _ = emit "isSomeDataElement_heap_lookup_lemma3_typed" lookup_cons_replay;
(* Replay the full local HOL allocation-existence proof. *)
val IMP_heap_store_unused_alt_replay = let
  open preamble helperLib gc_sharedTheory data_to_word_memoryProofTheory
  val isSomeDataElement_heap_lookup_lemma1 = lookup_unused_replay
  val isSomeDataElement_heap_lookup_lemma2 = lookup_expand_replay
  val isSomeDataElement_heap_lookup_lemma3 = lookup_cons_replay
in
  Q.prove (`unused_space_inv a sp (heap:('a,'b) heap_element list) /\
    el_length x <= sp ==>
    ?heap2. (heap_store_unused_alt a sp x heap = (heap2,T)) /\
            (isDataElement x ==>
               unused_space_inv (a + el_length x) (sp - el_length x) heap2) /\
            (heap_lookup a heap2 = SOME x) /\
            ~isSomeDataElement (heap_lookup a heap) /\
            (heap_length heap2 = heap_length heap) /\
            (~isForwardPointer x ==>
             (FILTER isForwardPointer heap2 = FILTER isForwardPointer heap)) /\
            (!xs l d.
               MEM (DataElement xs l d) heap2 <=>
                 (x = DataElement xs l d) \/
                 MEM (DataElement xs l d) heap) /\
            (isDataElement x ==>
             ({a | isSomeDataElement (heap_lookup a heap2)} =
               a INSERT {a | isSomeDataElement (heap_lookup a heap)})) /\
            heap_store_rel heap heap2` ,
  rpt strip_tac \\ asm_simp_tac std_ss [heap_store_unused_alt_def,heap_store_rel_def]
  \\ `sp <> 0` by (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss [unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [heap_store_lemma]
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def]
    \\ full_simp_tac std_ss [GSYM heap_length_def,heap_length_heap_expand]
    \\ DECIDE_TAC)
  \\ strip_tac THEN1
   (rpt strip_tac
    \\ full_simp_tac std_ss [APPEND_ASSOC,heap_expand_def]
    \\ `ha ++ [x] ++ [Unused (sp − el_length x − 1)] ++ hb =
        ha ++ [x] ++ Unused (sp − el_length x − 1)::hb` by
          fs [APPEND] \\ pop_assum (fn th => fs [th])
    \\ `el_length x + heap_length ha = heap_length (ha ++ [x])` by
          (fs [heap_length_def,SUM_APPEND] \\ NO_TAC)
    \\ pop_assum (fn th => fs [th]) \\ fs [heap_lookup_PREFIX]
    \\ qabbrev_tac `hh = ha ++ [x]`
    \\ full_simp_tac std_ss [data_up_to_APPEND,GSYM APPEND_ASSOC]
    \\ unabbrev_all_tac \\ fs []
    \\ fs [heap_length_APPEND,el_length_def,heap_length_heap_expand]
    \\ fs [heap_length_def,el_length_def] \\ rw [el_length_def])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac std_ss [APPEND_ASSOC]
    \\ `heap_length ha + sp - el_length x =
        heap_length (ha ++ heap_expand (sp - el_length x))` by
     (full_simp_tac std_ss [heap_length_APPEND,heap_length_heap_expand] \\ DECIDE_TAC)
    \\ full_simp_tac std_ss [heap_lookup_PREFIX])
  \\ strip_tac THEN1 (fs [isSomeDataElement_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      heap_length_def,el_length_def] \\ DECIDE_TAC)
  \\ strip_tac THEN1
   (full_simp_tac std_ss [rich_listTheory.FILTER_APPEND,FILTER,isForwardPointer_def,APPEND_NIL]
    \\ srw_tac [] [heap_expand_def,isForwardPointer_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [MEM_APPEND,MEM,heap_expand_def]
    \\ Cases_on `sp <= el_length x` \\ full_simp_tac (srw_ss()) []
    \\ metis_tac [])
  \\ strip_tac THEN1
   (rpt strip_tac \\ full_simp_tac (srw_ss()) [EXTENSION]
    \\ strip_tac \\ Q.ABBREV_TAC `y = x'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `y = heap_length ha`
    \\ full_simp_tac std_ss [] THEN1
     (full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,heap_lookup_PREFIX]
      \\ full_simp_tac (srw_ss()) [isDataElement_def,isSomeDataElement_def])
    \\ Cases_on `y < heap_length ha`
    THEN1 (full_simp_tac std_ss [LESS_IMP_heap_lookup,GSYM APPEND_ASSOC])
    \\ imp_res_tac NOT_LESS_IMP_heap_lookup
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [isSomeDataElement_heap_lookup_lemma1,
         isSomeDataElement_heap_lookup_lemma2]
    \\ `0 < el_length x` by
         (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
    \\ fs [heap_lookup_def,APPEND,heap_expand_def]
    \\ IF_CASES_TAC \\ fs []
    THEN1 fs [isSomeDataElement_def]
    \\ Cases_on `sp = el_length x` \\ fs []
    \\ fs [heap_lookup_def,el_length_def]
    \\ rw [] \\ fs [isSomeDataElement_def])
  \\ rpt strip_tac
  \\ full_simp_tac std_ss [isSomeDataElement_def]
  \\ Cases_on `ptr < heap_length ha`
  THEN1 (imp_res_tac LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ `0 < el_length x` by (Cases_on `x` \\ EVAL_TAC \\ fs [])
  \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ qpat_x_assum `xxx = SOME yyy` MP_TAC
  \\ simp_tac std_ss [Once heap_lookup_def] \\ srw_tac [] []
  \\ fs [el_length_def]
  \\ fs [heap_expand_def] \\ rw []
  \\ fs [heap_lookup_def] \\ rw []
  \\ fs [el_length_def]
  \\ imp_res_tac LESS_EQUAL_ANTISYM \\ fs []
  \\ rveq \\ fs []
  \\ rfs [GSYM SUB_PLUS]
  )
end;
val _ = emit "heap_store_rel_v_inv_typed" data_to_word_memoryProofTheory.heap_store_rel_v_inv;
val _ = emit "memory_rel_Cons1_typed" data_to_word_memoryProofTheory.memory_rel_Cons1;
val _ = emit "store_list_thm_typed" data_to_word_memoryProofTheory.store_list_thm;
val _ = emit "heap_store_unused_alt_IMP_length_typed" data_to_word_memoryProofTheory.heap_store_unused_alt_IMP_length;
val _ = emit "cons_thm_alt_typed" data_to_word_memoryProofTheory.cons_thm_alt;
val _ = emit "IMP_heap_store_unused_alt_typed" IMP_heap_store_unused_alt_replay;
(* Replay the original local allocation-shape theorem. *)
val heap_store_unused_alt_thm_replay = let
  open preamble helperLib gc_sharedTheory data_to_word_memoryProofTheory
in
  Q.prove (`!a n heap h1 h2 heap2 x.
    heap_split (a + n) heap = SOME (h1,h2) /\
    heap_store_unused_alt a n x heap = (heap2,T) /\
    unused_space_inv (a + el_length x) (n - el_length x) heap2 ==>
    ?h0. h1 = h0 ++ [Unused (n-1)] /\
         heap = h1 ++ h2 /\ heap_length h0 = a /\
         heap2 = h0 ++ [x] ++ heap_expand (n - el_length x) ++ h2`,
    fs [heap_store_unused_alt_def] \\ rw []
    \\ fs [unused_space_inv_def]
    \\ imp_res_tac gc_sharedTheory.heap_split_heap_length
    \\ fs [] \\ rveq \\ fs []
    \\ fs [heap_lookup_APPEND]
    \\ `0 < n` by (Cases_on `x` \\ fs [el_length_def])
    \\ fs [] \\ old_drule heap_lookup_SPLIT
    \\ strip_tac \\ rveq \\ fs []
    \\ `hb = []` by
      (fs [heap_length_APPEND]
       \\ fs [heap_length_def,el_length_def]
       \\ Cases_on `hb` \\ fs [])
    \\ rveq \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ fs [heap_store_lemma])
end;
val _ = emit "heap_store_unused_alt_thm_typed" heap_store_unused_alt_thm_replay;
(* Replay the original local heap_split_heap_store proof: local HOL theorems
   are not exported by data_to_word_memoryProofTheory. *)
val heap_split_heap_store_replay = let
  open preamble helperLib gc_sharedTheory data_to_word_memoryProofTheory
in
  Q.prove (`!heap e h1 h2 a y heap2.
      heap_split e heap = SOME (h1,h2) /\
      heap_store a y heap = (heap2,T) /\ e <= a ==>
      ?h3. heap_split e heap2 = SOME (h1,h3)`,
    Induct \\ fs [heap_split_def,heap_store_def]
    \\ rpt gen_tac
    \\ IF_CASES_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ strip_tac \\ rveq
    \\ Cases_on `a=0` \\ fs []
    \\ Cases_on `a < el_length h` \\ fs []
    \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ res_tac \\ rfs []
    \\ fs [heap_split_def])
end;
val _ = emit "heap_split_heap_store_typed" heap_split_heap_store_replay;
(* Replay the dependent original local generation-state theorem. *)
val heap_store_unused_alt_gen_state_ok_replay = let
  open preamble helperLib gc_sharedTheory data_to_word_memoryProofTheory
  val heap_split_heap_store = heap_split_heap_store_replay
in
  Q.prove (`heap_store_unused_alt a k x heap = (heap2,T) /\
    gen_state_ok a (a + k) heap gens ==>
    gen_state_ok (a + el_length x) (a + k) heap2 gens`,
    Cases_on `gens` \\ fs [gen_state_ok_def]
    \\ fs [EVERY_MEM] \\ rw [] \\ res_tac \\ fs []
    \\ fs [gen_start_ok_def]
    \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ fs [heap_store_unused_alt_def]
    \\ every_case_tac \\ fs []
    \\ fs [GSYM IMP_DISJ_THM]
    \\ imp_res_tac heap_split_heap_store \\ fs []
    \\ rveq \\ fs [] \\ res_tac \\ fs [])
end;
val _ = emit "heap_store_unused_alt_gen_state_ok_typed" heap_store_unused_alt_gen_state_ok_replay;

val _ = emit "heap_store_unused_alt_heap_lookup_typed" data_to_word_memoryProofTheory.heap_store_unused_alt_heap_lookup;
val _ = emit "heap_store_unused_alt_def_typed" data_to_word_memoryProofTheory.heap_store_unused_alt_def;
val _ = emit "heap_store_rel_def_typed" data_to_word_memoryProofTheory.heap_store_rel_def;
val _ = emit "memory_rel_Cons_empty_typed" data_to_word_memoryProofTheory.memory_rel_Cons_empty;
val _ = emit "parts_to_words_add_typed" data_to_word_memoryProofTheory.parts_to_words_add;
val _ = emit "part_to_words_add_typed" data_to_word_memoryProofTheory.part_to_words_add;
val _ = emit "part_to_words_IMP_build_words_typed" data_to_word_memoryProofTheory.part_to_words_IMP_build_words;
val _ = emit "parts_to_words_IMP_build_words_typed" data_to_word_memoryProofTheory.parts_to_words_IMP_build_words;
