load "data_to_word_memoryProofTheory"; load "blastLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "block_rep_typed" data_to_word_memoryProofTheory.BlockRep_def;
val _ = show "block_nil_typed" data_to_word_memoryProofTheory.BlockNil_def;
val _ = show "thunk_block_typed" data_to_word_memoryProofTheory.ThunkBlock_def;
val _ = show "lower_bits_typed" data_to_wordTheory.get_lowerbits_def;
val _ = show "get_addr_typed" data_to_word_memoryProofTheory.get_addr_def;
val _ = show "word_addr_typed" data_to_word_memoryProofTheory.word_addr_def;
val _ = show "lower_bits_word8" (EVAL ``data_to_word$get_lowerbits
  ((c:data_to_word$config) with <|len_bits := 2; tag_bits := 1|>) (wordLang$Word (255w:word8))``);
val _ = show "lower_bits_wide" (EVAL ``data_to_word$get_lowerbits
  ((c:data_to_word$config) with <|len_bits := 20; tag_bits := 1|>) (wordLang$Word (254w:word8))``);
val _ = show "word_addr_loc" (EVAL ``data_to_word_memoryProof$word_addr
  (c:data_to_word$config) (gc_shared$Data (wordLang$Loc 7 9):word8 wordLang$word_loc gc_shared$heap_address)``);
val _ = show "lower_bits_word8_result" (prove(
  ``data_to_word$get_lowerbits ((c:data_to_word$config) with <|len_bits := 2; tag_bits := 1|>)
      (wordLang$Word (255w:word8)) = (15w:word8)``,
  simp [data_to_wordTheory.get_lowerbits_def, data_to_wordTheory.small_shift_length_def] >> blastLib.BBLAST_TAC));
val _ = show "lower_bits_wide_result" (prove(
  ``data_to_word$get_lowerbits ((c:data_to_word$config) with <|len_bits := 20; tag_bits := 1|>)
      (wordLang$Word (254w:word8)) = (255w:word8)``,
  simp [data_to_wordTheory.get_lowerbits_def, data_to_wordTheory.small_shift_length_def] >> blastLib.BBLAST_TAC));
val _ = show "make_byte_header_typed" data_to_wordTheory.make_byte_header_def;
val _ = show "thunk_tag_to_bits_typed" data_to_word_memoryProofTheory.thunk_tag_to_bits_def;
val _ = show "word_payload_typed" data_to_word_memoryProofTheory.word_payload_def;
val _ = show "word_payload_T_IMP_typed" data_to_word_memoryProofTheory.word_payload_T_IMP;
val _ = show "el_length_typed" gc_sharedTheory.el_length_def;
val _ = show "word_el_typed" data_to_word_memoryProofTheory.word_el_def;
val _ = show "word_heap_typed" data_to_word_memoryProofTheory.word_heap_def;
val _ = show "heap_length_typed" gc_sharedTheory.heap_length_def;
val _ = show "heap_length_APPEND_typed" gc_sharedTheory.heap_length_APPEND;
val _ = show "heap_lookup_MEM_typed" gc_sharedTheory.heap_lookup_MEM;
val _ = show "heap_lookup_SPLIT_typed" gc_sharedTheory.heap_lookup_SPLIT;
val _ = show "heap_lookup_LESS_typed" gc_sharedTheory.heap_lookup_LESS;
val _ = show "word_heap_APPEND_typed" data_to_word_memoryProofTheory.word_heap_APPEND;
val _ = show "word_list_APPEND_typed" data_to_word_memoryProofTheory.word_list_APPEND;
val _ = show "all_ts_head_eq_typed" data_to_word_memoryProofTheory.all_ts_head_eq;
val _ = show "blocks_unique_el_typed" data_to_word_memoryProofTheory.blocks_unique_el;
val _ = show "memory_rel_El_any_typed" data_to_word_memoryProofTheory.memory_rel_El_any;
val _ = show "memory_rel_Block_MEM_typed" data_to_word_memoryProofTheory.memory_rel_Block_MEM;
val _ = show "memory_rel_pointer_eq_typed" data_to_word_memoryProofTheory.memory_rel_pointer_eq;
val _ = show "memory_rel_ptr_eq_typed" data_to_word_memoryProofTheory.memory_rel_ptr_eq;
val _ = show "memory_rel_simple_eq_typed" data_to_word_memoryProofTheory.memory_rel_simple_eq;
val _ = show "word_header_def_typed" data_to_word_memoryProofTheory.word_header_def;
val _ = show "fix_clock_def_typed" data_to_word_memoryProofTheory.fix_clock_def;
val fix_clock_imp_replay = prove(
  ``!ck l x. data_to_word_memoryProof$fix_clock ck l x = SOME (w,l1,ck1) ==> ck1 <= ck /\ l1 <= l``,
  ho_match_mp_tac data_to_word_memoryProofTheory.fix_clock_ind
  >> fs [data_to_word_memoryProofTheory.fix_clock_def] >> rw []);
val _ = show "fix_clock_IMP_replay_typed" fix_clock_imp_replay;
val _ = show "word_is_clos_def_typed" data_to_word_memoryProofTheory.word_is_clos_def;
val _ = show "word_eq_thm0_typed" data_to_word_memoryProofTheory.word_eq_thm0;
val _ = show "word_list_limit_typed" data_to_word_memoryProofTheory.word_list_limit;
val _ = show "v_depth_def_typed" data_to_word_memoryProofTheory.v_depth_def;
val _ = show "elements_list_def_typed" data_to_word_memoryProofTheory.elements_list_def;
val _ = show "memory_rel_elements_list_words_typed" data_to_word_memoryProofTheory.memory_rel_elements_list_words;
val _ = show "memory_rel_Block_ptr_eq_typed" data_to_word_memoryProofTheory.memory_rel_Block_ptr_eq;
val _ = show "elements_list_all_blocks_typed" data_to_word_memoryProofTheory.elements_list_all_blocks;
val _ = show "memory_rel_elements_list_distinct_typed" data_to_word_memoryProofTheory.memory_rel_elements_list_distinct;
val _ = show "memory_rel_depth_limit_typed" data_to_word_memoryProofTheory.memory_rel_depth_limit;
val _ = show "memory_rel_depth_size_limit_typed" data_to_word_memoryProofTheory.memory_rel_depth_size_limit;
val _ = show "memory_rel_limit_typed" data_to_word_memoryProofTheory.memory_rel_limit;
val _ = show "vb_eq_size_def_typed" data_to_word_memoryProofTheory.vb_eq_size_def;
val _ = show "vb_eq_size_IMP_vb_size_typed" data_to_word_memoryProofTheory.vb_eq_size_IMP_vb_size;
val _ = show "word_mem_eq_def_typed" data_to_word_memoryProofTheory.word_mem_eq_def;
val _ = show "word_mem_eq_mixed_words" (EVAL ``data_to_word_memoryProof$word_mem_eq
  (0w:word32) [5w:word64; 5w] (\a. T) (\a. wordLang$Word (5w:word64))``);
val _ = show "word_mem_eq_mixed_unequal" (EVAL ``data_to_word_memoryProof$word_mem_eq
  (0w:word32) [5w:word64; 6w] (\a. T) (\a. wordLang$Word (5w:word64))``);
val _ = show "word_mem_eq_mixed_outside" (EVAL ``data_to_word_memoryProof$word_mem_eq
  (0w:word32) [5w:word64] (\a. F) (\a. wordLang$Word (5w:word64))``);
val _ = show "word_mem_eq_mixed_loc" (EVAL ``data_to_word_memoryProof$word_mem_eq
  (0w:word32) [5w:word64] (\a. T) (\a. wordLang$Loc 0 0)``);
val _ = show "do_eq_IFF_vb_eq_size_typed" data_to_word_memoryProofTheory.do_eq_IFF_vb_eq_size;
val _ = show "do_eq_IMP_vb_eq_size_typed" data_to_word_memoryProofTheory.do_eq_IMP_vb_eq_size;
val _ = show "vb_eq_size_IMP_do_eq_typed" data_to_word_memoryProofTheory.vb_eq_size_IMP_do_eq;
val _ = show "memory_rel_ptr_vb_eq_typed" data_to_word_memoryProofTheory.memory_rel_ptr_vb_eq;
val _ = show "memory_rel_ByteArray_words_IMP_typed" data_to_word_memoryProofTheory.memory_rel_ByteArray_words_IMP;
val _ = show "memory_rel_ValueArray_IMP_typed" data_to_word_memoryProofTheory.memory_rel_ValueArray_IMP;
val _ = show "memory_rel_Word64_IMP_typed" data_to_word_memoryProofTheory.memory_rel_Word64_IMP;
val _ = show "memory_rel_Number_bignum_IMP_ALT_typed" data_to_word_memoryProofTheory.memory_rel_Number_bignum_IMP_ALT;
val _ = show "memory_rel_Number_bignum_header_typed" data_to_word_memoryProofTheory.memory_rel_Number_bignum_header;
val _ = show "memory_rel_bignum_cmp_typed" data_to_word_memoryProofTheory.memory_rel_bignum_cmp;
val _ = show "memory_rel_Number_cmp_typed" data_to_word_memoryProofTheory.memory_rel_Number_cmp;
val _ = show "memory_rel_RefPtr_T_IMP_typed" data_to_word_memoryProofTheory.memory_rel_RefPtr_T_IMP;
val _ = show "memory_rel_Loc_typed" data_to_word_memoryProofTheory.memory_rel_Loc;
val _ = show "get_byte_bytes_to_word_typed" data_to_word_memoryProofTheory.get_byte_bytes_to_word;
val _ = show "write_bytes_inj_typed" data_to_word_memoryProofTheory.write_bytes_inj;
val _ = show "vb_eq_size_numbers" (EVAL ``data_to_word_memoryProof$vb_eq_size
  (sptree$LN : num bvlSem$ref sptree$num_map) (dataSem$Number 7) (dataSem$Number 7)``);
val _ = show "vb_eq_size_blocks" (EVAL ``data_to_word_memoryProof$vb_eq_size
  (sptree$LN : num bvlSem$ref sptree$num_map)
  (dataSem$Block 0 2 [dataSem$Number 7; dataSem$Number 8])
  (dataSem$Block 1 2 [dataSem$Number 7; dataSem$Number 9])``);
val _ = show "vb_eq_size_closures" (EVAL ``data_to_word_memoryProof$vb_eq_size
  (sptree$LN : num bvlSem$ref sptree$num_map)
  (dataSem$Block 0 30 [dataSem$Number 7]) (dataSem$Block 0 31 [dataSem$Number 9])``);
val _ = show "vb_eq_size_closure_mismatch" (EVAL ``data_to_word_memoryProof$vb_eq_size
  (sptree$LN : num bvlSem$ref sptree$num_map)
  (dataSem$Block 0 30 [dataSem$Number 7]) (dataSem$Block 0 2 [dataSem$Number 7])``);
val _ = show "vb_eq_size_list_short_circuit" (EVAL ``data_to_word_memoryProof$vb_eq_size_list
  (sptree$LN : num bvlSem$ref sptree$num_map)
  [dataSem$Number 7; dataSem$CodePtr 1] [dataSem$Number 8; dataSem$CodePtr 1]``);
val _ = show "vb_eq_size_list_error" (EVAL ``data_to_word_memoryProof$vb_eq_size_list
  (sptree$LN : num bvlSem$ref sptree$num_map)
  [dataSem$Number 7; dataSem$CodePtr 1] [dataSem$Number 7; dataSem$CodePtr 1]``);
val _ = show "word_eq_def_rebound_typed" data_to_word_memoryProofTheory.word_eq_def;
val _ = show "word_eq_LESS_EQ_typed" data_to_word_memoryProofTheory.word_eq_LESS_EQ;
val _ = show "word_eq_add_clock_typed" data_to_word_memoryProofTheory.word_eq_add_clock;
val _ = show "word_eq_max_clock_typed" data_to_word_memoryProofTheory.word_eq_max_clock;
val _ = show "word_eq_min_max_clock_typed" data_to_word_memoryProofTheory.word_eq_min_max_clock;
val _ = show "eq_assum_def_typed" data_to_word_memoryProofTheory.eq_assum_def;
val _ = show "eq_explode_def_typed" data_to_word_memoryProofTheory.eq_explode_def;
val _ = show "memory_rel_Block_explode_typed" data_to_word_memoryProofTheory.memory_rel_Block_explode;
val fix_clock_word_eq_replay = prove(
  ``data_to_word_memoryProof$fix_clock ck l
      (data_to_word_memoryProof$word_eq c st dm m l ck w1 w2) =
    data_to_word_memoryProof$word_eq c st dm m l ck w1 w2``,
  Cases_on `data_to_word_memoryProof$word_eq c st dm m l ck w1 w2` >> fs [data_to_word_memoryProofTheory.fix_clock_def]
  >> PairCases_on `x` >> fs [data_to_word_memoryProofTheory.fix_clock_def] >> rw []
  >> imp_res_tac data_to_word_memoryProofTheory.word_eq_LESS_EQ >> fs []);
val _ = show "fix_clock_word_eq_replay_typed" fix_clock_word_eq_replay;
val word_eq_list_original_replay = prove(
  ``data_to_word_memoryProof$word_eq_list c st dm m l ck w a1 (a2:'a word) =
      if w = 0w then SOME (1w,l,ck) else
      if ~(a1 IN dm) \/ ~(a2 IN dm) \/ l = 0 \/ ck = 0 then NONE else
      case (m a1,m a2) of
      | (Word w1, Word w2) =>
        (case fix_clock (ck-1) (l-1) (word_eq c st dm m (l-1) (ck-1) w1 w2) of
         | NONE => NONE
         | SOME (x,l',ck') => if x <> 1w then SOME (x,l',ck) else
                            if l' = 0 then NONE else
                              word_eq_list c st dm m (l'-1) ck (w-1w)
                                (a1 + bytes_in_word) (a2 + bytes_in_word))
      | _ => NONE``,
  PURE_REWRITE_TAC [fix_clock_word_eq_replay]
  >> MATCH_ACCEPT_TAC (CONJUNCT2 data_to_word_memoryProofTheory.word_eq_def));
val _ = show "word_eq_original_first_typed" (CONJUNCT1 data_to_word_memoryProofTheory.word_eq_def);
val _ = show "word_eq_list_original_replay_typed" word_eq_list_original_replay;
val _ = show "word_eq_equal64" (EVAL ``data_to_word_memoryProof$word_eq
  (c:data_to_word$config) st dm m 7 5 (8w:word64) 8w``);
val _ = show "word_eq_immediate64" (EVAL ``data_to_word_memoryProof$word_eq
  (c:data_to_word$config) st dm m 7 5 (8w:word64) 12w``);
val _ = show "word_eq_list_empty64" (EVAL ``data_to_word_memoryProof$word_eq_list
  (c:data_to_word$config) st dm m 3 2 (0w:word64) 16w 24w``);
val _ = show "word_eq_list_one64" (EVAL ``data_to_word_memoryProof$word_eq_list
  (c:data_to_word$config) st (\(a:word64). T) (\a. wordLang$Word (4w:word64))
  3 2 (1w:word64) 16w 24w``);
val _ = show "word_eq_list_clock_zero64" (EVAL ``data_to_word_memoryProof$word_eq_list
  (c:data_to_word$config) st (\(a:word64). T) (\a. wordLang$Word (4w:word64))
  3 0 (1w:word64) 16w 24w``);
val _ = show "word_eq_list_more_clock64" (EVAL ``data_to_word_memoryProof$word_eq_list
  (c:data_to_word$config) st (\(a:word64). T) (\a. wordLang$Word (4w:word64))
  3 7 (1w:word64) 16w 24w``);
val _ = show "heap_expand_typed" gc_sharedTheory.heap_expand_def;
val _ = show "gen_starts_in_store_typed" data_to_word_memoryProofTheory.gen_starts_in_store_def;
val _ = show "gen_starts_in_store_IMP_typed" data_to_word_memoryProofTheory.gen_starts_in_store_IMP;
val _ = show "glob_real_inv_typed" data_to_word_memoryProofTheory.glob_real_inv_def;
val _ = show "heap_in_memory_store_typed" data_to_word_memoryProofTheory.heap_in_memory_store_def;
val _ = show "heap_lookup_typed" gc_sharedTheory.heap_lookup_def;
val _ = show "heap_split_typed" gc_sharedTheory.heap_split_def;
val _ = show "is_data_element_typed" gc_sharedTheory.isDataElement_def;
val _ = show "is_some_data_element_typed" gc_sharedTheory.isSomeDataElement_def;
val _ = show "is_forward_pointer_typed" gc_sharedTheory.isForwardPointer_def;
val _ = show "roots_ok_typed" gc_sharedTheory.roots_ok_def;
val _ = show "heap_ok_typed" gc_sharedTheory.heap_ok_def;
val _ = show "data_up_to_typed" data_to_word_memoryProofTheory.data_up_to_def;
val _ = show "unused_space_inv_typed" data_to_word_memoryProofTheory.unused_space_inv_def;
val _ = show "is_mut_tag_typed" data_to_word_memoryProofTheory.isMutTag_def;
val _ = show "is_ref_typed" data_to_word_memoryProofTheory.isRef_def;
val _ = show "gen_start_ok_typed" data_to_word_memoryProofTheory.gen_start_ok_def;
val _ = show "gen_state_ok_typed" data_to_word_memoryProofTheory.gen_state_ok_def;
val _ = show "gc_kind_inv_typed" data_to_word_memoryProofTheory.gc_kind_inv_def;
val _ = show "ref_block_typed" data_to_word_memoryProofTheory.RefBlock_def;
val _ = show "word64_rep_typed" data_to_word_memoryProofTheory.Word64Rep_def;
val _ = show "word64_rep_data_typed" data_to_word_memoryProofTheory.Word64Rep_DataElement;
val _ = show "get_refs_typed" data_to_word_memoryProofTheory.get_refs_def;
val _ = show "ref_edge_typed" data_to_word_memoryProofTheory.ref_edge_def;
val _ = show "reachable_refs_typed" data_to_word_memoryProofTheory.reachable_refs_def;
val _ = show "v_all_ts_typed" data_to_word_memoryProofTheory.v_all_ts_def;
val _ = show "find_ref_typed" data_to_word_memoryProofTheory.find_ref_def;
val _ = show "all_ts_typed" data_to_word_memoryProofTheory.all_ts_def;
val _ = show "be_ok_typed" data_to_word_memoryProofTheory.be_ok_def;
val _ = show "v_all_vs_typed" data_to_word_memoryProofTheory.v_all_vs_def;
val _ = show "all_vs_typed" data_to_word_memoryProofTheory.all_vs_def;
val _ = show "MEM_v_all_vs_typed" data_to_word_memoryProofTheory.MEM_v_all_vs;
val _ = show "MEM_stack_all_vs_typed" data_to_word_memoryProofTheory.MEM_stack_all_vs;
val _ = show "v_all_vs_append_typed" data_to_word_memoryProofTheory.v_all_vs_append;
val _ = show "MEM_v_all_vs_FST_typed" data_to_word_memoryProofTheory.MEM_v_all_vs_FST;
val _ = show "MEM_v_all_vs_SUBSET_typed" data_to_word_memoryProofTheory.MEM_v_all_vs_SUBSET;
val _ = show "blocks_unique_stack_permute_typed" data_to_word_memoryProofTheory.blocks_unique_stack_permute;
val _ = show "blocks_unique_duplicate_typed" data_to_word_memoryProofTheory.blocks_unique_duplicate;
val _ = show "blocks_unique_move_typed" data_to_word_memoryProofTheory.blocks_unique_move;
val _ = show "blocks_unique_Number_typed" data_to_word_memoryProofTheory.blocks_unique_Number;
val _ = show "abs_ml_inv_Num_typed" data_to_word_memoryProofTheory.abs_ml_inv_Num;
val _ = show "IMP_memory_rel_Number_typed" data_to_word_memoryProofTheory.IMP_memory_rel_Number;
val _ = show "memory_rel_Number_IMP_typed" data_to_word_memoryProofTheory.memory_rel_Number_IMP;
val _ = show "memory_rel_any_Number_IMP_typed" data_to_word_memoryProofTheory.memory_rel_any_Number_IMP;
val _ = show "Smallnum_i2w_typed" data_to_word_memoryProofTheory.Smallnum_i2w;
val _ = show "num_less_thm_typed" data_to_word_memoryProofTheory.num_less_thm;
val _ = show "memory_rel_Number_LESS_typed" data_to_word_memoryProofTheory.memory_rel_Number_LESS;
val _ = show "memory_rel_Number_EQ_typed" data_to_word_memoryProofTheory.memory_rel_Number_EQ;
val _ = show "memory_rel_Number_LESS_EQ_typed" data_to_word_memoryProofTheory.memory_rel_Number_LESS_EQ;
val _ = show "memory_rel_Number_word_msb_typed" data_to_word_memoryProofTheory.memory_rel_Number_word_msb;
val _ = show "ref_eq_thm_typed" data_to_word_memoryProofTheory.ref_eq_thm;
val _ = show "memory_rel_RefPtr_EQ_IMP_typed" data_to_word_memoryProofTheory.memory_rel_RefPtr_EQ_IMP;
val _ = show "memory_rel_RefPtr_EQ_typed" data_to_word_memoryProofTheory.memory_rel_RefPtr_EQ;
val _ = show "memory_rel_RefPtr_IMP_lemma_typed" data_to_word_memoryProofTheory.memory_rel_RefPtr_IMP_lemma;
val _ = show "word_ml_inv_SP_LIMIT_typed" data_to_word_memoryProofTheory.word_ml_inv_SP_LIMIT;
val _ = show "get_addr_0_typed" data_to_word_memoryProofTheory.get_addr_0;
val _ = show "get_real_addr_def_typed" data_to_word_memoryProofTheory.get_real_addr_def;
val _ = show "get_real_offset_def_typed" data_to_word_memoryProofTheory.get_real_offset_def;
val _ = show "get_real_simple_addr_def_typed" data_to_word_memoryProofTheory.get_real_simple_addr_def;
val _ = show "get_real_offset_thm_typed" data_to_word_memoryProofTheory.get_real_offset_thm;
val _ = show "get_lowerbits_LSL_shift_length_typed" data_to_word_memoryProofTheory.get_lowerbits_LSL_shift_length;
val _ = show "get_real_addr_get_addr_typed" data_to_word_memoryProofTheory.get_real_addr_get_addr;
val _ = show "word_addr_eq_Loc_typed" data_to_word_memoryProofTheory.word_addr_eq_Loc;
val _ = show "blocks_unique_CodePtr_typed" data_to_word_memoryProofTheory.blocks_unique_CodePtr;
val _ = show "memory_rel_CodePtr_typed" data_to_word_memoryProofTheory.memory_rel_CodePtr;
val _ = show "memory_rel_Block_IMP_typed" data_to_word_memoryProofTheory.memory_rel_Block_IMP;
val _ = load "preamble";
val _ = load "helperLib";
open preamble wordsTheory data_to_word_memoryProofTheory dataSemTheory wordLangTheory;
open helperLib set_sepTheory wordSemTheory;
open multiwordTheory;
val memory_rel_MutBlock_IMP_F_replay = prove(
  ``memory_rel c be ts refs sp st m dm ((RefPtr T p,v:'a word_loc)::vars) /\
    lookup p refs = SOME (MutBlock tg fin ls cv rs) ==> F``,
  strip_tac >> fs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
                   bc_stack_ref_inv_def,v_inv_RefPtr_T,word_addr_def]);
val _ = show "memory_rel_MutBlock_IMP_F_replay_typed" memory_rel_MutBlock_IMP_F_replay;
val word_cmp_loop_thm_replay = prove(
  ``!xs1 (xs2:'a word list) f1 f2 (a1:'a word) a2.
      LENGTH xs1 = LENGTH xs2 /\ LENGTH xs1 < dimword (:'a) /\
      (word_list (a1 + bytes_in_word) (MAP Word xs1) * f1) (fun2set (m,dm)) /\
      (word_list (a2 + bytes_in_word) (MAP Word xs2) * f2) (fun2set (m,dm)) ==>
      word_cmp_loop (n2w (LENGTH xs1)) (a1 + bytes_in_word * n2w (LENGTH xs1))
        (a2 + bytes_in_word * n2w (LENGTH xs1)) dm m =
        SOME (case mw_cmp xs1 xs2 of NONE => 1w | SOME T => 0w | SOME F => 2w)``,
  ho_match_mp_tac mw_cmp_ind >> rw []
  >> `xs1 = [] \/ ∃y1 ys1. xs1 = SNOC y1 ys1` by metis_tac [SNOC_CASES]
  >> `xs2 = [] \/ ∃y2 ys2. xs2 = SNOC y2 ys2` by metis_tac [SNOC_CASES]
  >> simp [Once mw_cmp_def] >> fs []
  >> once_rewrite_tac [word_cmp_loop_def]
  >> full_simp_tac std_ss [GSYM SNOC_APPEND,FRONT_SNOC] >> fs []
  >> fs [ADD1] >> rfs []
  >> fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  >> fs [SNOC_APPEND,word_list_APPEND,miscTheory.word_list_def,SEP_CLAUSES]
  >> SEP_R_TAC >> rfs [] >> SEP_R_TAC >> fs []
  >> IF_CASES_TAC >> fs [] >> rw []
  >> first_x_assum match_mp_tac >> metis_tac [STAR_ASSOC]);
val _ = show "word_cmp_loop_thm_replay_typed" word_cmp_loop_thm_replay;
val word_mem_eq_thm_replay = prove(
  ``!xs ys a ff.
      (word_list a (MAP Word xs) * ff) (fun2set (m,dm)) /\ LENGTH xs = LENGTH ys ==>
      word_mem_eq a ys dm m = SOME (xs = ys)``,
  Induct >> Cases_on `ys` >> fs [word_mem_eq_def]
  >> fs [miscTheory.word_list_def] >> rpt strip_tac
  >> SEP_R_TAC >> fs [isWord_def]
  >> IF_CASES_TAC >> fs [] >> rveq
  >> first_x_assum match_mp_tac
  >> qexists_tac `one (a,Word h) * ff`
  >> fs [AC STAR_COMM STAR_ASSOC]);
val _ = show "word_mem_eq_thm_replay_typed" word_mem_eq_thm_replay;
val memory_rel_isClos_replay = prove(
  ``memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,Word (w1:'a word))::vars) /\
    word_bit 0 w1 /\ get_real_addr c st w1 = SOME a' /\ m a' = Word x' /\
    good_dimindex (:'a) ==> (isClos t1 v1 <=> word_is_clos c x')``,
  rw [] >> old_drule memory_rel_Block_IMP >> fs [word_bit] >> rw []
  >> fs [word_is_clos_def] >> old_drule encode_header_tag_mask >> fs [] >> strip_tac
  >> fs [isClos_def]
  >> `4 <= dimindex (:'a)` by fs [good_dimindex_def]
  >> fs [EXP_SUB,X_LT_DIV,LEFT_ADD_DISTRIB]
  >> `(16 * t1 + 2) < dimword (:α)` by
       (fs [good_dimindex_def,dimword_def] >> rfs []) >> fs []
  >> fs [good_dimindex_def,dimword_def,
         backend_commonTheory.partial_app_tag_def,backend_commonTheory.closure_tag_def]);
val _ = show "memory_rel_isClos_replay_typed" memory_rel_isClos_replay;
val eq_explode_append_replay = prove(
  ``!xs ys a. eq_explode a m dm (xs ++ ys) =
      eq_explode a m dm xs ++ eq_explode (a + n2w (LENGTH xs) * bytes_in_word) m dm ys``,
  Induct >> fs [eq_explode_def, ADD1, byteTheory.bytes_in_word_def, word_mul_n2w]
  >> fs [RIGHT_ADD_DISTRIB] >> fs [GSYM word_add_n2w]);
val _ = show "eq_explode_APPEND_replay_typed" eq_explode_append_replay;
val eq_assum_append_replay = prove(
  ``!xs ys a. eq_assum a m dm (xs ++ ys) <=>
      eq_assum a m dm xs /\ eq_assum (a + n2w (LENGTH xs) * bytes_in_word) m dm ys``,
  Induct >> fs [eq_assum_def, ADD1, byteTheory.bytes_in_word_def, word_mul_n2w]
  >> fs [RIGHT_ADD_DISTRIB] >> fs [GSYM word_add_n2w] >> rw [] >> eq_tac >> rw []);
val _ = show "eq_assum_APPEND_replay_typed" eq_assum_append_replay;
val block_block_small_eq_replay = prove(
  ``data_to_word_memoryProof$memory_rel c be ts refs sp st m dm
      ((dataSem$Block ts1 t1 v1,wordLang$Word (w1:'a word))::(dataSem$Block ts2 t2 v2,wordLang$Word w2)::vars) /\
    misc$good_dimindex (:'a) /\ w1 <> w2 /\ ~words$word_bit 0 w1 ==>
    LENGTH v1 <> LENGTH v2 \/ t1 <> t2``,
  rw [] >> old_drule memory_rel_Block_IMP >> fs []
  >> fs [word_bit] >> strip_tac >> rveq
  >> once_rewrite_tac [EQ_SYM_EQ]
  >> CCONTR_TAC >> fs [LENGTH_NIL] >> rveq
  >> imp_res_tac memory_rel_tail
  >> old_drule memory_rel_Block_IMP >> fs []);
val _ = show "memory_rel_Block_Block_small_eq_replay_typed" block_block_small_eq_replay;
val do_eq_list_false_replay = prove(
  ``!l l'. dataSem$do_eq_list refs l l' = Eq_val F /\ LENGTH l' = LENGTH l ==>
      ?i. i < LENGTH l /\ dataSem$do_eq refs (EL i l) (EL i l') = Eq_val F``,
  Induct >> Cases_on `l'` >> fs [] >> rpt strip_tac
  >> every_case_tac >> fs [] >> res_tac
  >- (qexists_tac `SUC i` >> fs [])
  >> qexists_tac `0` >> fs []);
val _ = show "do_eq_list_F_IMP_MEM_replay_typed" do_eq_list_false_replay;
val _ = show "memory_rel_tag_limit_typed" data_to_word_memoryProofTheory.memory_rel_tag_limit;
val _ = show "memory_rel_test_nil_eq_typed" data_to_word_memoryProofTheory.memory_rel_test_nil_eq;
val _ = show "memory_rel_test_none_eq_typed" data_to_word_memoryProofTheory.memory_rel_test_none_eq;
val _ = show "encode_header_EQ_typed" data_to_word_memoryProofTheory.encode_header_EQ;
val _ = show "encode_header_tag_mask_typed" data_to_word_memoryProofTheory.encode_header_tag_mask;
val _ = show "word_cmp_res_def_typed" data_to_word_memoryProofTheory.word_cmp_res_def;
val _ = show "word_cmp_loop_def_typed" data_to_word_memoryProofTheory.word_cmp_loop_def;
val _ = show "mw_cmp_def_typed" multiwordTheory.mw_cmp_def;
val _ = show "mw_cmp_thm_typed" multiwordTheory.mw_cmp_thm;
val _ = show "mw2n_inj_typed" data_to_word_memoryProofTheory.mw2n_inj;
val _ = show "mw_cmp_equal32" (EVAL ``multiword$mw_cmp [1w:word32;2w] [1w;2w]``);
val _ = show "mw_cmp_low_less32" (EVAL ``multiword$mw_cmp [1w:word32;2w] [4w;2w]``);
val _ = show "mw_cmp_high_greater32" (EVAL ``multiword$mw_cmp [1w:word32;3w] [4w;2w]``);
val _ = show "word_cmp_loop_refl_typed" data_to_word_memoryProofTheory.word_cmp_loop_refl;
val _ = show "memory_rel_Add_typed" data_to_word_memoryProofTheory.memory_rel_Add;
val _ = show "memory_rel_Sub_typed" data_to_word_memoryProofTheory.memory_rel_Sub;
val _ = show "memory_rel_And_typed" data_to_word_memoryProofTheory.memory_rel_And;
val _ = show "memory_rel_Or_typed" data_to_word_memoryProofTheory.memory_rel_Or;
val _ = show "memory_rel_Xor_typed" data_to_word_memoryProofTheory.memory_rel_Xor;
val _ = show "cons_thm_EMPTY_typed" data_to_word_memoryProofTheory.cons_thm_EMPTY;
val _ = show "word_ml_inv_Unit_typed" data_to_word_memoryProofTheory.word_ml_inv_Unit;
val _ = show "memory_rel_Unit_typed" data_to_word_memoryProofTheory.memory_rel_Unit;
val _ = show "memory_rel_Boolv_T_typed" data_to_word_memoryProofTheory.memory_rel_Boolv_T;
val _ = show "memory_rel_Boolv_F_typed" data_to_word_memoryProofTheory.memory_rel_Boolv_F;
val _ = show "memory_rel_Boolv_typed" data_to_word_memoryProofTheory.memory_rel_Boolv;
val _ = show "reachable_refs_stack_subset_typed" data_to_word_memoryProofTheory.reachable_refs_stack_subset;
val _ = show "v_all_vs_ts_MEM_typed" data_to_word_memoryProofTheory.v_all_vs_ts_MEM;
val _ = show "v_all_vs_ts_typed" data_to_word_memoryProofTheory.v_all_vs_ts;
val _ = show "v_all_vs_MEM2_typed" data_to_word_memoryProofTheory.v_all_vs_MEM2;
val _ = show "v_all_vs_ts_list_typed" data_to_word_memoryProofTheory.v_all_vs_ts_list;
val _ = show "MEM_in_all_ts_typed" data_to_word_memoryProofTheory.MEM_in_all_ts;
val _ = show "blocks_unique_typed" data_to_word_memoryProofTheory.blocks_unique_def;
val _ = show "all_ones_typed" data_to_wordTheory.all_ones_def;
val _ = show "maxout_bits_typed" data_to_wordTheory.maxout_bits_def;
val _ = show "ptr_bits_typed" data_to_wordTheory.ptr_bits_def;
val _ = show "small_int_typed" data_to_wordTheory.small_int_def;
val _ = show "smallnum_typed" data_to_wordTheory.Smallnum_def;
val _ = show "i2mw_typed" multiwordTheory.i2mw_def;
val _ = show "bignum_rep_typed" data_to_word_memoryProofTheory.Bignum_def;
val _ = show "ref_ptr_annot_typed" data_to_word_memoryProofTheory.ref_ptr_annot_def;
val _ = show "v_inv_ck_rules_typed" data_to_word_memoryProofTheory.v_inv_ck_rules;
val _ = show "v_inv_eq_typed" data_to_word_memoryProofTheory.v_inv_eq;
val _ = show "v_inv_RefPtr_T_typed" data_to_word_memoryProofTheory.v_inv_RefPtr_T;
val _ = show "v_inv_tf_restrict_lemma_typed" data_to_word_memoryProofTheory.v_inv_tf_restrict_lemma;
val _ = show "v_inv_tf_restrict_typed" data_to_word_memoryProofTheory.v_inv_tf_restrict;
val _ = show "n2mw_typed" multiwordTheory.n2mw_def;
val _ = show "mw2n_def_typed" multiwordTheory.mw2n_def;
val _ = show "mw2i_def_typed" multiwordTheory.mw2i_def;
val _ = show "mw2n_n2mw_typed" multiwordTheory.mw2n_n2mw;
val _ = show "LENGTH_n2mw_LESS_LENGTH_n2mw_typed" multiwordTheory.LENGTH_n2mw_LESS_LENGTH_n2mw;
val _ = show "mw2i_i2mw_typed" multiwordTheory.mw2i_i2mw;
val _ = show "bytes_to_word_typed" byteTheory.bytes_to_word_def;
val _ = show "write_bytes_typed" data_to_wordTheory.write_bytes_def;
val _ = show "bytes_rep_typed" data_to_word_memoryProofTheory.Bytes_def;
val _ = show "write_bytes_le" (EVAL ``data_to_word$write_bytes
  [17w:word8;34w;51w] [0xAABBCCDDw:word32;0x11223344w] F``);
val _ = show "write_bytes_be" (EVAL ``data_to_word$write_bytes
  [17w:word8;34w;51w] [0xAABBCCDDw:word32;0x11223344w] T``);
val _ = show "write_bytes_64" (EVAL ``data_to_word$write_bytes
  [1w:word8;2w;3w;4w;5w;6w;7w;8w;9w] [0w:word64;0w] F``);
val _ = show "bc_ref_inv_typed" data_to_word_memoryProofTheory.bc_ref_inv_def;
val _ = show "bc_stack_ref_inv_typed" data_to_word_memoryProofTheory.bc_stack_ref_inv_def;
val _ = show "abs_ml_inv_typed" data_to_word_memoryProofTheory.abs_ml_inv_def;
val _ = show "word_ml_inv_typed" data_to_word_memoryProofTheory.word_ml_inv_def;
val _ = show "memory_rel_typed" data_to_word_memoryProofTheory.memory_rel_def;
val _ = show "memory_rel_less_space_typed" data_to_word_memoryProofTheory.memory_rel_less_space;
val _ = show "memory_rel_zero_space_typed" data_to_word_memoryProofTheory.memory_rel_zero_space;
val _ = show "memory_rel_Number_IMP_Word_typed" data_to_word_memoryProofTheory.memory_rel_Number_IMP_Word;
val _ = show "memory_rel_Number_IMP_Word_2_typed" data_to_word_memoryProofTheory.memory_rel_Number_IMP_Word_2;
val _ = show "abs_ml_inv_stack_permute_typed" data_to_word_memoryProofTheory.abs_ml_inv_stack_permute;
val _ = show "pop_thm_typed" data_to_word_memoryProofTheory.pop_thm;
val _ = show "duplicate_thm_typed" data_to_word_memoryProofTheory.duplicate_thm;
val _ = show "duplicate1_thm_typed" data_to_word_memoryProofTheory.duplicate1_thm;
val _ = show "move_thm_typed" data_to_word_memoryProofTheory.move_thm;
val _ = show "split1_thm_typed" data_to_word_memoryProofTheory.split1_thm;
val _ = show "split2_thm_typed" data_to_word_memoryProofTheory.split2_thm;
val _ = show "split3_thm_typed" data_to_word_memoryProofTheory.split3_thm;
val _ = show "word_ml_inv_rearrange_typed" data_to_word_memoryProofTheory.word_ml_inv_rearrange;
val _ = show "memory_rel_rearrange_typed" data_to_word_memoryProofTheory.memory_rel_rearrange;
val _ = show "memory_rel_tl_typed" data_to_word_memoryProofTheory.memory_rel_tl;
val _ = show "memory_rel_tail_typed" data_to_word_memoryProofTheory.memory_rel_tail;
val _ = show "memory_rel_drop_typed" data_to_word_memoryProofTheory.memory_rel_drop;
val _ = show "memory_rel_swap_typed" data_to_word_memoryProofTheory.memory_rel_swap;
val _ = show "v_inv_ck_mono_typed" data_to_word_memoryProofTheory.v_inv_ck_mono;
val _ = show "v_inv_def_typed" data_to_word_memoryProofTheory.v_inv_def;
