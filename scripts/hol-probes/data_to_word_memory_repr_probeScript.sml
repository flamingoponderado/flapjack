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
val _ = show "word_heap_APPEND_typed" data_to_word_memoryProofTheory.word_heap_APPEND;
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
val _ = show "v_inv_ck_mono_typed" data_to_word_memoryProofTheory.v_inv_ck_mono;
val _ = show "v_inv_def_typed" data_to_word_memoryProofTheory.v_inv_def;
