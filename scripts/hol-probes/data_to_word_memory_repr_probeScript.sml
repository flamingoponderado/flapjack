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
val _ = show "blocks_unique_typed" data_to_word_memoryProofTheory.blocks_unique_def;
