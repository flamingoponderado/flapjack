(* Typed source declarations for stack_allocProof (task 148). *)
load "preamble";
load "stack_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_allocProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_allocProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_allocProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "alloc_correct_lemma_typed" "alloc_correct_lemma";
val _ = emit "alloc_length_stack_typed" "alloc_length_stack";
val _ = emit "alloc_correct_lemma_Generational_typed" "alloc_correct_lemma_Generational";
val _ = emit "alloc_correct_lemma_None_typed" "alloc_correct_lemma_None";
val _ = emit "alloc_correct_lemma_Simple_typed" "alloc_correct_lemma_Simple";
val _ = emit "filter_bitmap_IMP_LENGTH_typed" "filter_bitmap_IMP_LENGTH";
val _ = emit "filter_bitmap_map_bitmap_typed" "filter_bitmap_map_bitmap";
val _ = emit "map_bitmap_IMP_LENGTH_typed" "map_bitmap_IMP_LENGTH";
val _ = emit "word_gc_move_code_thm_typed" "word_gc_move_code_thm";
val _ = emit "word_gc_move_bitmap_code_thm_typed" "word_gc_move_bitmap_code_thm";
val _ = emit "word_gc_move_bitmaps_code_thm_typed" "word_gc_move_bitmaps_code_thm";
val _ = emit "word_gc_move_list_code_thm_typed" "word_gc_move_list_code_thm";
val _ = emit "word_gc_move_roots_bitmaps_code_thm_typed" "word_gc_move_roots_bitmaps_code_thm";
val _ = emit "word_gen_gc_move_code_thm_typed" "word_gen_gc_move_code_thm";
val _ = emit "word_gen_gc_move_bitmap_code_thm_typed" "word_gen_gc_move_bitmap_code_thm";
val _ = emit "word_gen_gc_move_bitmaps_code_thm_typed" "word_gen_gc_move_bitmaps_code_thm";
val _ = emit "word_gen_gc_move_list_code_thm_typed" "word_gen_gc_move_list_code_thm";
val _ = emit "word_gen_gc_move_roots_bitmaps_code_thm_typed" "word_gen_gc_move_roots_bitmaps_code_thm";
val _ = emit "word_gen_gc_partial_move_code_thm_typed" "word_gen_gc_partial_move_code_thm";
val _ = emit "word_gen_gc_partial_move_bitmap_code_thm_typed" "word_gen_gc_partial_move_bitmap_code_thm";
val _ = emit "word_gen_gc_partial_move_bitmaps_code_thm_typed" "word_gen_gc_partial_move_bitmaps_code_thm";
val _ = emit "word_gen_gc_partial_move_list_code_thm_typed" "word_gen_gc_partial_move_list_code_thm";
val _ = emit "word_gen_gc_partial_move_roots_bitmaps_code_thm_typed" "word_gen_gc_partial_move_roots_bitmaps_code_thm";
val _ = emit "memcpy_code_thm_typed" "memcpy_code_thm";
val _ = emit "comp_correct_typed" "comp_correct";
val _ = emit "compile_semantics_typed" "compile_semantics";
val _ = emit "compile_has_fp_ops_typed" "compile_has_fp_ops";
val _ = emit "stack_alloc_call_args_typed" "stack_alloc_call_args";
val _ = emit "stack_alloc_comp_stack_asm_name_typed" "stack_alloc_comp_stack_asm_name";
val _ = emit "stack_alloc_reg_bound_typed" "stack_alloc_reg_bound";
val _ = emit "stack_alloc_stack_asm_convs_typed" "stack_alloc_stack_asm_convs";
val _ = emit "word_gc_move_bitmap_def_typed" "word_gc_move_bitmap_def";
val _ = emit "word_gc_move_bitmaps_def_typed" "word_gc_move_bitmaps_def";
val _ = emit "word_gc_move_bitmaps_LENGTH_typed" "word_gc_move_bitmaps_LENGTH";
val _ = emit "word_gc_move_loop_F_typed" "word_gc_move_loop_F";
val _ = emit "word_gc_move_loop_ok_typed" "word_gc_move_loop_ok";
val _ = emit "word_gc_move_roots_bitmaps_def_typed" "word_gc_move_roots_bitmaps_def";
val _ = emit "word_gc_move_roots_IMP_LENGTH_typed" "word_gc_move_roots_IMP_LENGTH";
val _ = emit "word_gen_gc_move_bitmap_def_typed" "word_gen_gc_move_bitmap_def";
val _ = emit "word_gen_gc_move_bitmaps_def_typed" "word_gen_gc_move_bitmaps_def";
val _ = emit "word_gen_gc_move_bitmaps_LENGTH_typed" "word_gen_gc_move_bitmaps_LENGTH";
val _ = emit "word_gen_gc_move_roots_bitmaps_def_typed" "word_gen_gc_move_roots_bitmaps_def";
val _ = emit "word_gen_gc_move_roots_IMP_LENGTH_typed" "word_gen_gc_move_roots_IMP_LENGTH";
val _ = emit "word_gen_gc_partial_move_bitmap_def_typed" "word_gen_gc_partial_move_bitmap_def";
val _ = emit "word_gen_gc_partial_move_bitmaps_def_typed" "word_gen_gc_partial_move_bitmaps_def";
val _ = emit "word_gen_gc_partial_move_bitmaps_LENGTH_typed" "word_gen_gc_partial_move_bitmaps_LENGTH";
val _ = emit "word_gen_gc_partial_move_roots_bitmaps_def_typed" "word_gen_gc_partial_move_roots_bitmaps_def";
val _ = emit "word_gen_gc_partial_move_roots_IMP_LENGTH_typed" "word_gen_gc_partial_move_roots_IMP_LENGTH";
val _ = emit "extract_labels_next_lab_typed" "extract_labels_next_lab";
val _ = emit "next_lab_EQ_MAX_typed" "next_lab_EQ_MAX";
val _ = emit "next_lab_thm_typed" "next_lab_thm";
val _ = emit "stack_alloc_lab_pres_typed" "stack_alloc_lab_pres";
val _ = emit "make_init_def_typed" "make_init_def";
val _ = emit "make_init_semantics_typed" "make_init_semantics";
val _ = emit "prog_comp_lambda_typed" "prog_comp_lambda";
val _ = emit "ALOOKUP_prog_comp_typed" "ALOOKUP_prog_comp";
val _ = emit "FST_prog_comp_typed" "FST_prog_comp";
val _ = emit "find_code_regs_SUBMAP_typed" "find_code_regs_SUBMAP";
val _ = emit "get_labels_comp_typed" "get_labels_comp";
val _ = emit "loc_check_compile_typed" "loc_check_compile";
val _ = emit "lookup_fromAList_prog_comp_typed" "lookup_fromAList_prog_comp";
val _ = emit "bit_length_eq_1_typed" "bit_length_eq_1";
val _ = emit "bit_length_LESS_EQ_dimindex_typed" "bit_length_LESS_EQ_dimindex";
val _ = emit "bit_length_minus_1_typed" "bit_length_minus_1";
val _ = emit "bit_length_thm_typed" "bit_length_thm";
val _ = emit "bytes_in_word_word_shift_typed" "bytes_in_word_word_shift";
val _ = emit "bytes_in_word_word_shift_n2w_typed" "bytes_in_word_word_shift_n2w";
val _ = emit "get_bits_def_typed" "get_bits_def";
val _ = emit "good_dimindex_byte_aligned_eq_typed" "good_dimindex_byte_aligned_eq";
val _ = emit "lsl_lsr_typed" "lsl_lsr";
val _ = emit "select_eq_select_0_typed" "select_eq_select_0";
val _ = emit "select_lower_lemma_typed" "select_lower_lemma";
val _ = emit "shift_to_zero_word_msb_typed" "shift_to_zero_word_msb";
val _ = emit "word_shift_not_0_typed" "word_shift_not_0";
val _ = emit "word_and_one_eq_0_iff_typed" "word_and_one_eq_0_iff";
val _ = emit "word_msb_IFF_lsr_EQ_0_typed" "word_msb_IFF_lsr_EQ_0";
