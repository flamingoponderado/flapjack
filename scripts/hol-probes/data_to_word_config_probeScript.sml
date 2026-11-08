load "preamble"; load "data_to_wordTheory";
open bossLib; open HolKernel Parse; open preamble; open data_to_wordTheory;
val _ = Globals.linewidth := 1000000;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;

val _ = print_eval "shift_length" ``shift_length ^conf``;
val _ = print_eval "small_shift_length" ``small_shift_length ^conf``;
val _ = print_eval "gen_size_nil_64" ``(get_gen_size [] : 64 word)``;
val _ = print_eval "gen_size_ten_64" ``(get_gen_size [10; 20] : 64 word)``;
val _ = print_eval "gen_size_overflow_64" ``(get_gen_size [2305843009213693952] : 64 word)``;
val _ = print_eval "gen_size_three_32" ``(get_gen_size [3] : 32 word)``;

(* Unrecognized assignment cases fall through to (Skip,l). *)
val _ = print_eval "assign_greater_fallback" ``(assign ^conf 4 7 3 (closLang$IntOp Greater) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_greater_eq_fallback" ``(assign ^conf 4 7 3 (closLang$IntOp GreaterEq) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_alloc_global_fallback" ``(assign ^conf 4 7 3 (closLang$GlobOp AllocGlobal) [] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_concat_byte_vec_fallback" ``(assign ^conf 4 7 3 (closLang$MemOp ConcatByteVec) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_from_list_byte_fallback" ``(assign ^conf 4 7 3 (closLang$MemOp FromListByte) [1] NONE : 64 wordLang$prog # num)``;

val _ = (print "real_addr_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.real_addr_def); print "\n");
val _ = print_eval "real_addr_sub_64" ``(real_addr (^conf with <|tag_bits := 0; len_bits := 0; pad_bits := 1|>) 4 : 64 wordLang$exp)``;
val _ = print_eval "real_addr_right_64" ``(real_addr ^conf 4 : 64 wordLang$exp)``;
val _ = print_eval "real_addr_both_64" ``(real_addr (^conf with pad_bits := 0) 4 : 64 wordLang$exp)``;
val _ = (print "shift_var_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.ShiftVar_def); print "\n");
val _ = (print "give_up_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.GiveUp_def); print "\n");
val _ = print_eval "shift_zero_64" ``(ShiftVar Lsl 4 0 : 64 wordLang$exp)``;
val _ = print_eval "shift_large_asr_64" ``(ShiftVar Asr 4 65 : 64 wordLang$exp)``;
val _ = print_eval "shift_large_lsl_64" ``(ShiftVar Lsl 4 64 : 64 wordLang$exp)``;
val _ = print_eval "shift_rotate_multiple_64" ``(ShiftVar Ror 4 128 : 64 wordLang$exp)``;
val _ = print_eval "shift_rotate_wrap_64" ``(ShiftVar Ror 4 67 : 64 wordLang$exp)``;
val _ = print_eval "give_up_64" ``(GiveUp : 64 wordLang$prog)``;
val _ = (print "list_seq_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.list_Seq_def); print "\n");
val _ = (print "store_each_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.StoreEach_def); print "\n");
val _ = (print "mem_eq_list_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.MemEqList_def); print "\n");
val _ = (print "silent_ffi_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.SilentFFI_def); print "\n");
val _ = (print "spt_lrnext_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl sptreeTheory.lrnext_def); print "\n");
val _ = (print "spt_to_alist_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl sptreeTheory.toAList_def); print "\n");
val _ = (print "adjust_var_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.adjust_var_def); print "\n");
val _ = (print "adjust_set_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.adjust_set_def); print "\n");
val _ = (print "adjust_sets_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.adjust_sets_def); print "\n");
val _ = (print "alloc_var_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.AllocVar_def); print "\n");
val _ = (print "assign_const_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_Const_def); print "\n");
val _ = print_eval "assign_const_negative_64" ``(assign_Const (~7) 9 3 : 64 wordLang$prog # num)``;
val _ = print_eval "assign_const_zero_64" ``(assign_Const 0 9 3 : 64 wordLang$prog # num)``;
val _ = print_eval "assign_const_positive_64" ``(assign_Const 7 9 3 : 64 wordLang$prog # num)``;
val _ = print_eval "assign_const_wrap_64" ``(assign_Const 4611686018427387904 9 3 : 64 wordLang$prog # num)``;
val _ = print_eval "assign_const_wrap_equal_64" ``(assign_Const 4611686018427387904 9 3 : 64 wordLang$prog # num) = (Assign 8 (Const 0w),9)``;
val _ = (print "arg1_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.arg1_def); print "\n");
val _ = (print "assign_set_globals_ptr_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_SetGlobalsPtr_def); print "\n");
val _ = (print "assign_global_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_Global_def); print "\n");
val _ = (print "assign_set_global_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_SetGlobal_def); print "\n");
val _ = print_eval "assign_global_64" ``(assign ^conf 4 9 3 (closLang$GlobOp (Global 2)) [] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_set_global_64" ``(assign ^conf 4 9 3 (closLang$GlobOp (SetGlobal 2)) [6] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_set_global_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$GlobOp (SetGlobal 2)) [6;7] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_set_globals_ptr_64" ``(assign ^conf 4 9 3 (closLang$GlobOp SetGlobalsPtr) [6] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_set_globals_ptr_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$GlobOp SetGlobalsPtr) [] NONE : 64 wordLang$prog # num)``;
val _ = (print "arg2_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.arg2_def); print "\n");
val _ = (print "real_offset_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.real_offset_def); print "\n");
val _ = (print "assign_el_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_El_def); print "\n");
val _ = (print "assign_elem_at_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_ElemAt_def); print "\n");
val _ = print_eval "assign_el_32" ``(assign ^conf 4 9 3 (closLang$MemOp El) [1;2] NONE : 32 wordLang$prog # num)``;
val _ = print_eval "assign_el_64" ``(assign ^conf 4 9 3 (closLang$MemOp El) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_el_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp El) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_elem_at_64" ``(assign ^conf 4 9 3 (closLang$BlockOp (ElemAt 2)) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_elem_at_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$BlockOp (ElemAt 2)) [] NONE : 64 wordLang$prog # num)``;
val _ = (print "arg3_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.arg3_def); print "\n");
val _ = (print "real_byte_offset_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.real_byte_offset_def); print "\n");
val _ = (print "assign_deref_byte_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_DerefByte_def); print "\n");
val _ = (print "assign_update_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_Update_def); print "\n");
val _ = (print "assign_update_byte_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_UpdateByte_def); print "\n");
val _ = print_eval "assign_deref_byte_64" ``(assign ^conf 4 9 3 (closLang$MemOp DerefByte) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_deref_byte_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp DerefByte) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_32" ``(assign ^conf 4 9 3 (closLang$MemOp Update) [1;2;3] NONE : 32 wordLang$prog # num)``;
val _ = print_eval "assign_update_cons_64" ``(assign ^conf 4 9 3 (closLang$MemOp UpdateCons) [1;2;3] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp Update) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_byte_64" ``(assign ^conf 4 9 3 (closLang$MemOp UpdateByte) [1;2;3] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_byte_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp UpdateByte) [] NONE : 64 wordLang$prog # num)``;
val _ = (print "unit_exp_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.Unit_def); print "\n");
val _ = (print "assign_update_thunk_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_UpdateThunk_def); print "\n");
val _ = print_eval "assign_update_thunk_pending_64" ``(assign ^conf 4 9 3 (closLang$ThunkOp (UpdateThunk NotEvaluated)) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_thunk_done_64" ``(assign ^conf 4 9 3 (closLang$ThunkOp (UpdateThunk Evaluated)) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_thunk_header_failure_64" ``(assign (^conf with len_size := 0) 4 9 3 (closLang$ThunkOp (UpdateThunk Evaluated)) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_update_thunk_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$ThunkOp (UpdateThunk Evaluated)) [1] NONE : 64 wordLang$prog # num)``;
val _ = (print "assign_bool_not_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_BoolNot_def); print "\n");
val _ = (print "assign_finalise_cons_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_FinaliseCons_def); print "\n");
val _ = (print "assign_length_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_Length_def); print "\n");
val _ = (print "assign_length_byte_def_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl data_to_wordTheory.assign_LengthByte_def); print "\n");
val _ = print_eval "assign_bool_not_64" ``(assign ^conf 4 9 3 (closLang$BlockOp BoolNot) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_bool_not_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$BlockOp BoolNot) [] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_finalise_cons_64" ``(assign ^conf 4 9 3 (closLang$MemOp FinaliseCons) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_finalise_cons_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp FinaliseCons) [1;2] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_length_64" ``(assign ^conf 4 9 3 (closLang$MemOp Length) [1] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "assign_length_byte_32" ``(assign ^conf 4 9 3 (closLang$MemOp LengthByte) [1] NONE : 32 wordLang$prog # num)``;
val _ = print_eval "assign_length_byte_bad_arity_64" ``(assign ^conf 4 9 3 (closLang$MemOp LengthByte) [] NONE : 64 wordLang$prog # num)``;
val _ = print_eval "store_each_64" ``(StoreEach 2 [4;6] 8w : 64 wordLang$prog)``;
val _ = print_eval "mem_eq_list_64" ``(MemEqList 8w [3w;7w] : 64 wordLang$prog)``;
val _ = print_eval "silent_ffi_off_64" ``(SilentFFI ^conf 3 (LN,LN) : 64 wordLang$prog)``;
val _ = print_eval "silent_ffi_on_64" ``(SilentFFI (^conf with call_empty_ffi := T) 3 (LN,LN) : 64 wordLang$prog)``;
val _ = (print "fp_cmp_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl fp_cmp_inst_def); print "\n");
val _ = (print "fp_bop_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl fp_bop_inst_def); print "\n");
val _ = (print "fp_uop_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl fp_uop_inst_def); print "\n");
val _ = (print "fp_top_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl fp_top_inst_def); print "\n");
