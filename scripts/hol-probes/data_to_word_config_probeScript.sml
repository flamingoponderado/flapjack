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
val _ = print_eval "store_each_64" ``(StoreEach 2 [4;6] 8w : 64 wordLang$prog)``;
val _ = print_eval "mem_eq_list_64" ``(MemEqList 8w [3w;7w] : 64 wordLang$prog)``;
val _ = print_eval "silent_ffi_off_64" ``(SilentFFI ^conf 3 (LN,LN) : 64 wordLang$prog)``;
val _ = print_eval "silent_ffi_on_64" ``(SilentFFI (^conf with call_empty_ffi := T) 3 (LN,LN) : 64 wordLang$prog)``;
