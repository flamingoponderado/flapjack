(* Typed source declarations for data_to_word (task 148). *)
load "preamble";
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
open preamble data_to_wordTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="data_to_word",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by data_to_word")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of data_to_word")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "conf_ok_def_typed" "conf_ok_def";
val _ = dt_label "config_typed" "config";
val _ = dt_label "gc_kind_typed" "gc_kind";
val _ = emit "get_gen_size_def_typed" "get_gen_size_def";
val _ = emit "shift_length_def_typed" "shift_length_def";
val _ = emit "small_shift_length_def_typed" "small_shift_length_def";
val _ = emit "max_heap_limit_def_typed" "max_heap_limit_def";
val _ = emit "get_lowerbits_def_typed" "get_lowerbits_def";
val _ = emit "make_byte_header_def_typed" "make_byte_header_def";
val _ = emit "all_ones_def_typed" "all_ones_def";
val _ = emit "maxout_bits_def_typed" "maxout_bits_def";
val _ = emit "ptr_bits_def_typed" "ptr_bits_def";
val _ = emit "small_int_def_typed" "small_int_def";
val _ = emit "Smallnum_def_typed" "Smallnum_def";
val _ = emit "write_bytes_def_typed" "write_bytes_def";
val _ = emit "adjust_var_def_typed" "adjust_var_def";
val _ = emit "adjust_set_def_typed" "adjust_set_def";
val _ = emit "adjust_sets_def_typed" "adjust_sets_def";
val _ = emit "make_header_def_typed" "make_header_def";
val _ = emit "encode_header_def_typed" "encode_header_def";
val _ = emit "FromList_location_def_typed" "FromList_location_def";
val _ = emit "FromList1_location_def_typed" "FromList1_location_def";
val _ = emit "RefByte_location_def_typed" "RefByte_location_def";
val _ = emit "RefArray_location_def_typed" "RefArray_location_def";
val _ = emit "Replicate_location_def_typed" "Replicate_location_def";
val _ = emit "AnyArith_location_def_typed" "AnyArith_location_def";
val _ = emit "Add_location_def_typed" "Add_location_def";
val _ = emit "Sub_location_def_typed" "Sub_location_def";
val _ = emit "Mul_location_def_typed" "Mul_location_def";
val _ = emit "Div_location_def_typed" "Div_location_def";
val _ = emit "Mod_location_def_typed" "Mod_location_def";
val _ = emit "Compare1_location_def_typed" "Compare1_location_def";
val _ = emit "Compare_location_def_typed" "Compare_location_def";
val _ = emit "Equal1_location_def_typed" "Equal1_location_def";
val _ = emit "Equal_location_def_typed" "Equal_location_def";
val _ = emit "LongDiv1_location_def_typed" "LongDiv1_location_def";
val _ = emit "LongDiv_location_def_typed" "LongDiv_location_def";
val _ = emit "MemCopy_location_def_typed" "MemCopy_location_def";
val _ = emit "ByteCopy_location_def_typed" "ByteCopy_location_def";
val _ = emit "ByteCopyAdd_location_def_typed" "ByteCopyAdd_location_def";
val _ = emit "ByteCopySub_location_def_typed" "ByteCopySub_location_def";
val _ = emit "ByteCopyNew_location_def_typed" "ByteCopyNew_location_def";
val _ = emit "Install_location_def_typed" "Install_location_def";
val _ = emit "InstallCode_location_def_typed" "InstallCode_location_def";
val _ = emit "InstallData_location_def_typed" "InstallData_location_def";
val _ = emit "Dummy_location_def_typed" "Dummy_location_def";
val _ = emit "Append_location_def_typed" "Append_location_def";
val _ = emit "AppendMainLoop_location_def_typed" "AppendMainLoop_location_def";
val _ = emit "AppendLenLoop_location_def_typed" "AppendLenLoop_location_def";
val _ = emit "XorLoop_location_def_typed" "XorLoop_location_def";
val _ = emit "Unused_location_def_typed" "Unused_location_def";
val _ = emit "StringCmpLoop_location_def_typed" "StringCmpLoop_location_def";
val _ = emit "Bignum_location_def_typed" "Bignum_location_def";
val _ = dt_label "word_op_type_typed" "word_op_type";
val _ = emit "lookup_word_op_def_typed" "lookup_word_op_def";
val _ = emit "stub_names_def_typed" "stub_names_def";
val _ = emit "fp_cmp_inst_def_typed" "fp_cmp_inst_def";
val _ = emit "fp_bop_inst_def_typed" "fp_bop_inst_def";
val _ = emit "fp_uop_inst_def_typed" "fp_uop_inst_def";
val _ = emit "fp_top_inst_def_typed" "fp_top_inst_def";
val _ = emit "real_addr_def_typed" "real_addr_def";
val _ = emit "GiveUp_def_typed" "GiveUp_def";
val _ = emit "ShiftVar_def_typed" "ShiftVar_def";
val _ = emit "list_Seq_def_typed" "list_Seq_def";
val _ = emit "StoreEach_def_typed" "StoreEach_def";
val _ = emit "MemEqList_def_typed" "MemEqList_def";
val _ = emit "LoadBignum_def_typed" "LoadBignum_def";
val _ = emit "WriteWord32_on_32_def_typed" "WriteWord32_on_32_def";
val _ = emit "assign_WordFromInt_def_typed" "assign_WordFromInt_def";
val _ = emit "assign_WordToInt_def_typed" "assign_WordToInt_def";
val _ = emit "assign_WordFromWord_def_typed" "assign_WordFromWord_def";
val _ = emit "LoadWord64_def_typed" "LoadWord64_def";
val _ = emit "WordShift64_on_32_def_typed" "WordShift64_on_32_def";
val _ = emit "assign_WordShiftW64_def_typed" "assign_WordShiftW64_def";
val _ = emit "WriteWord64_def_typed" "WriteWord64_def";
val _ = emit "WriteWord64_on_32_def_typed" "WriteWord64_on_32_def";
val _ = emit "WordOp64_on_32_def_typed" "WordOp64_on_32_def";
val _ = emit "assign_WordOpW64_def_typed" "assign_WordOpW64_def";
val _ = emit "assign_LengthBlock_def_typed" "assign_LengthBlock_def";
val _ = emit "assign_LessConstSmall_def_typed" "assign_LessConstSmall_def";
val _ = emit "assign_BoolTest_def_typed" "assign_BoolTest_def";
val _ = emit "assign_BoolNot_def_typed" "assign_BoolNot_def";
val _ = emit "assign_FinaliseCons_def_typed" "assign_FinaliseCons_def";
val _ = emit "assign_Length_def_typed" "assign_Length_def";
val _ = emit "assign_LengthByte_def_typed" "assign_LengthByte_def";
val _ = emit "Unit_def_typed" "Unit_def";
val _ = emit "assign_UpdateThunk_def_typed" "assign_UpdateThunk_def";
val _ = emit "arg3_def_typed" "arg3_def";
val _ = emit "real_byte_offset_def_typed" "real_byte_offset_def";
val _ = emit "assign_DerefByte_def_typed" "assign_DerefByte_def";
val _ = emit "assign_Update_def_typed" "assign_Update_def";
val _ = emit "assign_UpdateByte_def_typed" "assign_UpdateByte_def";
val _ = emit "arg2_def_typed" "arg2_def";
val _ = emit "real_offset_def_typed" "real_offset_def";
val _ = emit "assign_El_def_typed" "assign_El_def";
val _ = emit "assign_ElemAt_def_typed" "assign_ElemAt_def";
val _ = emit "arg1_def_typed" "arg1_def";
val _ = emit "assign_SetGlobalsPtr_def_typed" "assign_SetGlobalsPtr_def";
val _ = emit "assign_Global_def_typed" "assign_Global_def";
val _ = emit "assign_SetGlobal_def_typed" "assign_SetGlobal_def";
val _ = emit "assign_Const_def_typed" "assign_Const_def";
val _ = emit "AllocVar_def_typed" "AllocVar_def";
val _ = emit "SilentFFI_def_typed" "SilentFFI_def";
val _ = emit "AnyArith_call_tree_def_typed" "AnyArith_call_tree_def";
val _ = emit "getWords_def_typed" "getWords_def";
val _ = emit "StoreAnyConsts_def_typed" "StoreAnyConsts_def";
val _ = emit "lookup_mem_def_typed" "lookup_mem_def";
val _ = emit "get_Word_def_typed" "get_Word_def";
val _ = emit "make_ptr_def_typed" "make_ptr_def";
val _ = emit "part_to_words_def_typed" "part_to_words_def";
val _ = emit "parts_to_words_def_typed" "parts_to_words_def";
val _ = emit "const_parts_to_words_def_typed" "const_parts_to_words_def";
val _ = emit "byte_len_def_typed" "byte_len_def";
