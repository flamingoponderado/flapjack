(* Typed source declarations for labProps (task 148). *)
load "preamble";
load "labPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble labPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="labProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by labProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of labProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "addr_add_clock_eq_typed" "addr_add_clock_eq";
val _ = emit "asm_inst_with_clock_typed" "asm_inst_with_clock";
val _ = emit "reg_imm_with_clock_typed" "reg_imm_with_clock";
val _ = emit "share_mem_op_add_clock_same_typed" "share_mem_op_add_clock_same";
val _ = emit "no_install_def_typed" "no_install_def";
val _ = emit "no_share_mem_inst_def_typed" "no_share_mem_inst_def";
val _ = emit "align_dm_def_typed" "align_dm_def";
val _ = emit "align_dm_const_typed" "align_dm_const";
val _ = emit "align_dm_with_clock_typed" "align_dm_with_clock";
val _ = emit "align_sdm_def_typed" "align_sdm_def";
val _ = emit "align_sdm_const_typed" "align_sdm_const";
val _ = emit "align_sdm_with_clock_typed" "align_sdm_with_clock";
val _ = emit "dec_clock_align_dm_typed" "dec_clock_align_dm";
val _ = emit "get_pc_value_align_dm_typed" "get_pc_value_align_dm";
val _ = emit "get_ret_Loc_align_dm_typed" "get_ret_Loc_align_dm";
val _ = emit "inc_pc_align_dm_typed" "inc_pc_align_dm";
val _ = emit "share_mem_op_align_dm_simp_typed" "share_mem_op_align_dm_simp";
val _ = emit "upd_pc_align_dm_typed" "upd_pc_align_dm";
val _ = emit "evaluate_align_dm_typed" "evaluate_align_dm";
val _ = emit "implements_align_dm_typed" "implements_align_dm";
val _ = emit "asm_inst_align_dm_typed" "asm_inst_align_dm";
val _ = emit "mem_load32_align_dm_typed" "mem_load32_align_dm";
val _ = emit "mem_load_byte_align_dm_typed" "mem_load_byte_align_dm";
val _ = emit "mem_op_align_dm_typed" "mem_op_align_dm";
val _ = emit "mem_store32_align_dm_typed" "mem_store32_align_dm";
val _ = emit "mem_store_byte_align_dm_typed" "mem_store_byte_align_dm";
val _ = emit "addr_align_dm_typed" "addr_align_dm";
val _ = emit "addr_align_sdm_typed" "addr_align_sdm";
val _ = emit "arith_upd_align_dm_typed" "arith_upd_align_dm";
val _ = emit "arith_upd_align_sdm_typed" "arith_upd_align_sdm";
val _ = emit "fp_upd_align_dm_typed" "fp_upd_align_dm";
val _ = emit "fp_upd_align_sdm_typed" "fp_upd_align_sdm";
val _ = emit "asm_fetch_align_dm_typed" "asm_fetch_align_dm";
val _ = emit "asm_fetch_align_sdm_typed" "asm_fetch_align_sdm";
val _ = emit "assert_align_dm_typed" "assert_align_dm";
val _ = emit "assert_align_sdm_typed" "assert_align_sdm";
val _ = emit "binop_upd_align_dm_typed" "binop_upd_align_dm";
val _ = emit "binop_upd_align_sdm_typed" "binop_upd_align_sdm";
val _ = emit "read_reg_align_dm_typed" "read_reg_align_dm";
val _ = emit "read_reg_align_sdm_typed" "read_reg_align_sdm";
val _ = emit "reg_imm_align_dm_typed" "reg_imm_align_dm";
val _ = emit "reg_imm_align_sdm_typed" "reg_imm_align_sdm";
val _ = emit "upd_mem_align_dm_typed" "upd_mem_align_dm";
val _ = emit "upd_mem_align_sdm_typed" "upd_mem_align_sdm";
val _ = emit "upd_reg_align_dm_typed" "upd_reg_align_dm";
val _ = emit "upd_reg_align_sdm_typed" "upd_reg_align_sdm";
val _ = emit "evaluate_align_sdm_typed" "evaluate_align_sdm";
val _ = emit "implements_align_sdm_typed" "implements_align_sdm";
val _ = emit "asm_inst_align_sdm_typed" "asm_inst_align_sdm";
val _ = emit "mem_load32_align_sdm_typed" "mem_load32_align_sdm";
val _ = emit "mem_load_align_sdm_typed" "mem_load_align_sdm";
val _ = emit "mem_load_byte_align_sdm_typed" "mem_load_byte_align_sdm";
val _ = emit "mem_op_align_sdm_typed" "mem_op_align_sdm";
val _ = emit "mem_store32_align_sdm_typed" "mem_store32_align_sdm";
val _ = emit "mem_store_align_sdm_typed" "mem_store_align_sdm";
val _ = emit "mem_store_byte_align_sdm_typed" "mem_store_byte_align_sdm";
val _ = emit "dec_clock_align_sdm_typed" "dec_clock_align_sdm";
val _ = emit "get_pc_value_align_sdm_typed" "get_pc_value_align_sdm";
val _ = emit "get_ret_Loc_align_sdm_typed" "get_ret_Loc_align_sdm";
val _ = emit "inc_pc_align_sdm_typed" "inc_pc_align_sdm";
val _ = emit "read_bytearray_mem_load_byte_aux_align_sdm_typed" "read_bytearray_mem_load_byte_aux_align_sdm";
val _ = emit "upd_pc_align_sdm_typed" "upd_pc_align_sdm";
val _ = emit "write_bytearray_align_sdm_typed" "write_bytearray_align_sdm";
val _ = emit "align_sdm_aligned_typed" "align_sdm_aligned";
val _ = emit "share_mem_load_align_sdm_typed" "share_mem_load_align_sdm";
val _ = emit "share_mem_op_align_sdm_simp_typed" "share_mem_op_align_sdm_simp";
val _ = emit "share_mem_store_align_sdm_typed" "share_mem_store_align_sdm";
val _ = emit "mem_load_align_dm_typed" "mem_load_align_dm";
val _ = emit "mem_store_align_dm_typed" "mem_store_align_dm";
val _ = emit "evaluate_ADD_clock_typed" "evaluate_ADD_clock";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "sec_label_ok_extract_labels_typed" "sec_label_ok_extract_labels";
val _ = emit "extract_labels_def_typed" "extract_labels_def";
val _ = emit "extract_labels_append_typed" "extract_labels_append";
val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "get_code_labels_cons_typed" "get_code_labels_cons";
val _ = emit "get_code_labels_nil_typed" "get_code_labels_nil";
val _ = emit "get_labels_def_typed" "get_labels_def";
val _ = emit "get_labels_cons_typed" "get_labels_cons";
val _ = emit "labs_of_def_typed" "labs_of_def";
val _ = emit "line_get_code_labels_def_typed" "line_get_code_labels_def";
val _ = emit "line_get_labels_def_typed" "line_get_labels_def";
val _ = emit "sec_get_code_labels_def_typed" "sec_get_code_labels_def";
val _ = emit "sec_get_labels_def_typed" "sec_get_labels_def";
val _ = emit "sec_label_ok_def_typed" "sec_label_ok_def";
val _ = emit "sec_labels_ok_def_typed" "sec_labels_ok_def";
val _ = emit "line_length_def_typed" "line_length_def";
val _ = emit "line_ok_pre_def_typed" "line_ok_pre_def";
val _ = emit "sec_ok_pre_def_typed" "sec_ok_pre_def";
val _ = emit "sec_ends_with_label_def_typed" "sec_ends_with_label_def";
val _ = emit "EVERY_sec_label_ok_typed" "EVERY_sec_label_ok";
