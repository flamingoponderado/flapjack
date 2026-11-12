(* Typed source declarations for lab_to_target (task 148). *)
load "preamble";
load "lab_to_targetTheory";
open HolKernel Parse boolLib bossLib;
open preamble lab_to_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="lab_to_target",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by lab_to_target")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of lab_to_target")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "config_typed" "config";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "compile_lab_def_typed" "compile_lab_def";
val _ = emit "enc_line_def_typed" "enc_line_def";
val _ = emit "enc_sec_def_typed" "enc_sec_def";
val _ = emit "enc_sec_list_def_typed" "enc_sec_list_def";
val _ = emit "ffi_offset_def_typed" "ffi_offset_def";
val _ = emit "lab_inst_def_typed" "lab_inst_def";
val _ = emit "compute_labels_alt_def_typed" "compute_labels_alt_def";
val _ = emit "section_labels_def_typed" "section_labels_def";
val _ = emit "cbw_to_asm_def_typed" "cbw_to_asm_def";
val _ = emit "add_nop_def_typed" "add_nop_def";
val _ = emit "get_symbols_def_typed" "get_symbols_def";
val _ = emit "line_ok_light_def_typed" "line_ok_light_def";
val _ = emit "pad_bytes_def_typed" "pad_bytes_def";
val _ = emit "pad_code_def_typed" "pad_code_def";
val _ = emit "pad_code_MAP_typed" "pad_code_MAP";
val _ = emit "pad_section_def_typed" "pad_section_def";
val _ = emit "sec_length_def_typed" "sec_length_def";
val _ = emit "sec_ok_light_def_typed" "sec_ok_light_def";
val _ = emit "find_pos_def_typed" "find_pos_def";
val _ = emit "get_ffi_index_def_typed" "get_ffi_index_def";
val _ = emit "get_jump_offset_def_typed" "get_jump_offset_def";
val _ = emit "get_label_def_typed" "get_label_def";
val _ = emit "get_zero_labs_acc_def_typed" "get_zero_labs_acc_def";
val _ = emit "line_bytes_def_typed" "line_bytes_def";
val _ = emit "line_get_zero_labs_acc_def_typed" "line_get_zero_labs_acc_def";
val _ = emit "prog_to_bytes_def_typed" "prog_to_bytes_def";
val _ = emit "prog_to_bytes_MAP_typed" "prog_to_bytes_MAP";
val _ = emit "remove_labels_def_typed" "remove_labels_def";
val _ = emit "remove_labels_loop_def_typed" "remove_labels_loop_def";
val _ = emit "sec_get_zero_labs_acc_def_typed" "sec_get_zero_labs_acc_def";
val _ = emit "zero_labs_acc_exist_def_typed" "zero_labs_acc_exist_def";
val _ = emit "zero_labs_acc_of_def_typed" "zero_labs_acc_of_def";
val _ = emit "enc_lines_again_def_typed" "enc_lines_again_def";
val _ = emit "enc_secs_again_def_typed" "enc_secs_again_def";
val _ = emit "lines_upd_lab_len_def_typed" "lines_upd_lab_len_def";
val _ = emit "upd_lab_len_def_typed" "upd_lab_len_def";
val _ = dt_label "shmem_info_num_typed" "shmem_info_num";
val _ = emit "find_ffi_names_def_typed" "find_ffi_names_def";
val _ = emit "get_memop_info_def_typed" "get_memop_info_def";
val _ = emit "get_shmem_info_def_typed" "get_shmem_info_def";
val _ = emit "list_add_if_fresh_def_typed" "list_add_if_fresh_def";
