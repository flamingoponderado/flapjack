(* Typed source declarations for word_gcFunctions (task 148). *)
load "preamble";
load "word_gcFunctionsTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_gcFunctionsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_gcFunctions",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_gcFunctions")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_gcFunctions")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "bytes_in_word_mul_eq_shift_typed" "bytes_in_word_mul_eq_shift";
val _ = emit "decode_length_def_typed" "decode_length_def";
val _ = emit "glob_real_def_typed" "glob_real_def";
val _ = emit "is_ref_header_def_typed" "is_ref_header_def";
val _ = emit "memcpy_def_typed" "memcpy_def";
val _ = emit "new_trig_def_typed" "new_trig_def";
val _ = emit "ptr_to_addr_def_typed" "ptr_to_addr_def";
val _ = emit "refs_to_addresses_def_typed" "refs_to_addresses_def";
val _ = emit "shift_length_has_fp_ops_typed" "shift_length_has_fp_ops";
val _ = emit "update_addr_def_typed" "update_addr_def";
val _ = emit "word_full_gc_def_typed" "word_full_gc_def";
val _ = emit "word_gc_fun_def_typed" "word_gc_fun_def";
val _ = emit "word_gc_fun_assum_def_typed" "word_gc_fun_assum_def";
val _ = emit "word_gc_move_def_typed" "word_gc_move_def";
val _ = emit "word_gc_move_list_def_typed" "word_gc_move_list_def";
val _ = emit "word_gc_move_loop_def_typed" "word_gc_move_loop_def";
val _ = emit "word_gc_move_roots_def_typed" "word_gc_move_roots_def";
val _ = emit "word_gen_gc_def_typed" "word_gen_gc_def";
val _ = emit "word_gen_gc_can_do_partial_def_typed" "word_gen_gc_can_do_partial_def";
val _ = emit "word_gen_gc_move_def_typed" "word_gen_gc_move_def";
val _ = emit "word_gen_gc_move_data_def_typed" "word_gen_gc_move_data_def";
val _ = emit "word_gen_gc_move_list_def_typed" "word_gen_gc_move_list_def";
val _ = emit "word_gen_gc_move_loop_def_typed" "word_gen_gc_move_loop_def";
val _ = emit "word_gen_gc_move_refs_def_typed" "word_gen_gc_move_refs_def";
val _ = emit "word_gen_gc_move_roots_def_typed" "word_gen_gc_move_roots_def";
val _ = emit "word_gen_gc_partial_def_typed" "word_gen_gc_partial_def";
val _ = emit "word_gen_gc_partial_full_def_typed" "word_gen_gc_partial_full_def";
val _ = emit "word_gen_gc_partial_move_def_typed" "word_gen_gc_partial_move_def";
val _ = emit "word_gen_gc_partial_move_data_def_typed" "word_gen_gc_partial_move_data_def";
val _ = emit "word_gen_gc_partial_move_list_def_typed" "word_gen_gc_partial_move_list_def";
val _ = emit "word_gen_gc_partial_move_list_append_typed" "word_gen_gc_partial_move_list_append";
val _ = emit "word_gen_gc_partial_move_list_suc_typed" "word_gen_gc_partial_move_list_suc";
val _ = emit "word_gen_gc_partial_move_list_zero_typed" "word_gen_gc_partial_move_list_zero";
val _ = emit "word_gen_gc_partial_move_ref_list_def_typed" "word_gen_gc_partial_move_ref_list_def";
val _ = emit "word_gen_gc_partial_move_roots_def_typed" "word_gen_gc_partial_move_roots_def";
val _ = emit "word_or_eq_0_typed" "word_or_eq_0";
val _ = emit "glob_real_has_fp_ops_typed" "glob_real_has_fp_ops";
val _ = emit "word_full_gc_has_fp_ops_typed" "word_full_gc_has_fp_ops";
val _ = emit "word_gc_fun_assum_has_fp_ops_typed" "word_gc_fun_assum_has_fp_ops";
val _ = emit "word_gc_fun_has_fp_ops_typed" "word_gc_fun_has_fp_ops";
val _ = emit "word_gc_move_list_has_fp_ops_typed" "word_gc_move_list_has_fp_ops";
val _ = emit "word_gc_move_loop_has_fp_ops_typed" "word_gc_move_loop_has_fp_ops";
val _ = emit "word_gc_move_roots_has_fp_ops_typed" "word_gc_move_roots_has_fp_ops";
val _ = emit "word_gc_move_has_fp_ops_typed" "word_gc_move_has_fp_ops";
val _ = emit "word_gen_gc_move_data_has_fp_ops_typed" "word_gen_gc_move_data_has_fp_ops";
val _ = emit "word_gen_gc_move_list_has_fp_ops_typed" "word_gen_gc_move_list_has_fp_ops";
val _ = emit "word_gen_gc_move_loop_has_fp_ops_typed" "word_gen_gc_move_loop_has_fp_ops";
val _ = emit "word_gen_gc_move_refs_has_fp_ops_typed" "word_gen_gc_move_refs_has_fp_ops";
val _ = emit "word_gen_gc_move_roots_has_fp_ops_typed" "word_gen_gc_move_roots_has_fp_ops";
val _ = emit "word_gen_gc_move_has_fp_ops_typed" "word_gen_gc_move_has_fp_ops";
val _ = emit "word_gen_gc_partial_full_has_fp_ops_typed" "word_gen_gc_partial_full_has_fp_ops";
val _ = emit "word_gen_gc_partial_move_data_has_fp_ops_typed" "word_gen_gc_partial_move_data_has_fp_ops";
val _ = emit "word_gen_gc_partial_move_list_has_fp_ops_typed" "word_gen_gc_partial_move_list_has_fp_ops";
val _ = emit "word_gen_gc_partial_move_ref_list_has_fp_ops_typed" "word_gen_gc_partial_move_ref_list_has_fp_ops";
val _ = emit "word_gen_gc_partial_move_roots_has_fp_ops_typed" "word_gen_gc_partial_move_roots_has_fp_ops";
val _ = emit "word_gen_gc_partial_move_has_fp_ops_typed" "word_gen_gc_partial_move_has_fp_ops";
val _ = emit "word_gen_gc_has_fp_ops_typed" "word_gen_gc_has_fp_ops";
val _ = emit "word_gc_move_roots_IMP_EVERY2_typed" "word_gc_move_roots_IMP_EVERY2";
val _ = emit "word_gen_gc_move_roots_IMP_EVERY2_typed" "word_gen_gc_move_roots_IMP_EVERY2";
val _ = emit "word_gen_gc_partial_move_roots_IMP_EVERY2_typed" "word_gen_gc_partial_move_roots_IMP_EVERY2";
val _ = emit "word_gc_IMP_EVERY2_typed" "word_gc_IMP_EVERY2";
val _ = emit "word_gc_fun_LENGTH_typed" "word_gc_fun_LENGTH";
