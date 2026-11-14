(* Typed source declarations for word_to_stack (task 148). *)
load "preamble";
load "word_to_stackTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_to_stack",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_to_stack")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_to_stack")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "bits_to_word_def_typed" "bits_to_word_def";
val _ = emit "chunk_to_bitmap_def_typed" "chunk_to_bitmap_def";
val _ = emit "chunk_to_bits_def_typed" "chunk_to_bits_def";
val _ = emit "const_words_to_bitmap_def_typed" "const_words_to_bitmap_def";
val _ = emit "handler_slots_def_typed" "handler_slots_def";
val _ = emit "insert_bitmap_def_typed" "insert_bitmap_def";
val _ = emit "num_stack_ret_def_typed" "num_stack_ret_def";
val _ = emit "perf_rbp_def_typed" "perf_rbp_def";
val _ = emit "perf_rsp_def_typed" "perf_rsp_def";
val _ = emit "skip_free_def_typed" "skip_free_def";
val _ = emit "stack_arg_count_def_typed" "stack_arg_count_def";
val _ = emit "stack_free_def_typed" "stack_free_def";
val _ = emit "word_list_def_typed" "word_list_def";
val _ = emit "wLive_def_typed" "wLive_def";
val _ = emit "write_bitmap_def_typed" "write_bitmap_def";
val _ = emit "call_dest_def_typed" "call_dest_def";
val _ = emit "StackArgs_def_typed" "StackArgs_def";
val _ = emit "stack_move_def_typed" "stack_move_def";
val _ = emit "comp_def_typed" "comp_def";
val _ = dt_label "config_typed" "config";
val _ = emit "PopHandler_def_typed" "PopHandler_def";
val _ = emit "PushHandler_def_typed" "PushHandler_def";
val _ = emit "StackHandlerArgs_def_typed" "StackHandlerArgs_def";
val _ = emit "wInst_def_typed" "wInst_def";
val _ = emit "wRegWrite1_def_typed" "wRegWrite1_def";
val _ = emit "wRegWrite2_def_typed" "wRegWrite2_def";
val _ = emit "wStackLoad_def_typed" "wStackLoad_def";
val _ = emit "wMoveAux_def_typed" "wMoveAux_def";
val _ = emit "wMove_def_typed" "wMove_def";
val _ = emit "wMoveSingle_def_typed" "wMoveSingle_def";
val _ = emit "perf_call_prefix_def_typed" "perf_call_prefix_def";
val _ = emit "perf_call_suffix_def_typed" "perf_call_suffix_def";
val _ = emit "compile_prog_def_typed" "compile_prog_def";
val _ = emit "compile_word_to_stack_def_typed" "compile_word_to_stack_def";
val _ = emit "copy_ret_aux_def_typed" "copy_ret_aux_def";
val _ = emit "copy_ret_def_typed" "copy_ret_def";
val _ = emit "SeqStackFree_def_typed" "SeqStackFree_def";
val _ = emit "wShareInst_def_typed" "wShareInst_def";
val _ = emit "wStackStore_def_typed" "wStackStore_def";
val _ = emit "raise_stub_def_typed" "raise_stub_def";
val _ = emit "store_consts_stub_def_typed" "store_consts_stub_def";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "stub_names_def_typed" "stub_names_def";
val _ = emit "format_var_def_typed" "format_var_def";
val _ = emit "wReg1_def_typed" "wReg1_def";
val _ = emit "wReg2_def_typed" "wReg2_def";
