(* Typed source declarations for targetProps (task 148). *)
load "preamble";
load "targetPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble targetPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="targetProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by targetProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of targetProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "asm_step_IMP_evaluate_step_find_next_typed" "asm_step_IMP_evaluate_step_find_next";
val _ = emit "asm_step_IMP_evaluate_step_typed" "asm_step_IMP_evaluate_step";
val _ = emit "target_cc_regs_callee_saved_typed" "target_cc_regs_callee_saved";
val _ = emit "target_io_regs_callee_saved_typed" "target_io_regs_callee_saved";
val _ = emit "constructed_oracles_cc_step_typed" "constructed_oracles_cc_step";
val _ = emit "constructed_oracles_ffi_step_typed" "constructed_oracles_ffi_step";
val _ = emit "encoder_correct_asm_step_target_state_rel_typed" "encoder_correct_asm_step_target_state_rel";
val _ = emit "encoder_correct_RTC_asm_step_target_state_rel_typed" "encoder_correct_RTC_asm_step_target_state_rel";
val _ = emit "evaluate_add_clock_typed" "evaluate_add_clock";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "evaluate_EQ_evaluate_lemma_typed" "evaluate_EQ_evaluate_lemma";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "find_next_interference_def_typed" "find_next_interference_def";
val _ = emit "bytes_in_memory_DIFF_typed" "bytes_in_memory_DIFF";
val _ = emit "bytes_in_memory_SUBSET_typed" "bytes_in_memory_SUBSET";
val _ = emit "ffi_entry_pcs_disjoint_def_typed" "ffi_entry_pcs_disjoint_def";
val _ = emit "shift_interfer_def_typed" "shift_interfer_def";
val _ = dt_label "interference_app_typed" "interference_app";
val _ = emit "app_post_def_typed" "app_post_def";
val _ = emit "is_ffi_app_def_typed" "is_ffi_app_def";
val _ = emit "interference_app_seq_def_typed" "interference_app_seq_def";
val _ = emit "interference_count_def_typed" "interference_count_def";
val _ = emit "interference_pos_def_typed" "interference_pos_def";
val _ = emit "next_interference_def_typed" "next_interference_def";
val _ = emit "next_interference_ccache_typed" "next_interference_ccache";
val _ = emit "next_interference_ExtCall_typed" "next_interference_ExtCall";
val _ = emit "next_interference_intro_typed" "next_interference_intro";
val _ = emit "next_interference_shift_typed" "next_interference_shift";
val _ = emit "next_interference_MappedRead_typed" "next_interference_MappedRead";
val _ = emit "next_interference_MappedWrite_typed" "next_interference_MappedWrite";
val _ = emit "next_interference_SharedMem_typed" "next_interference_SharedMem";
val _ = emit "constructed_oracles_EQ_typed" "constructed_oracles_EQ";
val _ = emit "interference_count_EQ_typed" "interference_count_EQ";
val _ = emit "interference_count_tail_typed" "interference_count_tail";
val _ = emit "interference_pos_head_typed" "interference_pos_head";
val _ = emit "interference_pos_tail_hit_typed" "interference_pos_tail_hit";
val _ = emit "interference_pos_tail_miss_typed" "interference_pos_tail_miss";
val _ = emit "interference_count_lt_typed" "interference_count_lt";
val _ = emit "interference_pos_unique_typed" "interference_pos_unique";
val _ = emit "ccache_interfer_ok_post_ccache_asm_typed" "ccache_interfer_ok_post_ccache_asm";
val _ = emit "ffi_interfer_ok_post_ffi_asm_typed" "ffi_interfer_ok_post_ffi_asm";
val _ = emit "target_cc_fp_regs_def_typed" "target_cc_fp_regs_def";
val _ = emit "target_cc_regs_def_typed" "target_cc_regs_def";
val _ = emit "target_io_fp_regs_def_typed" "target_io_fp_regs_def";
val _ = emit "target_io_regs_def_typed" "target_io_regs_def";
val _ = emit "find_next_interference_const_typed" "find_next_interference_const";
val _ = emit "next_interference_const_typed" "next_interference_const";
val _ = emit "find_next_interference_mono_typed" "find_next_interference_mono";
val _ = emit "find_next_interference_unique_typed" "find_next_interference_unique";
val _ = emit "interference_app_seq_EQ_typed" "interference_app_seq_EQ";
val _ = emit "interference_app_seq_tail_typed" "interference_app_seq_tail";
val _ = emit "interference_count_mono_typed" "interference_count_mono";
