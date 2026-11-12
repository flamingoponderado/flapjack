(* Typed source declarations for word_alloc (task 148). *)
load "preamble";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_allocTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_alloc",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_alloc")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_alloc")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "canonize_moves_def_typed" "canonize_moves_def";
val _ = emit "canonize_moves_aux_def_typed" "canonize_moves_aux_def";
val _ = emit "get_delta_inst_def_typed" "get_delta_inst_def";
val _ = emit "get_clash_tree_def_typed" "get_clash_tree_def";
val _ = emit "get_coalescecost_def_typed" "get_coalescecost_def";
val _ = emit "apply_colour_def_typed" "apply_colour_def";
val _ = emit "every_even_colour_def_typed" "every_even_colour_def";
val _ = emit "apply_colour_exp_def_typed" "apply_colour_exp_def";
val _ = emit "big_union_def_typed" "big_union_def";
val _ = emit "get_live_exp_def_typed" "get_live_exp_def";
val _ = emit "full_ssa_cc_trans_def_typed" "full_ssa_cc_trans_def";
val _ = emit "get_forced_def_typed" "get_forced_def";
val _ = emit "get_heuristics_def_typed" "get_heuristics_def";
val _ = emit "get_prefs_def_typed" "get_prefs_def";
val _ = emit "get_stack_only_def_typed" "get_stack_only_def";
val _ = emit "get_stack_only_aux_def_typed" "get_stack_only_aux_def";
val _ = emit "add_call_def_typed" "add_call_def";
val _ = emit "heu_merge_call_def_typed" "heu_merge_call_def";
val _ = emit "add1_lhs_const_def_typed" "add1_lhs_const_def";
val _ = emit "add1_lhs_mem_def_typed" "add1_lhs_mem_def";
val _ = emit "add1_lhs_reg_def_typed" "add1_lhs_reg_def";
val _ = emit "add1_rhs_mem_def_typed" "add1_rhs_mem_def";
val _ = emit "add1_rhs_reg_def_typed" "add1_rhs_reg_def";
val _ = emit "get_heu_inst_def_typed" "get_heu_inst_def";
val _ = emit "heu_max_def_typed" "heu_max_def";
val _ = emit "heu_max_all_def_typed" "heu_max_all_def";
val _ = emit "get_heu_def_typed" "get_heu_def";
val _ = emit "get_spillcost_def_typed" "get_spillcost_def";
val _ = emit "get_writes_inst_def_typed" "get_writes_inst_def";
val _ = emit "apply_colour_imm_def_typed" "apply_colour_imm_def";
val _ = emit "apply_colour_inst_def_typed" "apply_colour_inst_def";
val _ = emit "get_live_inst_def_typed" "get_live_inst_def";
val _ = emit "remove_dead_inst_def_typed" "remove_dead_inst_def";
val _ = emit "apply_nummap_key_def_typed" "apply_nummap_key_def";
val _ = emit "apply_nummaps_key_def_typed" "apply_nummaps_key_def";
val _ = emit "limit_var_def_typed" "limit_var_def";
val _ = emit "merge_stack_sets_def_typed" "merge_stack_sets_def";
val _ = emit "oracle_colour_ok_def_typed" "oracle_colour_ok_def";
val _ = emit "get_live_def_typed" "get_live_def";
val _ = emit "numset_list_insert_def_typed" "numset_list_insert_def";
val _ = emit "get_writes_def_typed" "get_writes_def";
val _ = emit "get_reads_exp_def_typed" "get_reads_exp_def";
val _ = emit "remove_dead_def_typed" "remove_dead_def";
val _ = emit "remove_dead_prog_def_typed" "remove_dead_prog_def";
val _ = emit "ssa_cc_trans_def_typed" "ssa_cc_trans_def";
val _ = emit "fake_move_def_typed" "fake_move_def";
val _ = emit "fake_moves_def_typed" "fake_moves_def";
val _ = emit "fix_inconsistencies_def_typed" "fix_inconsistencies_def";
val _ = emit "option_lookup_def_typed" "option_lookup_def";
val _ = emit "priority_def_typed" "priority_def";
val _ = emit "force_rename_def_typed" "force_rename_def";
val _ = emit "list_next_var_rename_move_def_typed" "list_next_var_rename_move_def";
val _ = emit "loop_setup_def_typed" "loop_setup_def";
val _ = emit "mk_prio_def_typed" "mk_prio_def";
val _ = emit "ssa_reconcile_def_typed" "ssa_reconcile_def";
val _ = emit "merge_moves_def_typed" "merge_moves_def";
val _ = emit "even_list_def_typed" "even_list_def";
val _ = emit "list_next_var_rename_def_typed" "list_next_var_rename_def";
val _ = emit "next_var_rename_def_typed" "next_var_rename_def";
val _ = emit "setup_ssa_def_typed" "setup_ssa_def";
val _ = emit "ssa_cc_trans_exp_def_typed" "ssa_cc_trans_exp_def";
val _ = emit "ssa_cc_trans_inst_def_typed" "ssa_cc_trans_inst_def";
val _ = emit "select_reg_alloc_def_typed" "select_reg_alloc_def";
val _ = emit "merge_stack_only_def_typed" "merge_stack_only_def";
val _ = emit "remove_temp_stack_def_typed" "remove_temp_stack_def";
val _ = emit "total_colour_def_typed" "total_colour_def";
val _ = emit "total_colour_alt_typed" "total_colour_alt";
val _ = emit "word_alloc_def_typed" "word_alloc_def";
