(* Typed source declarations for linear_scan (task 148). *)
load "preamble";
load "linear_scanTheory";
open HolKernel Parse boolLib bossLib;
open preamble linear_scanTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="linear_scan",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by linear_scan")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of linear_scan")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "live_tree_typed" "live_tree";
val _ = emit "check_intervals_def_typed" "check_intervals_def";
val _ = emit "check_live_tree_def_typed" "check_live_tree_def";
val _ = emit "check_number_property_def_typed" "check_number_property_def";
val _ = emit "check_number_property_strong_def_typed" "check_number_property_strong_def";
val _ = emit "check_startlive_prop_def_typed" "check_startlive_prop_def";
val _ = emit "fix_domination_def_typed" "fix_domination_def";
val _ = emit "get_intervals_def_typed" "get_intervals_def";
val _ = emit "get_intervals_ct_def_typed" "get_intervals_ct_def";
val _ = emit "get_intervals_ct_aux_def_typed" "get_intervals_ct_aux_def";
val _ = emit "get_intervals_withlive_def_typed" "get_intervals_withlive_def";
val _ = emit "get_live_backward_def_typed" "get_live_backward_def";
val _ = emit "get_live_tree_def_typed" "get_live_tree_def";
val _ = emit "interval_intersect_def_typed" "interval_intersect_def";
val _ = emit "live_tree_registers_def_typed" "live_tree_registers_def";
val _ = emit "numset_list_add_if_def_typed" "numset_list_add_if_def";
val _ = emit "numset_list_add_if_gt_def_typed" "numset_list_add_if_gt_def";
val _ = emit "numset_list_add_if_lt_def_typed" "numset_list_add_if_lt_def";
val _ = emit "numset_list_insert_def_typed" "numset_list_insert_def";
val _ = emit "numset_list_insert_nottailrec_def_typed" "numset_list_insert_nottailrec_def";
val _ = emit "point_inside_interval_def_typed" "point_inside_interval_def";
val _ = emit "size_of_live_tree_def_typed" "size_of_live_tree_def";
val _ = dt_label "linear_scan_hidden_state_typed" "linear_scan_hidden_state";
val _ = dt_label "linear_scan_state_typed" "linear_scan_state";
val _ = emit "colors_length_def_typed" "colors_length_def";
val _ = emit "colors_sub_def_typed" "colors_sub_def";
val _ = emit "get_intervals_ct_monad_def_typed" "get_intervals_ct_monad_def";
val _ = emit "get_intervals_ct_monad_aux_def_typed" "get_intervals_ct_monad_aux_def";
val _ = emit "int_beg_length_def_typed" "int_beg_length_def";
val _ = emit "int_beg_sub_def_typed" "int_beg_sub_def";
val _ = emit "int_end_length_def_typed" "int_end_length_def";
val _ = emit "int_end_sub_def_typed" "int_end_sub_def";
val _ = emit "numset_list_add_if_gt_monad_def_typed" "numset_list_add_if_gt_monad_def";
val _ = emit "numset_list_add_if_lt_monad_def_typed" "numset_list_add_if_lt_monad_def";
val _ = emit "sorted_moves_length_def_typed" "sorted_moves_length_def";
val _ = emit "sorted_moves_sub_def_typed" "sorted_moves_sub_def";
val _ = emit "sorted_regs_length_def_typed" "sorted_regs_length_def";
val _ = emit "sorted_regs_sub_def_typed" "sorted_regs_sub_def";
val _ = emit "update_colors_def_typed" "update_colors_def";
val _ = emit "update_int_beg_def_typed" "update_int_beg_def";
val _ = emit "update_int_end_def_typed" "update_int_end_def";
val _ = emit "update_sorted_moves_def_typed" "update_sorted_moves_def";
val _ = emit "update_sorted_regs_def_typed" "update_sorted_regs_def";
val _ = emit "apply_reg_exchange_def_typed" "apply_reg_exchange_def";
val _ = emit "edges_to_adjlist_def_typed" "edges_to_adjlist_def";
val _ = emit "find_reg_exchange_def_typed" "find_reg_exchange_def";
val _ = emit "list_to_sorted_moves_def_typed" "list_to_sorted_moves_def";
val _ = emit "list_to_sorted_regs_def_typed" "list_to_sorted_regs_def";
val _ = emit "MAP_colors_def_typed" "MAP_colors_def";
val _ = emit "partition_moves_def_typed" "partition_moves_def";
val _ = emit "partition_regs_def_typed" "partition_regs_def";
val _ = emit "sort_moves_def_typed" "sort_moves_def";
val _ = emit "sort_moves_rev_def_typed" "sort_moves_rev_def";
val _ = emit "sort_regs_def_typed" "sort_regs_def";
val _ = emit "sorted_moves_to_list_def_typed" "sorted_moves_to_list_def";
val _ = emit "sorted_regs_to_list_def_typed" "sorted_regs_to_list_def";
val _ = emit "st_ex_FILTER_good_def_typed" "st_ex_FILTER_good_def";
val _ = emit "st_ex_FOLDL_def_typed" "st_ex_FOLDL_def";
val _ = emit "swap_moves_def_typed" "swap_moves_def";
val _ = emit "swap_regs_def_typed" "swap_regs_def";
val _ = emit "add_active_interval_def_typed" "add_active_interval_def";
val _ = emit "color_register_def_typed" "color_register_def";
val _ = emit "find_color_def_typed" "find_color_def";
val _ = emit "find_color_in_colornum_def_typed" "find_color_in_colornum_def";
val _ = emit "find_color_in_list_def_typed" "find_color_in_list_def";
val _ = emit "find_last_stealable_def_typed" "find_last_stealable_def";
val _ = emit "find_spill_def_typed" "find_spill_def";
val _ = emit "linear_reg_alloc_pass1_initial_state_def_typed" "linear_reg_alloc_pass1_initial_state_def";
val _ = emit "linear_reg_alloc_pass2_initial_state_def_typed" "linear_reg_alloc_pass2_initial_state_def";
val _ = emit "linear_reg_alloc_step_aux_def_typed" "linear_reg_alloc_step_aux_def";
val _ = emit "linear_reg_alloc_step_pass1_def_typed" "linear_reg_alloc_step_pass1_def";
val _ = emit "linear_reg_alloc_step_pass2_def_typed" "linear_reg_alloc_step_pass2_def";
val _ = emit "remove_inactive_intervals_def_typed" "remove_inactive_intervals_def";
val _ = emit "spill_register_def_typed" "spill_register_def";
val _ = dt_label "bijection_state_typed" "bijection_state";
val _ = dt_label "i_linear_scan_hidden_state_typed" "i_linear_scan_hidden_state";
val _ = emit "apply_bij_on_clash_tree_def_typed" "apply_bij_on_clash_tree_def";
val _ = emit "apply_bijection_def_typed" "apply_bijection_def";
val _ = emit "extract_coloration_def_typed" "extract_coloration_def";
val _ = emit "find_bijection_clash_tree_def_typed" "find_bijection_clash_tree_def";
val _ = emit "find_bijection_init_def_typed" "find_bijection_init_def";
val _ = emit "find_bijection_step_def_typed" "find_bijection_step_def";
val _ = emit "linear_reg_alloc_and_extract_coloration_def_typed" "linear_reg_alloc_and_extract_coloration_def";
val _ = emit "linear_reg_alloc_intervals_def_typed" "linear_reg_alloc_intervals_def";
val _ = emit "linear_scan_reg_alloc_def_typed" "linear_scan_reg_alloc_def";
val _ = emit "run_i_linear_scan_hidden_state_def_typed" "run_i_linear_scan_hidden_state_def";
val _ = emit "run_linear_reg_alloc_intervals_def_typed" "run_linear_reg_alloc_intervals_def";
val _ = emit "size_of_clash_tree_def_typed" "size_of_clash_tree_def";
