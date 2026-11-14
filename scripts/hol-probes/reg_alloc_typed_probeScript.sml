(* Typed source declarations for reg_alloc (task 148). *)
load "preamble";
load "reg_allocTheory";
open HolKernel Parse boolLib bossLib;
open preamble reg_allocTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="reg_alloc",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by reg_alloc")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of reg_alloc")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "convention_partitions_typed" "convention_partitions";
val _ = emit "is_alloc_var_def_typed" "is_alloc_var_def";
val _ = emit "is_phy_var_def_typed" "is_phy_var_def";
val _ = emit "is_stack_var_def_typed" "is_stack_var_def";
val _ = emit "adj_ls_length_def_typed" "adj_ls_length_def";
val _ = emit "adj_ls_sub_def_typed" "adj_ls_sub_def";
val _ = emit "coalesced_length_def_typed" "coalesced_length_def";
val _ = emit "coalesced_sub_def_typed" "coalesced_sub_def";
val _ = emit "degrees_length_def_typed" "degrees_length_def";
val _ = emit "degrees_sub_def_typed" "degrees_sub_def";
val _ = emit "get_adj_ls_def_typed" "get_adj_ls_def";
val _ = emit "get_avail_moves_wl_def_typed" "get_avail_moves_wl_def";
val _ = emit "get_coalesced_def_typed" "get_coalesced_def";
val _ = emit "get_degrees_def_typed" "get_degrees_def";
val _ = emit "get_dim_def_typed" "get_dim_def";
val _ = emit "get_freeze_wl_def_typed" "get_freeze_wl_def";
val _ = emit "get_move_related_def_typed" "get_move_related_def";
val _ = emit "get_node_tag_def_typed" "get_node_tag_def";
val _ = emit "get_simp_wl_def_typed" "get_simp_wl_def";
val _ = emit "get_spill_wl_def_typed" "get_spill_wl_def";
val _ = emit "get_stack_def_typed" "get_stack_def";
val _ = emit "get_unavail_moves_wl_def_typed" "get_unavail_moves_wl_def";
val _ = emit "move_related_length_def_typed" "move_related_length_def";
val _ = emit "move_related_sub_def_typed" "move_related_sub_def";
val _ = emit "node_tag_length_def_typed" "node_tag_length_def";
val _ = emit "node_tag_sub_def_typed" "node_tag_sub_def";
val _ = emit "set_adj_ls_def_typed" "set_adj_ls_def";
val _ = emit "set_avail_moves_wl_def_typed" "set_avail_moves_wl_def";
val _ = emit "set_coalesced_def_typed" "set_coalesced_def";
val _ = emit "set_degrees_def_typed" "set_degrees_def";
val _ = emit "set_dim_def_typed" "set_dim_def";
val _ = emit "set_freeze_wl_def_typed" "set_freeze_wl_def";
val _ = emit "set_move_related_def_typed" "set_move_related_def";
val _ = emit "set_node_tag_def_typed" "set_node_tag_def";
val _ = emit "set_simp_wl_def_typed" "set_simp_wl_def";
val _ = emit "set_spill_wl_def_typed" "set_spill_wl_def";
val _ = emit "set_stack_def_typed" "set_stack_def";
val _ = emit "set_unavail_moves_wl_def_typed" "set_unavail_moves_wl_def";
val _ = emit "update_adj_ls_def_typed" "update_adj_ls_def";
val _ = emit "update_coalesced_def_typed" "update_coalesced_def";
val _ = emit "update_degrees_def_typed" "update_degrees_def";
val _ = emit "update_move_related_def_typed" "update_move_related_def";
val _ = emit "update_node_tag_def_typed" "update_node_tag_def";
val _ = emit "bg_ok_def_typed" "bg_ok_def";
val _ = emit "biased_pref_def_typed" "biased_pref_def";
val _ = emit "do_alloc1_def_typed" "do_alloc1_def";
val _ = emit "do_coalesce_def_typed" "do_coalesce_def";
val _ = emit "do_coalesce_real_def_typed" "do_coalesce_real_def";
val _ = emit "do_freeze_def_typed" "do_freeze_def";
val _ = emit "do_prefreeze_def_typed" "do_prefreeze_def";
val _ = emit "do_reg_alloc_def_typed" "do_reg_alloc_def";
val _ = emit "do_simplify_def_typed" "do_simplify_def";
val _ = emit "do_spill_def_typed" "do_spill_def";
val _ = emit "do_step_def_typed" "do_step_def";
val _ = emit "do_upd_coalesce_def_typed" "do_upd_coalesce_def";
val _ = emit "init_alloc1_heu_def_typed" "init_alloc1_heu_def";
val _ = emit "reg_alloc_def_typed" "reg_alloc_def";
val _ = emit "reg_alloc_aux_def_typed" "reg_alloc_aux_def";
val _ = emit "revive_moves_def_typed" "revive_moves_def";
val _ = emit "rpt_do_step_def_typed" "rpt_do_step_def";
val _ = emit "unspill_def_typed" "unspill_def";
val _ = dt_label "algorithm_typed" "algorithm";
val _ = dt_label "ra_state_typed" "ra_state";
val _ = dt_label "tag_typed" "tag";
val _ = dt_label "clash_tree_typed" "clash_tree";
val _ = emit "check_clash_tree_def_typed" "check_clash_tree_def";
val _ = emit "check_col_def_typed" "check_col_def";
val _ = emit "check_partial_col_def_typed" "check_partial_col_def";
val _ = emit "numset_list_delete_def_typed" "numset_list_delete_def";
val _ = emit "canonize_move_def_typed" "canonize_move_def";
val _ = emit "coalesce_parent_def_typed" "coalesce_parent_def";
val _ = emit "consistency_ok_def_typed" "consistency_ok_def";
val _ = emit "inc_deg_def_typed" "inc_deg_def";
val _ = emit "reset_move_related_def_typed" "reset_move_related_def";
val _ = emit "st_ex_FIRST_def_typed" "st_ex_FIRST_def";
val _ = emit "assign_Atemp_tag_def_typed" "assign_Atemp_tag_def";
val _ = emit "assign_Atemps_def_typed" "assign_Atemps_def";
val _ = emit "first_match_col_def_typed" "first_match_col_def";
val _ = emit "remove_colours_def_typed" "remove_colours_def";
val _ = emit "considered_var_def_typed" "considered_var_def";
val _ = emit "deg_or_inf_def_typed" "deg_or_inf_def";
val _ = emit "is_Atemp_def_typed" "is_Atemp_def";
val _ = emit "is_Fixed_def_typed" "is_Fixed_def";
val _ = emit "is_Fixed_k_def_typed" "is_Fixed_k_def";
val _ = emit "handle_Fail_def_typed" "handle_Fail_def";
val _ = emit "handle_Subscript_def_typed" "handle_Subscript_def";
val _ = emit "raise_Fail_def_typed" "raise_Fail_def";
val _ = emit "raise_Subscript_def_typed" "raise_Subscript_def";
val _ = dt_label "state_exn_typed" "state_exn";
val _ = emit "clique_insert_edge_def_typed" "clique_insert_edge_def";
val _ = emit "extend_clique_def_typed" "extend_clique_def";
val _ = emit "extend_graph_def_typed" "extend_graph_def";
val _ = emit "init_ra_state_def_typed" "init_ra_state_def";
val _ = emit "insert_edge_def_typed" "insert_edge_def";
val _ = emit "list_insert_edge_def_typed" "list_insert_edge_def";
val _ = emit "mk_graph_def_typed" "mk_graph_def";
val _ = emit "mk_tags_def_typed" "mk_tags_def";
val _ = dt_label "ira_state_typed" "ira_state";
val _ = emit "run_ira_state_def_typed" "run_ira_state_def";
val _ = emit "coalesce_root_def_typed" "coalesce_root_def";
val _ = emit "extract_color_def_typed" "extract_color_def";
val _ = emit "full_consistency_ok_def_typed" "full_consistency_ok_def";
val _ = emit "update_move_def_typed" "update_move_def";
val _ = emit "moves_to_sp_def_typed" "moves_to_sp_def";
val _ = emit "pri_move_insert_def_typed" "pri_move_insert_def";
val _ = emit "resort_moves_def_typed" "resort_moves_def";
val _ = emit "undir_move_insert_def_typed" "undir_move_insert_def";
val _ = emit "list_remap_def_typed" "list_remap_def";
val _ = emit "mk_bij_def_typed" "mk_bij_def";
val _ = emit "mk_bij_aux_def_typed" "mk_bij_aux_def";
val _ = emit "safe_div_def_typed" "safe_div_def";
val _ = emit "smerge_def_typed" "smerge_def";
val _ = emit "sort_moves_def_typed" "sort_moves_def";
val _ = emit "sorted_insert_def_typed" "sorted_insert_def";
val _ = emit "sorted_mem_def_typed" "sorted_mem_def";
val _ = emit "sp_default_def_typed" "sp_default_def";
val _ = emit "st_ex_list_MAX_deg_def_typed" "st_ex_list_MAX_deg_def";
val _ = emit "st_ex_list_MIN_cost_def_typed" "st_ex_list_MIN_cost_def";
val _ = emit "is_not_coalesced_def_typed" "is_not_coalesced_def";
val _ = emit "split_degree_def_typed" "split_degree_def";
val _ = emit "st_ex_FILTER_def_typed" "st_ex_FILTER_def";
val _ = emit "st_ex_FOREACH_def_typed" "st_ex_FOREACH_def";
val _ = emit "st_ex_MAP_def_typed" "st_ex_MAP_def";
val _ = emit "st_ex_PARTITION_def_typed" "st_ex_PARTITION_def";
val _ = emit "assign_Stemp_tag_def_typed" "assign_Stemp_tag_def";
val _ = emit "assign_Stemps_def_typed" "assign_Stemps_def";
val _ = emit "neg_biased_pref_def_typed" "neg_biased_pref_def";
val _ = emit "neg_first_match_col_def_typed" "neg_first_match_col_def";
val _ = emit "extract_tag_def_typed" "extract_tag_def";
val _ = emit "tag_col_def_typed" "tag_col_def";
val _ = emit "unbound_colour_def_typed" "unbound_colour_def";
val _ = emit "add_freeze_wl_def_typed" "add_freeze_wl_def";
val _ = emit "add_simp_wl_def_typed" "add_simp_wl_def";
val _ = emit "add_spill_wl_def_typed" "add_spill_wl_def";
val _ = emit "add_unavail_moves_wl_def_typed" "add_unavail_moves_wl_def";
val _ = emit "dec_deg_def_typed" "dec_deg_def";
val _ = emit "dec_degree_def_typed" "dec_degree_def";
val _ = emit "push_stack_def_typed" "push_stack_def";
val _ = emit "respill_def_typed" "respill_def";
