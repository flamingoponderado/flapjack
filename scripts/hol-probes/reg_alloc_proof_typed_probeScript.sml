(* Typed source declarations for reg_allocProof (task 148). *)
load "preamble";
load "reg_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble reg_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="reg_allocProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by reg_allocProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of reg_allocProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "check_clash_tree_INJ_typed" "check_clash_tree_INJ";
val _ = emit "check_col_INJ_typed" "check_col_INJ";
val _ = emit "check_partial_col_domain_typed" "check_partial_col_domain";
val _ = emit "check_partial_col_INJ_typed" "check_partial_col_INJ";
val _ = emit "check_partial_col_success_typed" "check_partial_col_success";
val _ = emit "domain_numset_list_delete_typed" "domain_numset_list_delete";
val _ = emit "in_clash_tree_def_typed" "in_clash_tree_def";
val _ = emit "INJ_IMG_lookup_typed" "INJ_IMG_lookup";
val _ = emit "adj_ls_sub_eqn_typed" "adj_ls_sub_eqn";
val _ = emit "coalesced_sub_typed" "coalesced_sub";
val _ = emit "degrees_sub_eqn_typed" "degrees_sub_eqn";
val _ = emit "list_case_st_typed" "list_case_st";
val _ = emit "move_related_sub_typed" "move_related_sub";
val _ = emit "Msub_eqn_typed" "Msub_eqn";
val _ = emit "Mupdate_eqn_typed" "Mupdate_eqn";
val _ = emit "node_tag_sub_eqn_typed" "node_tag_sub_eqn";
val _ = emit "st_ex_MAP_adj_ls_sub_typed" "st_ex_MAP_adj_ls_sub";
val _ = emit "st_ex_MAP_degrees_sub_typed" "st_ex_MAP_degrees_sub";
val _ = emit "st_ex_MAP_node_tag_sub_typed" "st_ex_MAP_node_tag_sub";
val _ = emit "tag_case_st_typed" "tag_case_st";
val _ = emit "update_adj_ls_eqn_typed" "update_adj_ls_eqn";
val _ = emit "update_coalesced_eqn_typed" "update_coalesced_eqn";
val _ = emit "update_degrees_eqn_typed" "update_degrees_eqn";
val _ = emit "update_move_related_eqn_typed" "update_move_related_eqn";
val _ = emit "update_node_tag_eqn_typed" "update_node_tag_eqn";
val _ = emit "assign_Atemp_tag_correct_typed" "assign_Atemp_tag_correct";
val _ = emit "assign_Atemps_correct_typed" "assign_Atemps_correct";
val _ = emit "coalesce_root_success_typed" "coalesce_root_success";
val _ = emit "good_pref_biased_pref_typed" "good_pref_biased_pref";
val _ = emit "remove_colours_frame_typed" "remove_colours_frame";
val _ = emit "remove_colours_success_typed" "remove_colours_success";
val _ = emit "check_clash_tree_domain_typed" "check_clash_tree_domain";
val _ = emit "check_clash_tree_same_dom_typed" "check_clash_tree_same_dom";
val _ = emit "check_partial_col_same_dom_typed" "check_partial_col_same_dom";
val _ = emit "INJ_COMPOSE_IMAGE_typed" "INJ_COMPOSE_IMAGE";
val _ = emit "TWOxDIV2_typed" "TWOxDIV2";
val _ = emit "clique_insert_edge_succeeds_typed" "clique_insert_edge_succeeds";
val _ = emit "extend_clique_succeeds_typed" "extend_clique_succeeds";
val _ = emit "extend_graph_succeeds_typed" "extend_graph_succeeds";
val _ = emit "mk_graph_succeeds_typed" "mk_graph_succeeds";
val _ = emit "mk_tags_succeeds_typed" "mk_tags_succeeds";
val _ = emit "extract_color_succeeds_typed" "extract_color_succeeds";
val _ = emit "colouring_satisfactory_cliques_typed" "colouring_satisfactory_cliques";
val _ = emit "colouring_satisfactory_subgraph_typed" "colouring_satisfactory_subgraph";
val _ = emit "no_clash_colouring_satisfactory_typed" "no_clash_colouring_satisfactory";
val _ = emit "do_reg_alloc_correct_typed" "do_reg_alloc_correct";
val _ = emit "reg_alloc_correct_typed" "reg_alloc_correct";
val _ = emit "insert_edge_succeeds_typed" "insert_edge_succeeds";
val _ = emit "list_insert_edge_succeeds_typed" "list_insert_edge_succeeds";
val _ = emit "sorted_insert_correct_typed" "sorted_insert_correct";
val _ = emit "sorted_mem_correct_typed" "sorted_mem_correct";
val _ = emit "colouring_satisfactory_def_typed" "colouring_satisfactory_def";
val _ = emit "good_neg_pref_def_typed" "good_neg_pref_def";
val _ = emit "good_pref_def_typed" "good_pref_def";
val _ = emit "good_ra_state_def_typed" "good_ra_state_def";
val _ = emit "has_edge_def_typed" "has_edge_def";
val _ = emit "hide_def_typed" "hide_def";
val _ = emit "is_clique_def_typed" "is_clique_def";
val _ = emit "is_subgraph_def_typed" "is_subgraph_def";
val _ = emit "is_subgraph_refl_typed" "is_subgraph_refl";
val _ = emit "is_subgraph_trans_typed" "is_subgraph_trans";
val _ = emit "no_clash_def_typed" "no_clash_def";
val _ = emit "undirected_def_typed" "undirected_def";
val _ = emit "mk_bij_aux_wf_typed" "mk_bij_aux_wf";
val _ = emit "mk_graph_check_clash_tree_typed" "mk_graph_check_clash_tree";
val _ = emit "sp_inverts_def_typed" "sp_inverts_def";
val _ = emit "sp_inverts_insert_typed" "sp_inverts_insert";
val _ = emit "assign_Stemp_tag_correct_typed" "assign_Stemp_tag_correct";
val _ = emit "assign_Stemps_correct_typed" "assign_Stemps_correct";
val _ = emit "good_neg_pref_neg_biased_pref_typed" "good_neg_pref_neg_biased_pref";
val _ = emit "unbound_colour_correct_typed" "unbound_colour_correct";
