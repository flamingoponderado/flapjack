(* Direct original linear_scan monadic state definitions on a concrete hidden
   state; CakeML remains read-only. Each row prints the full EVAL result. *)
load "bossLib";
load "preamble";
load "linear_scanTheory";
open bossLib HolKernel Parse preamble ml_monadBaseTheory linear_scanTheory;
(* Print sparse trees as raw LN/LS/BN/BS constructors. *)
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val s0 = ``<| colors := [7;8;9;6]; int_beg := [3i;1;2;0]; int_end := [5i;4;6;3];
             sorted_regs := [0;1;2;3]; sorted_moves := [(5,(1,2)); (2,(0,3)); (4,(2,2))] |>``;
val st0 = ``<| active := [(-1i,1); (2,2)]; colorpool := [4]; phyregs := LN;
              colornum := 0; colormax := 2; stacknum := 10 |>``;
val _ = print_eval "add_if_lt_monad" ``numset_list_add_if_lt_monad [0;1;3] (2:int) ^s0``;
val _ = print_eval "add_if_gt_monad" ``numset_list_add_if_gt_monad [0;1;3] (4:int) ^s0``;
val _ = print_eval "add_if_subscript" ``numset_list_add_if_gt_monad [9] (4:int) ^s0``;
val _ = print_eval "intervals_ct_monad"
  ``get_intervals_ct_monad (Seq (Delta [1] [2]) (Branch (SOME (insert 3 () LN)) (Delta [] [1]) (Set (insert 2 () LN))))
      (^s0 with <| int_beg := [1;1;1;1]; int_end := [1;1;1;1] |>)``;
val _ = print_eval "remove_inactive" ``remove_inactive_intervals 0 ^st0 ^s0``;
val _ = print_eval "add_active" ``add_active_interval (3i,1) [(1,0); (5,2)]``;
val _ = print_eval "find_color_in_list" ``find_color_in_list [1;2;3] (insert 1 () LN)``;
val _ = print_eval "find_color_pool" ``find_color ^st0 (insert 1 () LN)``;
val _ = print_eval "find_color_colornum" ``find_color ^st0 (insert 4 () LN)``;
val _ = print_eval "spill" ``spill_register ^st0 2 ^s0``;
val _ = print_eval "color_phy" ``color_register ^st0 2 5 7 ^s0``;
val _ = print_eval "color_virt" ``color_register ^st0 1 5 7 ^s0``;
val _ = print_eval "find_last_stealable" ``find_last_stealable [(1i,1); (2,3); (4,0)] (insert 9 () LN) ^s0``;
val _ = print_eval "find_spill_steal" ``find_spill (^st0 with active := [(9i,1)]) (insert 9 () LN) 3 5 F ^s0``;
val _ = print_eval "find_spill_keep" ``find_spill (^st0 with active := [(4i,1)]) (insert 9 () LN) 3 5 F ^s0``;
val _ = print_eval "step_aux_pref" ``linear_reg_alloc_step_aux ^st0 LN [3;4] 1 7 F ^s0``;
val _ = print_eval "step_aux_spill" ``linear_reg_alloc_step_aux (^st0 with <| colorpool := []; colornum := 2 |>) LN [] 1 7 F ^s0``;
val _ = print_eval "pass1_phy" ``linear_reg_alloc_step_pass1 LN LN (linear_reg_alloc_pass1_initial_state 2) 2 ^s0``;
val _ = print_eval "pass1_stack" ``linear_reg_alloc_step_pass1 LN LN (linear_reg_alloc_pass1_initial_state 2) 3 ^s0``;
val _ = print_eval "pass1_forced" ``linear_reg_alloc_step_pass1 (insert 1 [0] LN) (insert 1 [2] LN) (linear_reg_alloc_pass1_initial_state 2 with colorpool := [7;9]) 1 ^s0``;
val _ = print_eval "pass2_virt" ``linear_reg_alloc_step_pass2 LN (insert 1 [0] LN) (linear_reg_alloc_pass2_initial_state 2 3) 1 ^s0``;
val _ = print_eval "find_reg_exchange" ``find_reg_exchange [0;2] LN LN ^s0``;
val _ = print_eval "apply_reg_exchange" ``apply_reg_exchange [0;2] ^s0``;
val _ = print_eval "foldl" ``st_ex_FOLDL (\e x. st_ex_return (e + x)) (0:num) [1;2;3] ^s0``;
val _ = print_eval "filter_good" ``st_ex_FILTER_good (\r. st_ex_bind (colors_sub r) (\col. st_ex_return ((7:num) < col))) [0;1;2;3] ^s0``;
val _ = print_eval "edges" ``edges_to_adjlist [(0,1); (2,2); (3,1)] LN ^s0``;
val _ = print_eval "sort_moves_rev" ``sort_moves_rev [(5,(1,2)); (2,(0,3)); (4,(2,2))]``;
val _ = print_eval "sort_regs" ``sort_regs 0 4 ^s0``;
val _ = print_eval "sorted_regs_to_list" ``sorted_regs_to_list 1 3 ^s0``;
val _ = print_eval "list_to_sorted_regs" ``list_to_sorted_regs [3;2] 1 ^s0``;
val _ = print_eval "sort_moves" ``sort_moves 0 3 ^s0``;
val _ = print_eval "sorted_moves_to_list" ``sorted_moves_to_list 0 2 ^s0``;
val _ = print_eval "list_to_sorted_moves" ``list_to_sorted_moves [(1,(1,1))] 2 ^s0``;
val _ = print_eval "pass_init" ``(linear_reg_alloc_pass1_initial_state 3, linear_reg_alloc_pass2_initial_state 3 4)``;
