(* Direct original linear_scan top-level allocator definitions; CakeML remains
   read-only. Each row prints the full EVAL result with raw sparse trees. *)
load "bossLib";
load "preamble";
load "linear_scanTheory";
open bossLib HolKernel Parse preamble ml_monadBaseTheory linear_scanTheory;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "bijection_seq" ``find_bijection_clash_tree find_bijection_init (Seq (Delta [5;3] [2]) (Set (insert 9 () (insert 4 () LN))))``;
val _ = print_eval "bijection_branch" ``find_bijection_clash_tree find_bijection_init (Branch (SOME (insert 7 () LN)) (Delta [1] [5]) (Delta [11] [0]))``;
val _ = print_eval "apply_bij_tree" ``apply_bij_on_clash_tree (Branch (SOME (insert 7 () LN)) (Delta [1;3] [5]) (Set (insert 3 () LN))) (insert 1 9 (insert 3 4 (insert 7 2 LN)))``;
val _ = print_eval "apply_bijection" ``apply_bijection (insert 1 9 (insert 3 4 LN)) (insert 1 (-2) (insert 3 5 (insert 8 0 LN)))``;
val _ = print_eval "size_ct" ``size_of_clash_tree (Branch (SOME (insert 7 () LN)) (Delta [1] [5]) (Seq (Set LN) (Delta [] [])))``;
val _ = print_eval "extract" ``extract_coloration (insert 1 5 (insert 5 9 LN)) [1;5] LN <| colors := [0;3;0;0;0;7]; int_beg := []; int_end := []; sorted_regs := []; sorted_moves := [] |>``;
val _ = print_eval "run_i" ``run_i_linear_scan_hidden_state (colors_sub 1) <| colors := (3, 4); int_beg := (0, 0); int_end := (0, 0); sorted_regs := (0, 0); sorted_moves := (0, (0,0,0)) |>``;
val _ = print_eval "run_i_fail" ``run_i_linear_scan_hidden_state (colors_sub 3) <| colors := (3, 4); int_beg := (0, 0); int_end := (0, 0); sorted_regs := (0, 0); sorted_moves := (0, (0,0,0)) |>``;
val _ = print_eval "lsra_delta" ``linear_scan_reg_alloc 3 [] (Delta [1;5] [2]) []``;
val _ = print_eval "lsra_moves" ``linear_scan_reg_alloc 3 [(1,(1,5))] (Seq (Delta [5] [1]) (Delta [1] [])) []``;
val _ = print_eval "lsra_forced" ``linear_scan_reg_alloc 2 [] (Delta [1;5;9] [3]) [(1,5)]``;
val _ = print_eval "lsra_branch_spill" ``linear_scan_reg_alloc 1 [] (Branch (SOME (insert 1 () LN)) (Delta [1] [5]) (Delta [9] [1])) []``;
val _ = print_eval "lsra_phys" ``linear_scan_reg_alloc 2 [] (Delta [0;2;5] [4;7]) []``;
val _ = print_eval "lsra_stack" ``linear_scan_reg_alloc 2 [(3,(5,7))] (Seq (Delta [3;5] [7;1]) (Delta [7] [5])) [(5,1)]``;
