(* Original HOL mergesortTheory sort2, sort3, merge and mergesortN at the pinned HOL
   revision: types and EVAL results, including a non-strict, a strict and a
   non-total relation and counts that differ from the list length. *)
load "bossLib";
load "mergesortTheory";
open HolKernel Parse boolLib bossLib mergesortTheory;
val _ = Globals.linewidth := 1000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label c = (print (label ^ "="); print_type (type_of c); print "\n");
val _ = observe_type "sort2_type" ``mergesort$sort2``;
val _ = observe_type "sort3_type" ``mergesort$sort3``;
val _ = observe_type "merge_type" ``mergesort$merge``;
val _ = observe_type "mergesortN_type" ``mergesort$mergesortN``;
val _ = observe "sort2_lt" ``sort2 ($< : num -> num -> bool) 5 3``;
val _ = observe "sort2_eq_le" ``sort2 ($<= : num -> num -> bool) 4 4``;
val _ = observe "sort3_all" ``MAP (\(x,y,z). sort3 ($< : num -> num -> bool) x y z) [(1,2,3);(1,3,2);(2,1,3);(2,3,1);(3,1,2);(3,2,1)]``;
val _ = observe "sort3_dup_le" ``sort3 ($<= : num -> num -> bool) 2 1 2``;
val _ = observe "merge_basic" ``merge ($<= : num -> num -> bool) [1; 4; 6] [2; 4; 5]``;
val _ = observe "merge_unsorted" ``merge ($< : num -> num -> bool) [5; 1] [3; 2]``;
val _ = observe "merge_left_empty" ``merge ($< : num -> num -> bool) [] [3; 2]``;
val _ = observe "merge_nontotal" ``merge (\x y:num. EVEN x) [1; 2; 3] [4; 5]``;
val _ = observe "msn_full" ``mergesortN ($<= : num -> num -> bool) 7 [5; 3; 8; 1; 9; 2; 3]``;
val _ = observe "msn_prefix" ``mergesortN ($< : num -> num -> bool) 4 [5; 3; 8; 1; 9; 2]``;
val _ = observe "msn_over" ``mergesortN ($< : num -> num -> bool) 6 [4; 1; 3]``;
val _ = observe "msn_three_short" ``mergesortN ($< : num -> num -> bool) 3 [9; 2]``;
val _ = observe "msn_nontotal" ``mergesortN (\x y:num. EVEN x) 5 [1; 2; 3; 4; 5]``;
val _ = observe "msn_zero" ``mergesortN ($< : num -> num -> bool) 0 [1; 2]``;
