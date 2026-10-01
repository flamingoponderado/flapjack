(* Original HOL sortingTheory SORTED, PART and PARTITION at the pinned HOL
   revision: types and EVAL results. *)
load "bossLib";
load "sortingTheory";
open HolKernel Parse boolLib bossLib sortingTheory;
val _ = Globals.linewidth := 1000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label c = (print (label ^ "="); print_type (type_of c); print "\n");
val _ = observe_type "sorted_type" ``sorting$SORTED``;
val _ = observe_type "part_type" ``sorting$PART``;
val _ = observe_type "partition_type" ``sorting$PARTITION``;
val _ = observe "sorted_empty" ``SORTED ($< : num -> num -> bool) []``;
val _ = observe "sorted_single" ``SORTED ($< : num -> num -> bool) [5]``;
val _ = observe "sorted_asc" ``SORTED ($< : num -> num -> bool) [1; 2; 5]``;
val _ = observe "sorted_dup" ``SORTED ($< : num -> num -> bool) [1; 2; 2]``;
val _ = observe "sorted_le_dup" ``SORTED ($<= : num -> num -> bool) [1; 2; 2]``;
val _ = observe "sorted_gt" ``SORTED ($> : num -> num -> bool) [9; 4; 1; 0]``;
val _ = observe "sorted_nontrans" ``SORTED (\x y:num. x <> y) [1; 2; 1]``;
val _ = observe "part_basic" ``PART (\x:num. x < 3) [1; 5; 2; 7] [10] [20]``;
val _ = observe "part_empty" ``PART (\x:num. T) [] [1] [2]``;
val _ = observe "partition_basic" ``PARTITION (\x:num. EVEN x) [1; 2; 3; 4; 6]``;
val _ = observe "partition_bool" ``PARTITION (\b:bool. b) [T; F; T]``;
