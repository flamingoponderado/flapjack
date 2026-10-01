load "bossLib";
load "preamble";
load "miscTheory";
open bossLib HolKernel Parse preamble miscTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "fi_empty" ``find_index 2 ([] : num list) 0``;
val _ = observe "fi_head" ``find_index 2 ([2;3] : num list) 7``;
val _ = observe "fi_middle" ``find_index 2 ([1;2;3] : num list) 7``;
val _ = observe "fi_absent" ``find_index 2 ([1;3] : num list) 7``;
val _ = observe "fi_duplicate" ``find_index 2 ([1;2;2] : num list) 3``;
val _ = observe "fi_zero" ``find_index 0 ([0;0] : num list) 0``;
val _ = observe "fi_large_offset" ``find_index 2 ([1;2] : num list) 4294967296``;
val _ = observe "fi_last" ``find_index 4 ([1;2;3;4] : num list) 9``;
