load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "tc_absent_zero" ``total_colour (LN : num num_map) 0``;
val _ = observe "tc_absent_physical" ``total_colour (LN : num num_map) 2``;
val _ = observe "tc_absent_virtual" ``total_colour (LN : num num_map) 3``;
val _ = observe "tc_absent_large_physical" ``total_colour (LN : num num_map) 4294967296``;
val _ = observe "tc_absent_large_virtual" ``total_colour (LN : num num_map) 4294967297``;
val _ = observe "tc_mapped_physical" ``total_colour (insert 2 7 LN : num num_map) 2``;
val _ = observe "tc_mapped_virtual" ``total_colour (insert 3 8 LN : num num_map) 3``;
val _ = observe "tc_mapped_zero" ``total_colour (insert 3 0 LN : num num_map) 3``;
