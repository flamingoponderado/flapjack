load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "spill_zero" ``get_spillcost (0,0,0,0,0) T``;
val _ = observe "spill_call_tail" ``get_spillcost (1,0,0,0,0) T``;
val _ = observe "spill_call_nontail" ``get_spillcost (1,0,0,0,0) F``;
val _ = observe "spill_left_register" ``get_spillcost (0,1,0,0,0) F``;
val _ = observe "spill_left_memory" ``get_spillcost (0,0,1,0,0) F``;
val _ = observe "spill_right_register" ``get_spillcost (0,0,0,1,0) F``;
val _ = observe "spill_right_memory" ``get_spillcost (0,0,0,0,1) F``;
val _ = observe "spill_asymmetric_tail" ``get_spillcost (2,3,5,7,11) T``;
val _ = observe "spill_asymmetric_nontail" ``get_spillcost (2,3,5,7,11) F``;
val _ = observe "spill_large" ``get_spillcost (0,0,0,0,18446744073709551616) F``;
