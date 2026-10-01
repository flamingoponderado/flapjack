load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "cc_absent" ``get_coalescecost (LN : num num_map) (2,3,(7,8))``;
val _ = observe "cc_left" ``get_coalescecost (insert 7 999 LN) (2,3,(7,8))``;
val _ = observe "cc_right" ``get_coalescecost (insert 8 0 LN) (2,3,(7,8))``;
val _ = observe "cc_both" ``get_coalescecost (insert 7 999 (insert 8 0 LN)) (2,3,(7,8))``;
val _ = observe "cc_same" ``get_coalescecost (insert 7 F LN) (2,3,(7,7))``;
val _ = observe "cc_zero" ``get_coalescecost (insert 7 T LN) (0,3,(7,8))``;
val _ = observe "cc_large" ``get_coalescecost (LN : num num_map) (18446744073709551616,0,(7,8))``;
val _ = observe "cc_raw" ``get_coalescecost (BN LN LN : num num_map) (1,0,(0,1))``;
