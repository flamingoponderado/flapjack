load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "rts_empty" ``remove_temp_stack [] (LN,LN) = (LN,LN)``;
val _ = observe "rts_zero" ``remove_temp_stack [0] (fromAList [(0,());(2,())],LN) = (fromAList [(2,())],LN)``;
val _ = observe "rts_duplicate" ``remove_temp_stack [2;2] (fromAList [(0,());(2,())],LN) = (LS (),LN)``;
val _ = observe "rts_missing" ``remove_temp_stack [99] (LS (),LS ()) = (LS (),LS ())``;
val _ = observe "rts_fixed" ``remove_temp_stack [0;2] (fromAList [(0,());(2,())],fromAList [(0,());(2,())]) = (LN,fromAList [(0,());(2,())])``;
val _ = observe "rts_raw" ``remove_temp_stack [0] (BN LN LN,BN LN LN) = (BN LN LN,BN LN LN)``;
val _ = observe "rts_generic_payload" ``remove_temp_stack [0] (LS (7:num),42:num) = (LN,42)``;
val _ = observe "rts_generic_fixed" ``remove_temp_stack [99] (LS (),T) = (LS (),T)``;
