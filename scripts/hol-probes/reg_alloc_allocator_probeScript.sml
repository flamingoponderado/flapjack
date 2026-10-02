load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
(* complete reg_alloc runs, observed through toAList of the returned colouring *)
fun ra t = ``case ^t of M_success col => SOME (toAList col) | M_failure _ => NONE``;
val _ = observe "ra_simple_delta" (ra ``reg_alloc Simple NONE 3 [] (Delta [1;5] [9]) [] LN``);
val _ = observe "ra_irc_move" (ra ``reg_alloc IRC NONE 2 [(1,(1,5))] (Seq (Delta [1] [5]) (Delta [9] [1;5])) [] LN``);
val _ = observe "ra_simple_move" (ra ``reg_alloc Simple NONE 2 [(1,(1,5))] (Seq (Delta [1] [5]) (Delta [9] [1;5])) [] LN``);
val _ = observe "ra_irc_spill_cost" (ra ``reg_alloc IRC (SOME (fromAList [(1,10);(5,1);(9,7)])) 1 [] (Delta [1;5;9] [1;5;9]) [] LN``);
val _ = observe "ra_irc_spill_deg" (ra ``reg_alloc IRC NONE 1 [] (Delta [1;5;9] [1;5;9]) [] LN``);
val _ = observe "ra_simple_branch_forced" (ra ``reg_alloc Simple NONE 2 [] (Branch (SOME (insert 1 () LN)) (Delta [5] [1]) (Delta [9] [1])) [(1,5)] LN``);
val _ = observe "ra_irc_phys" (ra ``reg_alloc IRC NONE 3 [(5,(0,1))] (Delta [0;1] [2;5]) [] LN``);
val _ = observe "ra_irc_fs" (ra ``reg_alloc IRC NONE 2 [] (Delta [1;5] []) [] (insert 1 () LN)``);
val _ = observe "ra_irc_stack" (ra ``reg_alloc IRC NONE 2 [] (Delta [3;1;7] [5]) [] LN``);
val _ = observe "ra_irc_coalesce_chain" (ra ``reg_alloc IRC NONE 2 [(3,(1,5));(2,(5,9))] (Seq (Delta [1] []) (Seq (Delta [5] [1]) (Delta [9] [5]))) [] LN``);
val _ = observe "ra_irc_pressure" (ra ``reg_alloc IRC NONE 2 [(4,(1,13))] (Seq (Delta [1;5;9] [13]) (Delta [13] [1;5;9])) [] LN``);
val _ = observe "ra_empty" (ra ``reg_alloc IRC NONE 2 [] (Set LN) [] LN``);
