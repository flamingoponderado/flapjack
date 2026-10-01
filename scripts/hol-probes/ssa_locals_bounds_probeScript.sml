load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory;
val more = Q.prove(
 `!na ssa stlocs cstlocs na'.
    ssa_locals_rel na ssa stlocs cstlocs /\ na <= na' ==>
    ssa_locals_rel na' ssa stlocs cstlocs`,
 srw_tac[][ssa_locals_rel_def]>>full_simp_tac(srw_ss())[]
 >- metis_tac[]>>
 res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val _ = print "lb_more=";
val _ = print_thm more;
val _ = print "\n";
