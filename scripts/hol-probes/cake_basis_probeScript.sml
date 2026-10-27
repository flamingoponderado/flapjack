load "basisProgTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 100000000;
val _ = (print "basis="; print_term (rhs (concl basisProgTheory.basis_def)); print "\n");
val _ = (print "length="; print_term (rhs (concl (EVAL ``LENGTH basisProg$basis``))); print "\n");
