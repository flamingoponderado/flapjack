load "pegexec_cml_foTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "variable="; print_term (rhs (concl (EVAL ``
 pegexec_cml_fo$peg_exec_fuel_fo 100 (Nt_fo (INL nV) SemU_id)
 [(AlphaT «abc»,Locs (POSN 0 1) (POSN 0 4))] [] NONE [] Done_fo Failed_fo``))); print "\n");
val _ = (print "empty="; print_term (rhs (concl (EVAL ``
 pegexec_cml_fo$peg_exec_core_fuel 2000 []``))); print "\n");
