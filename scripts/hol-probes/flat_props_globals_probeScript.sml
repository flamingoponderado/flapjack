load "flatPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "elist_globals_eq_empty="; print_thm flatPropsTheory.elist_globals_eq_empty; print "\n");
val _ = (print "elist_globals_type="; print (type_to_string (type_of ``flatProps$elist_globals``)); print "\n");
