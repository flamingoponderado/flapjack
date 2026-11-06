load "flatPropsTheory";
open HolKernel Parse boolLib bossLib;
open flatPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "evaluate_match_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_match_def); print "\n");
