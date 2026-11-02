load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
open source_to_flatProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "change_clock_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl invariant_change_clock); print "\n");
val _ = (print "dec_clock_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl invariant_dec_clock); print "\n");
