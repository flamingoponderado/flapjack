load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "env_rel_list_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl source_to_flatProofTheory.env_rel_LIST_REL); print "\n");
