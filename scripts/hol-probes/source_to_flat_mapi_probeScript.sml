load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "mapi_map_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl source_to_flatProofTheory.mapi_map); print "\n");
val _ = (print "filter_mapi_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl source_to_flatProofTheory.FILTER_MAPi_ID); print "\n");
