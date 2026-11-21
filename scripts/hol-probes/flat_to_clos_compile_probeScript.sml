load "flat_to_closTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "HD_compile_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.HD_compile); print "\n");
