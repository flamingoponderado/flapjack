load "clos_interpProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "attach_semantics_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl clos_interpProofTheory.semantics_attach_interpreter);
  print "\n");
