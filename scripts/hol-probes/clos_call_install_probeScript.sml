load "clos_callProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "code_rel_state_rel_install_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.code_rel_state_rel_install); print "\n");
