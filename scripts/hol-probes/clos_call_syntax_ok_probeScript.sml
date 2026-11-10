load "clos_callProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "syntax_ok_def="; print_thm clos_callProofTheory.syntax_ok_def; print "\n");
val _ = (print "every_Fn_SOME_type="; print (type_to_string (type_of ``closProps$every_Fn_SOME``)); print "\n");
val _ = (print "every_Fn_vs_NONE_type="; print (type_to_string (type_of ``closProps$every_Fn_vs_NONE``)); print "\n");
val _ = (print "code_locs_type="; print (type_to_string (type_of ``closProps$code_locs``)); print "\n");
