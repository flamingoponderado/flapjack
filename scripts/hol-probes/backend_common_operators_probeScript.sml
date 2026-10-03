load "bossLib"; load "preamble"; load "backend_commonTheory";
open bossLib HolKernel Parse preamble backend_commonTheory;
val _ = show_types := true;
val _ = print "opw_case_def=";
val _ = print_term (concl (DB.fetch "backend_common" "opw_case_def"));
val _ = print "\n";
val _ = print "opw_nchotomy=";
val _ = print_term (concl (DB.fetch "backend_common" "opw_nchotomy"));
val _ = print "\n";
