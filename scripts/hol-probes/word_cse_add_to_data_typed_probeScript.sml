load "word_cseTheory";
open HolKernel Parse bossLib word_cseTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "add_to_data_type="; print_type (type_of ``add_to_data``); print "\n");
val _ = (print "add_to_data_def_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl add_to_data_def));
val _ = print("add_to_data_def_hypotheses=" ^ Int.toString(length(hyp add_to_data_def)) ^ "\n");
