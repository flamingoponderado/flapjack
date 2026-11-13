load "data_spaceProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "get_code_labels_compile="; print_thm data_spaceProofTheory.get_code_labels_compile; print "\n");
val _ = (print "compile_type="; print (type_to_string (type_of ``data_space$compile``)); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "get_code_labels_space_typed="; print_term (concl data_spaceProofTheory.get_code_labels_space); print "\n");
