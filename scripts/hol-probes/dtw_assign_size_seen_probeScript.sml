load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "size_of_cons_seen_Block="; print_thm data_to_word_assignProofTheory.size_of_cons_seen_Block; print "\n");
val _ = (print "size_of_type="; print (type_to_string (type_of ``dataSem$size_of``)); print "\n");
