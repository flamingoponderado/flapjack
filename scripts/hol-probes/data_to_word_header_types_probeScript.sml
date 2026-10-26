load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib data_to_wordTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val _ = (print "make_header_type="; print (type_to_string (type_of ``data_to_word$make_header``)); print "\n");
val _ = (print "make_header_definition="; print_term (concl make_header_def); print "\n");
val _ = (print "encode_header_type="; print (type_to_string (type_of ``data_to_word$encode_header``)); print "\n");
val _ = (print "encode_header_definition="; print_term (concl encode_header_def); print "\n");
