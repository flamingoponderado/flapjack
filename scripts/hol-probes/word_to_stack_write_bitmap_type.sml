load "bossLib";
load "preamble";
load "word_to_stackTheory";
open HolKernel Parse;
val _ = print "write_bitmap_type=";
val _ = print_type (type_of ``word_to_stack$write_bitmap``);
val _ = print "\n";
