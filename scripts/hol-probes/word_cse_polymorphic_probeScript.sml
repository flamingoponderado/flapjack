load "preamble"; load "word_cseTheory";
open HolKernel Parse bossLib preamble word_cseTheory;
val _ = Globals.linewidth := 2000;
fun statement label th = (print (label ^ "="); print_thm th; print "\n");
fun typ label tm = (print (label ^ "="); print_type (type_of tm); print "\n");
statement "map_insert_statement" map_insert_def;
typ "map_insert_type" ``map_insert``;
statement "keep_data_statement" keep_data_def;
typ "keep_data_type" ``keep_data``;
