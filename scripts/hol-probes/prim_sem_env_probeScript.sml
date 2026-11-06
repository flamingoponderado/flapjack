load "primTypesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "add_type="; print_type (type_of ``primTypes$add_to_sem_env``); print "\n");
val _ = (print "prim_type="; print_type (type_of ``primTypes$prim_sem_env``); print "\n");
