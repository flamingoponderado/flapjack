load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val _ = (print "lt_ok_full="; print_thm lt_ok_def; print "\n");
val vars = free_vars (concl (SPEC_ALL lt_ok_def));
val lt = valOf(List.find (fn t => fst(dest_var t) = "lt") vars);
val _ = (print "lt_ok_type_lt="; print_type(type_of lt); print "\n");
