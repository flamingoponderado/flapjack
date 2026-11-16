(* Inferred source type and complete thunk-force compilation equation. *)
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "force_thunk_typed="; print_thm data_to_wordTheory.force_thunk_def; print "\n");
