(* Inferred source type and complete thunk-force compilation equation. *)
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "force_thunk_typed="; print_thm data_to_wordTheory.force_thunk_def; print "\n");
val _ = (print "arg4_typed="; print_thm data_to_wordTheory.arg4_def; print "\n");
val _ = (print "set_bool_typed="; print_thm data_to_wordTheory.SetBool_def; print "\n");
val _ = (print "assign_cmp_typed="; print_thm data_to_wordTheory.AssignCmp_def; print "\n");
