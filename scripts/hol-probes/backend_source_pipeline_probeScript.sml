(* Inferred source-to-data backend pipeline definitions. *)
load "backendTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "to_flat_typed="; print_thm backendTheory.to_flat_def; print "\n");
val _ = (print "to_clos_typed="; print_thm backendTheory.to_clos_def; print "\n");
val _ = (print "to_bvl_typed="; print_thm backendTheory.to_bvl_def; print "\n");
val _ = (print "to_bvi_typed="; print_thm backendTheory.to_bvi_def; print "\n");
val _ = (print "to_data_typed="; print_thm backendTheory.to_data_def; print "\n");
