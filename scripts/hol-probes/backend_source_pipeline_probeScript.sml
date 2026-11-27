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
val _ = let val ty = mk_type ("backend_progs", [alpha])
            val [c] = TypeBase.constructors_of ty
            val (n, t) = dest_const c
        in print ("backend_progs_typed=" ^ n ^ ":" ^ type_to_string t ^ "\n") end;
val _ = (print "empty_progs_def_typed="; print_thm backendTheory.empty_progs_def; print "\n");
val _ = (print "keep_progs_def_typed="; print_thm backendTheory.keep_progs_def; print "\n");
val _ = (print "set_oracle_def_typed="; print_thm backendTheory.set_oracle_def; print "\n");
