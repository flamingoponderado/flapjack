(* Types and checked recursive-layout observations from the pinned theory. *)
load "clos_to_bvlTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "recc_lets_type="; print_type (type_of ``clos_to_bvl$recc_Lets``); print "\n");
val _ = (print "build_recc_lets_type="; print_type (type_of ``clos_to_bvl$build_recc_lets``); print "\n");
val example = rhs (concl (EVAL ``clos_to_bvl$recc_Lets 4 [1; 2] 2 (bvl$Var 0)``));
val _ = (print "recc_lets_example="; print_term example; print "\n");
val group = rhs (concl (EVAL ``clos_to_bvl$build_recc_lets [1; 2] [5] 4 2 (bvl$Var 0)``));
val _ = (print "build_recc_lets_example="; print_term group; print "\n");
val _ = (print "compile_exp_sing_def="; print_term (concl clos_to_bvlTheory.compile_exp_sing_def); print "\n");
val _ = (print "compile_exp_sing_type="; print_type (type_of ``clos_to_bvl$compile_exp_sing``); print "\n");
val _ = (print "compile_exp_list_type="; print_type (type_of ``clos_to_bvl$compile_exp_list``); print "\n");
val _ = (print "compile_prog_def="; print_term (concl clos_to_bvlTheory.compile_prog_def); print "\n");
val _ = (print "compile_prog_type="; print_type (type_of ``clos_to_bvl$compile_prog``); print "\n");
val _ = (print "compile_exps_def="; print_term (concl clos_to_bvlTheory.compile_exps_def); print "\n");
val _ = (print "compile_exps_type="; print_type (type_of ``clos_to_bvl$compile_exps``); print "\n");
val _ = (print "compile_exp_sing_eq="; print_term (concl clos_to_bvlTheory.compile_exp_sing_eq); print "\n");
