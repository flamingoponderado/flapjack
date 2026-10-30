(* Typed compiler global-effect theorems from the pinned source proof. *)
load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "op_theorem="; print_term (concl source_to_flatProofTheory.op_gbag_astOp_to_flatOp); print "\n");
val _ = (print "compile_theorem="; print_term (concl source_to_flatProofTheory.compile_exp_esgc_free); print "\n");
val _ = (print "make_varls_theorem="; print_term (concl source_to_flatProofTheory.make_varls_esgc_free); print "\n");
val _ = (print "compile_decs_theorem="; print_term (concl source_to_flatProofTheory.compile_decs_esgc_free); print "\n");
val _ = (print "compile_prog_theorem="; print_term (concl source_to_flatProofTheory.compile_prog_esgc_free); print "\n");
val _ = (print "inc_compile_prog_theorem="; print_term (concl source_to_flatProofTheory.inc_compile_prog_esgc_free); print "\n");
val _ = (print "compile_flat_esgc="; print_term (concl source_to_flatProofTheory.compile_flat_esgc_free); print "\n");
val _ = (print "compile_full_esgc="; print_term (concl source_to_flatProofTheory.compile_esgc_free); print "\n");
val _ = (print "inc_compile_full_esgc="; print_term (concl source_to_flatProofTheory.inc_compile_esgc_free); print "\n");
val _ = (print "compile_no_mat="; print_term (concl source_to_flatProofTheory.compile_no_Mat); print "\n");
val _ = (print "inc_compile_no_mat="; print_term (concl source_to_flatProofTheory.inc_compile_no_Mat); print "\n");
val _ = (print "num_bindings="; print_term (concl source_to_flatProofTheory.num_bindings_def); print "\n");
val _ = (print "compile_decs_num_bindings="; print_term (concl source_to_flatProofTheory.compile_decs_num_bindings); print "\n");
