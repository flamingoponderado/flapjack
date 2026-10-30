(* Typed compiler global-effect theorems from the pinned source proof. *)
load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "op_theorem="; print_term (concl source_to_flatProofTheory.op_gbag_astOp_to_flatOp); print "\n");
val _ = (print "compile_theorem="; print_term (concl source_to_flatProofTheory.compile_exp_esgc_free); print "\n");
