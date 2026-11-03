(* Typed source statements for closure lifting invariants. *)
load "clos_opProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print "="; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "dont_lift_thm_typed" clos_opProofTheory.dont_lift_thm;
val _ = show "dont_lift_pure_typed" clos_opProofTheory.dont_lift_pure;
val _ = show "lift_acc_typed" clos_opProofTheory.lift_exps_acc;
val _ = show "lift_n_typed" clos_opProofTheory.lift_exps_n;
val _ = show "lift_length_typed" clos_opProofTheory.lift_exps_length;
