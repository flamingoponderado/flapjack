(* Typed source statements for the closure-to-BVL state relation. *)
load "clos_to_bvlProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "state_rel_typed=" clos_to_bvlProofTheory.state_rel_def;
val _ = show "state_rel_clock_typed=" clos_to_bvlProofTheory.state_rel_clock;
val _ = show "state_rel_refs_lookup_typed=" clos_to_bvlProofTheory.state_rel_refs_lookup;
val _ = show "compile_exps_correct_typed=" clos_to_bvlProofTheory.compile_exps_correct;
