(* Typed original association-list finite-map definitions. *)
load "alistTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "alist_to_fmap_typed=" alistTheory.alist_to_fmap_def;
val _ = show "alist_to_fmap_clauses_typed=" alistTheory.alist_to_fmap_thm;
val _ = show "alookup_typed=" alistTheory.ALOOKUP_def;
