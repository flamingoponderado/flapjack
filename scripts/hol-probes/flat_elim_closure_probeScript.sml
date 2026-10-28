load "flat_elimTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "closure_definition=" spt_closureTheory.closure_spt_def;
val _ = show_eval "noncanonical_subset=" ``sptree$subspt (sptree$BN sptree$LN sptree$LN : unit sptree$spt) (sptree$LS ())``;
val _ = show_eval "noncanonical_closure=" ``spt_closure$closure_spt (sptree$LS ()) (sptree$LS (sptree$BN sptree$LN sptree$LN : unit sptree$spt))``;
