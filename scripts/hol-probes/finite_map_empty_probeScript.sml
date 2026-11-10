load "finite_mapTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "fempty_typed=" finite_mapTheory.FEMPTY_DEF;
val _ = show_thm "flookup_empty_typed=" finite_mapTheory.FLOOKUP_EMPTY;
val _ = show_thm "funion_spec_typed=" finite_mapTheory.FUNION_DEF;
