(* Typed definitions and representative source tick-removal results. *)
load "bvl_inlineTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun example label term = (print label; print_term (rhs (concl (EVAL term))); print "\n");
val _ = show "remove_ticks_sing=" bvl_inlineTheory.remove_ticks_sing_def;
val _ = show "remove_ticks=" bvl_inlineTheory.remove_ticks_def;
val _ = show "remove_ticks_equivalence=" bvl_inlineTheory.remove_ticks_sing;
val _ = example "nested=" ``bvl_inline$remove_ticks_sing
  (bvl$Tick (bvl$Call 3 (SOME 8) [bvl$Tick (bvl$Var 4); bvl$Force 2 9]))``;
val _ = example "branches=" ``bvl_inline$remove_ticks_list
  [bvl$If (bvl$Tick (bvl$Var 0)) (bvl$Tick (bvl$Var 1)) (bvl$Var 2);
   bvl$Let [bvl$Tick (bvl$Var 3)] (bvl$Raise (bvl$Tick (bvl$Var 4)))]``;
