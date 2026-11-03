(* Typed source declarations for closure tick removal. *)
load "clos_ticksTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_sing_typed" clos_ticksTheory.remove_ticks_sing_def;
val _ = show "remove_sing_eq_typed" clos_ticksTheory.remove_ticks_sing_eq;
val _ = show "compile_inc_typed" clos_ticksTheory.compile_inc_def;
