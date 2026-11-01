load "data_to_wordTheory";
load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "any_arith_call_tree=" data_to_wordTheory.AnyArith_call_tree_def;
val _ = show "stack_consumed=" dataSemTheory.stack_consumed_def;
val _ = show "do_stack=" dataSemTheory.do_stack_def;
