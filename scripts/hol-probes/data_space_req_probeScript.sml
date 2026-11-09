load "data_spaceTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "num_size=" data_spaceTheory.num_size_def;
val _ = show "part_space_req=" data_spaceTheory.part_space_req_def;
val _ = show "op_space_req=" data_spaceTheory.op_space_req_def;
