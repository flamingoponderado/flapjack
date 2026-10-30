load "bvl_to_bviProofTheory";
load "preamble";
open preamble bvl_to_bviProofTheory bvlSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "adjust_bv_def=" adjust_bv_def;
val _ = show "adjust_bv_Unit=" adjust_bv_Unit;
val _ = show "adjust_bv_Boolv=" adjust_bv_Boolv;
val _ = show "adjust_nested=" (EVAL ``adjust_bv (\n. n + 5)
  (Block 7 [Number ~3; RefPtr T 2; CodePtr 3; Block 8 [RefPtr F 9]])``);
