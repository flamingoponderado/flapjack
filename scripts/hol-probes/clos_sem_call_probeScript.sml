load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "dest_closure_typed=" closSemTheory.dest_closure_def;
val _ = show_thm "dest_closure_length_typed=" closSemTheory.dest_closure_length;
val _ = show_eval "partial=" ``closSem$dest_closure 3 NONE
  (Closure NONE [] [Number 9] 2 (closLang$Var None 0)) [Number 1]``;
val _ = show_eval "overapplication=" ``closSem$dest_closure 3 NONE
  (Closure NONE [] [Number 9] 2 (closLang$Var None 0)) [Number 1; Number 2; Number 3]``;
val _ = show_eval "direct_mismatch=" ``closSem$dest_closure 3 (SOME 4)
  (Closure (SOME 3) [] [] 1 (closLang$Var None 0)) [Number 1]``;
val _ = show_eval "recursive_direct=" ``closSem$dest_closure 3 (SOME 12)
  (Recclosure (SOME 10) [] [] [(1,closLang$Var None 0); (1,closLang$Var None 1)] 1) [Number 7]``;
val _ = show_eval "recursive_out_of_range=" ``closSem$dest_closure 3 NONE
  (Recclosure NONE [] [] [(1,closLang$Var None 0)] 1) [Number 7]``;
