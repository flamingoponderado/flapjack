load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print(label ^ "="); print_term(rconc th); print "\n") end;
val _ = print_eval "pn_duplicate_left" ``parmove$parsem [(1:num,2);(1,3)] (\r. r+10) 1``;
val _ = print_eval "pn_duplicate_right" ``parmove$parsem [(1:num,3)] (\r. if r=1 then 12 else r+10) 1``;
val _ = print_eval "pn_untouched_left" ``parmove$parsem [(1:num,2);(1,3)] (\r. r+10) 7``;
val _ = print_eval "pn_untouched_right" ``parmove$parsem [(1:num,3)] (\r. if r=1 then 12 else r+10) 7``;
val _ = print_eval "pn_boundary_left" ``parmove$parsem [(1:num,2);(3,1)] (\r. r+10) 3``;
val _ = print_eval "pn_boundary_right" ``parmove$parsem [(3:num,1)] (\r. if r=1 then 12 else r+10) 3``;
val _ = print_eval "pn_self_left" ``parmove$parsem [(1:num,1);(3,2)] (\r. r+10) 3``;
val _ = print_eval "pn_self_right" ``parmove$parsem [(3:num,2)] (\r. if r=1 then 11 else r+10) 3``;
