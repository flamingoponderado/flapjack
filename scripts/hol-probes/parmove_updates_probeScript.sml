load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pu_fresh" ``parmove$parsem [(1:num,2);(3,1)] (\r. r+10) 1``;
val _ = print_eval "pu_snapshot" ``parmove$parsem [(1:num,2);(3,1)] (\r. r+10) 3``;
val _ = print_eval "pu_untouched" ``parmove$parsem [(1:num,2);(3,1)] (\r. r+10) 7``;
val _ = print_eval "pu_later_destination" ``parmove$parsem [(1:num,2);(3,2)] (\r. r+10) 3``;
val _ = print_eval "pu_freshness_boundary" ``parmove$parsem [(1:num,2);(1,3)] (\r. r+10) 1``;
val _ = print_eval "pu_empty" ``parmove$parsem ([] : (num # num) list) (\r. r+10) 1``;
val _ = print_eval "pu_self" ``parmove$parsem [(1:num,1)] (\r. r+10) 1``;
val _ = print_eval "pu_swap" ``parmove$parsem [(1:num,2);(2,1)] (\r. r+10) 2``;
fun print_simp label q =
  let val th = SIMP_CONV (srw_ss()) [parmoveTheory.eqenv_def, optionTheory.FORALL_OPTION] q
  in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_simp "pu_eq_forward"
  ``parmove$eqenv (\r:num option. if r = NONE then 0 else 1)
    (\r:num option. if r = NONE then 9 else 1)``;
val _ = print_simp "pu_eq_reverse"
  ``parmove$eqenv (\r:num option. if r = NONE then 9 else 1)
    (\r:num option. if r = NONE then 0 else 1)``;
