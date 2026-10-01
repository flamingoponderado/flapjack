load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pp_first_one" ``parmove$parsem [(1:num,2);(3,1);(4,2)] (\r. r+10) 1``;
val _ = print_eval "pp_second_one" ``parmove$parsem [(4:num,2);(3,1);(1,2)] (\r. r+10) 1``;
val _ = print_eval "pp_first_three" ``parmove$parsem [(1:num,2);(3,1);(4,2)] (\r. r+10) 3``;
val _ = print_eval "pp_second_three" ``parmove$parsem [(4:num,2);(3,1);(1,2)] (\r. r+10) 3``;
val _ = print_eval "pp_first_four" ``parmove$parsem [(1:num,2);(3,1);(4,2)] (\r. r+10) 4``;
val _ = print_eval "pp_second_four" ``parmove$parsem [(4:num,2);(3,1);(1,2)] (\r. r+10) 4``;
val _ = print_eval "pp_duplicate_first" ``parmove$parsem [(1:num,2);(1,3)] (\r. r+10) 1``;
val _ = print_eval "pp_duplicate_second" ``parmove$parsem [(1:num,3);(1,2)] (\r. r+10) 1``;
val _ = print_eval "pp_swap" ``parmove$parsem [(1:num,2);(2,1)] (\r. r+10) 2``;
val _ = print_eval "pp_empty" ``parmove$parsem ([]:(num#num)list) (\r. r+10) 7``;
