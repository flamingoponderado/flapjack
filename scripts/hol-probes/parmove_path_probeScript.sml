load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pv_empty" ``parmove$path (SNOC (1:num,99) [])``;
val _ = print_eval "pv_single" ``parmove$path (SNOC (1:num,99) [(3,1)])``;
val _ = print_eval "pv_chain" ``parmove$path (SNOC (1:num,99) [(4,3);(3,1)])``;
val _ = print_eval "pv_cycle" ``parmove$path (SNOC (3:num,99) [(1,2);(2,3)])``;
val _ = print_eval "pv_changed_dest" ``parmove$path (SNOC (2:num,99) [(3,1)])``;
val _ = print_eval "pv_bad_prefix" ``parmove$path (SNOC (1:num,99) [(4,2);(3,1)])``;
val _ = print_eval "pv_windmill_empty" ``parmove$windmill [(1:num,2)]``;
val _ = print_eval "pv_windmill_fresh" ``parmove$windmill [(1:num,2);(3,2)]``;
val _ = print_eval "pv_windmill_repeated" ``parmove$windmill [(1:num,2);(1,3)]``;
val _ = print_eval "pv_windmill_sources" ``parmove$windmill [(1:num,2);(3,2);(4,2)]``;
