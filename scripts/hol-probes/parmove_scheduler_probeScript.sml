load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
(* Direct original terminating scheduler and wrapper observations. *)
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pm_final" ``parmove$pmov ([],[],[(SOME 8,SOME 9)] : (num option # num option) list)``;
val _ = print_eval "pm_temp_self" ``parmove$pmov ([(NONE,NONE)],[],[] : (num option # num option) list)``;
val _ = print_eval "pm_empty" ``parmove$parmove ([] : (num # num) list)``;
val _ = print_eval "pm_self" ``parmove$parmove [(1:num,1)]``;
val _ = print_eval "pm_single" ``parmove$parmove [(1:num,2)]``;
val _ = print_eval "pm_chain" ``parmove$parmove [(1:num,2);(2,3);(3,4)]``;
val _ = print_eval "pm_swap" ``parmove$parmove [(1:num,2);(2,1)]``;
val _ = print_eval "pm_cycle" ``parmove$parmove [(1:num,2);(2,3);(3,1)]``;
val _ = print_eval "pm_repeated" ``parmove$parmove [(1:num,2);(1,3)]``;
