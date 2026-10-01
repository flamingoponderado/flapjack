load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pe_first_written" ``parmove$parsem [(1:num,2);(1,2)] (\r. r+10) 1``;
val _ = print_eval "pe_second_written" ``parmove$parsem [(1:num,2);(1,2)] (\r. if r=2 then 12 else 99) 1``;
val _ = print_eval "pe_first_untouched" ``parmove$parsem [(1:num,2);(1,2)] (\r. r+10) 7``;
val _ = print_eval "pe_second_untouched" ``parmove$parsem [(1:num,2);(1,2)] (\r. if r=2 then 12 else 99) 7``;
val _ = print_eval "pe_source_boundary" ``parmove$parsem [(1:num,2);(1,2)] (\r. if r=2 then 100 else 99) 1``;
val _ = print_eval "pe_source_maps" ``MAP ((\r:num. r+10) o SND) [(1:num,2);(1,2)] = MAP ((\r:num. if r=2 then 12 else 99) o SND) [(1:num,2);(1,2)]``;
val _ = print_eval "pe_empty" ``parmove$parsem ([]:(num#num)list) (\r. r+10) 7``;
val _ = print_eval "pe_snapshot" ``parmove$parsem [(1:num,2);(3,1)] (\r. r+10) 3``;
