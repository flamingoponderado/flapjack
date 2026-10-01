load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun out label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = out "dw_empty" ``MAP FST (parmove ([]:(num#num) list))``;
val _ = out "dw_self" ``MAP FST (parmove [(1:num,1:num)])``;
val _ = out "dw_chain" ``MAP FST (parmove [(1:num,2:num);(2,3)])``;
val _ = out "dw_cycle" ``MAP FST (parmove [(1:num,2:num);(2,1)])``;
val _ = out "dw_duplicate" ``MAP FST (parmove [(1:num,2:num);(1,3)])``;
val _ = out "dw_order" ``MAP FST (parmove [(9:num,7:num);(2,3);(8,6)])``;
val _ = out "dw_nested_option" ``MAP FST (parmove [(NONE:num option,SOME (2:num));(SOME 1,NONE)])``;
