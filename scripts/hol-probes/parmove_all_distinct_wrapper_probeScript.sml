load "bossLib";
load "parmoveTheory";
open HolKernel Parse boolLib bossLib parmoveTheory;
val _ = Globals.linewidth := 1000;
val _ = print "pad_original_statement=";
val _ = print_term (concl (DB.fetch "parmove" "ALL_DISTINCT_parmove"));
val _ = print "\n";
fun observe label term =
  (print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n");
val _ = observe "pad_empty" ``parmove ([]:(num # num) list)``;
val _ = observe "pad_self" ``parmove [(0:num,0:num)]``;
val _ = observe "pad_chain" ``parmove [(0:num,1:num);(1,2)]``;
val _ = observe "pad_swap" ``parmove [(0:num,1:num);(1,0)]``;
val _ = observe "pad_cycle" ``parmove [(0:num,1:num);(1,2);(2,0)]``;
val _ = observe "pad_shared_source" ``parmove [(0:num,2:num);(1,2)]``;
val _ = observe "pad_duplicate_boundary" ``(ALL_DISTINCT (MAP FST [(0:num,1:num);(0,2)]), ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove [(0:num,1:num);(0,2)]))))``;
