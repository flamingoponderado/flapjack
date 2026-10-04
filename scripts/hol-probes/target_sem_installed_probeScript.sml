load "targetSemTheory";
open HolKernel Parse bossLib targetSemTheory;
val _ = Globals.linewidth := 1000000;
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = pr_stmt "installed_def_statement" installed_def;
val _ = pr_hyps "installed_def_hypotheses" installed_def;
val _ = pr_typed "installed_def_typed" installed_def;
