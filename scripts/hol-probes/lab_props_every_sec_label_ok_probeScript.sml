load "labPropsTheory";
open HolKernel Parse bossLib labPropsTheory;
val _ = Globals.linewidth := 1000000;
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = pr_stmt "EVERY_sec_label_ok_statement" EVERY_sec_label_ok;
val _ = pr_hyps "EVERY_sec_label_ok_hypotheses" EVERY_sec_label_ok;
val _ = pr_typed "EVERY_sec_label_ok_typed" EVERY_sec_label_ok;
