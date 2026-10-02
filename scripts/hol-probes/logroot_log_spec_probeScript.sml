(* Original HOL logroot LOG (logrootScript.sml:286-306) and bit LOG2 (bitScript.sml:54):
   the kernel statements of LOG_exists, the new_specification theorem LOG, LOG_UNIQUE and
   LOG2_def, plus LOG2 values on positive arguments proved from LOG_UNIQUE (LOG2 is [nocompute]); no
   value of LOG2 0 is derivable from the specification. *)
load "bossLib";
load "logrootTheory";
load "bitTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 4000;
fun observe_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val _ = observe_thm "lg_log_exists" logrootTheory.LOG_exists;
val _ = observe_thm "lg_log_spec" logrootTheory.LOG;
val _ = observe_thm "lg_log_unique" logrootTheory.LOG_UNIQUE;
val _ = observe_thm "lg_log2_def" bitTheory.LOG2_def;
fun observe_pos label tm = let val th = prove (tm, REWRITE_TAC [bitTheory.LOG2_def] >> irule logrootTheory.LOG_UNIQUE >> EVAL_TAC) in observe_thm label th end;
val _ = observe_pos "lg_log2_8" ``LOG2 8 = 3``;
val _ = observe_pos "lg_log2_1" ``LOG2 1 = 0``;
val _ = observe_pos "lg_log2_9" ``LOG2 9 = 3``;
val _ = observe_pos "lg_log2_64" ``LOG2 64 = 6``;
