load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail label;
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "do_log_typed=" semanticPrimitivesTheory.do_log_def;
val _ = show_eval "log_boolean=" ``MAP (\(op,b). semanticPrimitives$do_log op (semanticPrimitives$Boolv b) (Lit (IntLit 7)))
  [(Andalso,T); (Andalso,F); (Orelse,T); (Orelse,F)]``;
val _ = show_eval "log_non_boolean=" ``semanticPrimitives$do_log Andalso (Litv (IntLit 1)) (Lit (IntLit 7))``;
