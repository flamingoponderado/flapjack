load "bvi_letTheory";
open HolKernel Parse boolLib bossLib bvi_letTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "compile_sing_def=" compile_sing_def;
val _ = show "compile_sing=" compile_sing;
val _ = show "compile_exp_def=" compile_exp_def;
val _ = show "compile_exp_eq=" compile_exp_eq;
val _ = show "compile_tail=" (EVAL ``compile_exp
  (bvi$Let [bvi$Var 3; bvi$Var 1] (bvi$Var 1))``);
val _ = show "compile_vars=" (EVAL ``compile_exp
  (bvi$Let [bvi$Var 3; bvi$Var 1] (bvi$Var 0))``);
val _ = show "compile_empty=" (EVAL ``compile_exp
  (bvi$Let [] (bvi$Var 2))``);
