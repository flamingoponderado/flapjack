load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "compile_sing=" bvi_to_dataTheory.compile_sing_def;
val _ = show "compile_exp_eq=" bvi_to_dataTheory.compile_exp_eq;
val _ = show "compile_part=" bvi_to_dataTheory.compile_part_def;
val _ = show "compile_prog=" bvi_to_dataTheory.compile_prog_def;
val _ = show "code_rel=" bvi_to_dataProofTheory.code_rel_def;
val _ = show "state_rel=" bvi_to_dataProofTheory.state_rel_def;
val _ = show "data_to_bvi_do_eq=" bvi_to_dataProofTheory.data_to_bvi_do_eq;
val _ = show "data_to_bvi_do_app=" bvi_to_dataProofTheory.data_to_bvi_do_app;
val _ = show "missing_var=" (EVAL ``bvi_to_data$compile_sing 4 [] F [] (bvi$Var 5)``);
val _ = show "tail_var=" (EVAL ``bvi_to_data$compile_sing 4 [7] T [] (bvi$Var 0)``);
val _ = show "tail_letcall=" (EVAL ``bvi_to_data$compile_sing 2 [] F []
  (bvi$LetCall 1 0 3 [] (bvi$Return [bvi$Var 0]))``);
