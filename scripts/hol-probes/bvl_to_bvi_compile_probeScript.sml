load "bvl_to_bviTheory";
load "miscTheory";
open HolKernel Parse boolLib bossLib bvl_to_bviTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "smart_append_def=" miscTheory.SmartAppend_def;
val _ = show "compile_aux_def=" compile_aux_def;
val _ = show "compile_exps_sing_def=" compile_exps_sing_def;
val _ = show "compile_exps_sing=" compile_exps_sing;
val _ = show "compile_aux_example=" (EVAL ``compile_aux (2, T, bvi$Var 1)``);
val _ = show "compile_tree_example=" (EVAL ``compile_exps_sing 0
  (bvl$If (bvl$Let [] (bvl$Let [] (bvl$Var 0)))
    (bvl$Let [] (bvl$Let [] (bvl$Var 0)))
    (bvl$Let [] (bvl$Let [] (bvl$Var 0))))``);
