load "bvi_tailrecProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then
    (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail ("hypotheses: " ^ label);
val _ = show_thm "input_condition_def_typed=" bvi_tailrecProofTheory.input_condition_def;
val _ = show_thm "compile_prog_semantics_typed=" bvi_tailrecProofTheory.compile_prog_semantics;
val _ = show_thm "compile_each_semantics_typed=" bvi_tailrecProofTheory.compile_each_semantics;
