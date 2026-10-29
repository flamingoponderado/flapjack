load "source_letProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "lift_prefix=" source_letProofTheory.lift_lets_is_prefix;
val local_let_lifting = prove(
  ``(!ds1 ds2. source_let$lift_lets [] (Dlocal ds1 ds2) = NONE) /\
    (!mn ds. source_let$lift_lets [] (Dmod mn ds) = NONE)``,
  once_rewrite_tac [source_letTheory.lift_lets_def] \\ simp [source_letTheory.lift_let_def]);
val _ = show_thm "lift_modules_locals=" local_let_lifting;
val _ = show_thm "lift_single_evaluation=" source_letProofTheory.evaluate_lift_let;
val _ = show_thm "lift_all_evaluation=" source_letProofTheory.evaluate_lift_lets;
val _ = show_thm "compile_declarations=" source_letProofTheory.compile_decs_correct;
val _ = show_thm "compile_semantics=" source_letProofTheory.compile_semantics;
