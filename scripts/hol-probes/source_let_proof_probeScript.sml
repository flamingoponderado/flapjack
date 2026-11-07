load "preamble"; load "source_letProofTheory";
open HolKernel Parse boolLib bossLib preamble;
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
val _ = show_thm "compile_semantics_oracle=" source_letProofTheory.compile_semantics_oracle;
val lift_start = Q.SPEC `[]` source_letProofTheory.evaluate_lift_lets
  |> SIMP_RULE (srw_ss()) [Once semanticPrimitivesTheory.extend_dec_env_def];
val _ = show_thm "lift_start=" lift_start;
val _ = show_thm "dest_let_definition=" source_letTheory.dest_Let_def;
val _ = show_thm "dest_letrec_definition=" source_letTheory.dest_Letrec_def;
val _ = show_thm "lift_let_definition=" source_letTheory.lift_let_def;
val _ = show_thm "lift_lets_definition=" source_letTheory.lift_lets_def;
val _ = show_thm "compile_decs_definition=" source_letTheory.compile_decs_def;
