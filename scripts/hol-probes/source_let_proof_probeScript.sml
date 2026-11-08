load "preamble"; load "source_letProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val env_c_lemma_replay = prove(
  ``(semanticPrimitives$extend_dec_env
       <|v := semanticPrimitives$build_rec_env q env env1; c := namespace$nsEmpty|> env).c = env.c``,
  fs [semanticPrimitivesTheory.extend_dec_env_def]);
val _ = show_thm "env_c_lemma_replay=" env_c_lemma_replay;
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
val nested_lifts = ``source_let$compile_decs
  [ast$Dmod «M» [ast$Dlet location$unknown_loc ast$Pany
    (ast$Let NONE (ast$Lit (ast$IntLit 1))
      (ast$Let (SOME «x») (ast$Lit (ast$IntLit 2)) (ast$Var (namespace$Short «x»))))]] =
  [ast$Dmod «M» [ast$Dlocal
    [ast$Dlet location$unknown_loc ast$Pany (ast$Lit (ast$IntLit 1));
     ast$Dlet location$unknown_loc (ast$Pvar «x») (ast$Lit (ast$IntLit 2))]
    [ast$Dlet location$unknown_loc ast$Pany (ast$Var (namespace$Short «x»))]]]``;
val _ = show_thm "nested_lifts=" (EVAL nested_lifts);
