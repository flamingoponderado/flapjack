load "source_evalProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "v_rel_abs=" source_evalProofTheory.v_rel_abs;
val _ = show_thm "compiler_fun=" source_evalProofTheory.mk_compiler_fun_from_ci_def;
val _ = show_thm "init_eval=" source_evalProofTheory.mk_init_eval_state_def;
val _ = show_thm "insert=" source_evalProofTheory.insert_gen_oracle_def;
val _ = show_thm "adjust=" source_evalProofTheory.adjust_oracle_def;
val _ = show_thm "is_insert=" source_evalProofTheory.is_insert_oracle_def;
val _ = show_thm "adjust_insert=" source_evalProofTheory.adjust_oracle_insert_gen_oracle;
