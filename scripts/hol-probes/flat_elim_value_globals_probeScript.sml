load "flat_elimProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "value_globals=" flat_elimProofTheory.find_v_globals_def;
val _ = show_thm "refs_globals=" flat_elimProofTheory.find_refs_globals_def;
val _ = show_thm "env_globals=" flat_elimProofTheory.find_env_globals_def;
val _ = show_thm "result_globals=" flat_elimProofTheory.find_result_globals_def;
val _ = show_thm "primitive_result_globals=" flat_elimProofTheory.find_sem_prim_res_globals_def;
val _ = show_thm "value_has_eval=" flat_elimProofTheory.v_has_Eval_def1;
val _ = show_thm "globals_relation=" flat_elimProofTheory.globals_rel_def;
val _ = show_thm "globals_transitivity=" flat_elimProofTheory.globals_rel_trans;
val _ = show_thm "state_relation=" flat_elimProofTheory.flat_state_rel_def;
val _ = show_thm "state_transitivity=" flat_elimProofTheory.flat_state_rel_trans;
val _ = show_eval "closure_lookup=" ``sptree$lookup 3 (flat_elimProof$find_v_globals (flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$GlobalVarLookup 3) [])))``;
val _ = show_eval "tuple_lookup=" ``sptree$lookup 3 (flat_elimProof$find_v_globals (flatSem$Conv NONE [flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$GlobalVarLookup 3) [])]))``;
val _ = show_eval "closure_eval=" ``flat_elimProof$v_has_Eval (flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$Src ast$Eval) []))``;
