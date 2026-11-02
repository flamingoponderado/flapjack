load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "nat_to_value_definition=" semanticPrimitivesTheory.nat_to_v_def;
val _ = show_thm "lookup_definition=" semanticPrimitivesTheory.lookup_env_def;
val _ = show_thm "add_decs_definition=" semanticPrimitivesTheory.add_decs_generation_def;
val _ = show_thm "add_env_definition=" semanticPrimitivesTheory.add_env_generation_def;
val _ = show_thm "declare_definition=" semanticPrimitivesTheory.declare_env_def;
val _ = show_thm "reset_definition=" semanticPrimitivesTheory.reset_env_generation_def;
val _ = (print "declare_type="; print_type (type_of ``semanticPrimitives$declare_env``); print "\n");
val _ = (print "reset_type="; print_type (type_of ``semanticPrimitives$reset_env_generation``); print "\n");
val decs = rhs (concl (EVAL ``(semanticPrimitives$add_decs_generation
  ((ARB:eval_decs_state) with env_id_counter := (2,3,9))).env_id_counter``));
val _ = (print "decs="; print_term decs; print "\n");
val oracle = rhs (concl (EVAL ``let s = semanticPrimitives$add_env_generation
  ((ARB:eval_oracle_state) with <| envs := [[]; []]; generation := 8 |>) in
  (s.generation,LENGTH s.envs)``));
val _ = (print "oracle="; print_term oracle; print "\n");
val lookup = rhs (concl (EVAL ``IS_SOME (semanticPrimitives$lookup_env
  ((ARB:eval_oracle_state) with envs := [[ARB:v sem_env]]) (0,0))``));
val _ = (print "lookup="; print_term lookup; print "\n");
val invalid_lookup = rhs (concl (EVAL ``IS_SOME (semanticPrimitives$lookup_env
  ((ARB:eval_oracle_state) with envs := [[ARB:v sem_env]]) (1,0))``));
val _ = (print "invalid_lookup="; print_term invalid_lookup; print "\n");
val invalid_inner_lookup = rhs (concl (EVAL ``IS_SOME (semanticPrimitives$lookup_env
  ((ARB:eval_oracle_state) with envs := [[ARB:v sem_env]]) (0,1))``));
val _ = (print "invalid_inner_lookup="; print_term invalid_inner_lookup; print "\n");
val declared_decs = rhs (concl (EVAL ``case semanticPrimitives$declare_env
  (SOME (EvalDecs ((ARB:eval_decs_state) with env_id_counter := (2,3,9)))) (ARB:v sem_env) of
    SOME (Env _ id,SOME (EvalDecs s)) => SOME (id,s.env_id_counter) | _ => NONE``));
val _ = (print "declared_decs="; print_term declared_decs; print "\n");
val declared_oracle = rhs (concl (EVAL ``case semanticPrimitives$declare_env
  (SOME (EvalOracle ((ARB:eval_oracle_state) with <|envs := [[ARB:v sem_env]]; generation := 0|>))) (ARB:v sem_env) of
    SOME (Conv NONE [Litv (IntLit a); Litv (IntLit b)],SOME (EvalOracle s)) =>
      SOME (a,b,LENGTH (EL 0 s.envs)) | _ => NONE``));
val _ = (print "declared_oracle="; print_term declared_oracle; print "\n");
val invalid_decl = rhs (concl (EVAL ``IS_SOME (semanticPrimitives$declare_env
  (SOME (EvalOracle ((ARB:eval_oracle_state) with <|envs := [[]]; generation := 1|>))) (ARB:v sem_env))``));
val _ = (print "invalid_decl="; print_term invalid_decl; print "\n");
val reset = rhs (concl (EVAL ``case semanticPrimitives$reset_env_generation
  (SOME (EvalDecs ((ARB:eval_decs_state) with env_id_counter := (2,3,9))))
  (SOME (EvalDecs ((ARB:eval_decs_state) with env_id_counter := (4,5,11)))) of
    SOME (EvalDecs s) => SOME s.env_id_counter | _ => NONE``));
val _ = (print "reset="; print_term reset; print "\n");
val reset_mixed = rhs (concl (EVAL ``case semanticPrimitives$reset_env_generation
  (SOME (EvalDecs (ARB:eval_decs_state)))
  (SOME (EvalOracle ((ARB:eval_oracle_state) with generation := 7))) of
    SOME (EvalOracle s) => SOME s.generation | _ => NONE``));
val _ = (print "reset_mixed="; print_term reset_mixed; print "\n");
