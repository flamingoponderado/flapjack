load "evaluateTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "agrees_type="; print_type (type_of ``semanticPrimitives$compiler_agrees``); print "\n");
val _ = (print "eval_type="; print_type (type_of ``semanticPrimitives$do_eval``); print "\n");
val _ = (print "result_type="; print_type (type_of ``evaluate$do_eval_res``); print "\n");
val missing = rhs (concl (EVAL ``semanticPrimitives$do_eval [] NONE``));
val _ = (print "missing="; print_term missing; print "\n");
val oracle = rhs (concl (EVAL ``case semanticPrimitives$do_eval []
  (SOME (EvalOracle ((ARB:eval_oracle_state) with
    <| custom_do_eval := (λvs oc. SOME ((0,0),oc,[])); envs := [[ARB:v sem_env]]; generation := 0 |>))) of
  SOME (_,ds,SOME (EvalOracle s)) => SOME (LENGTH ds,s.generation,LENGTH s.envs) | _ => NONE``));
val _ = (print "oracle="; print_term oracle; print "\n");
val decs = rhs (concl (EVAL ``case semanticPrimitives$do_eval
  [Env (ARB:v sem_env) (2,3); Litv (IntLit 1); Litv (IntLit 0); Litv (IntLit 2);
    semanticPrimitives$list_to_v []; semanticPrimitives$list_to_v []]
  (SOME (EvalDecs <| compiler := (λ_. SOME (Litv (IntLit 2),[],[]));
    compiler_state := Litv (IntLit 1); env_id_counter := (2,3,9); decode_decs := (λ_. SOME []) |>)) of
  SOME (_,ds,SOME (EvalDecs s)) => SOME (LENGTH ds,s.env_id_counter) | _ => NONE``));
val _ = (print "decs="; print_term decs; print "\n");
val mismatch = rhs (concl (EVAL ``IS_SOME (semanticPrimitives$do_eval
  [Env (ARB:v sem_env) (2,3); Litv (IntLit 3); Litv (IntLit 0); Litv (IntLit 2);
    semanticPrimitives$list_to_v []; semanticPrimitives$list_to_v []]
  (SOME (EvalDecs <| compiler := (λ_. SOME (Litv (IntLit 2),[],[]));
    compiler_state := Litv (IntLit 1); env_id_counter := (2,3,9); decode_decs := (λ_. SOME []) |>)))``));
val _ = (print "mismatch="; print_term mismatch; print "\n");
val abort = rhs (concl (EVAL ``case SND (evaluate$do_eval_res []
  ((ARB:'ffi semanticPrimitives$state) with eval_state := NONE)) of
  Rerr (Rabort Rtype_error) => T | _ => F``));
val _ = (print "abort="; print_term abort; print "\n");
