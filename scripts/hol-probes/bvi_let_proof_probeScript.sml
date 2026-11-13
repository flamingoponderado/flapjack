load "bvi_letProofTheory";
load "preamble";
open preamble bvi_letProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print "="; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "v_rel" v_rel_def;
val _ = show "env_rel" env_rel_def;
val _ = show "env_rel_length" env_rel_length;
val _ = show "env_rel_MAP" env_rel_MAP;
val _ = show "evaluate_env_rel" evaluate_env_rel;
val _ = show "compile_thm" compile_thm;
val _ = show "evaluate_compile_exp" evaluate_compile_exp;
val _ = show "dest_var_code_labels" dest_var_code_labels;
val _ = show "compile_code_labels" compile_code_labels;
val _ = show "compile_exp_code_labels" compile_exp_code_labels;
(* Replay the original local prefix relation proof. *)
val env_rel_REPLICATE_0_replay = Q.prove
  (`!vs ax d env1 env2.
      env_rel ax d env1 env2 ==>
      env_rel (REPLICATE (LENGTH vs) 0 ++ ax) d (vs ++ env1) (vs ++ env2)`,
   Induct \\ fs [REPLICATE, env_rel_def, v_rel_def, LLOOKUP_def]);
val _ = show "env_rel_REPLICATE_0_replay" env_rel_REPLICATE_0_replay;
val _ = show "bvi_exp_size_def" bviTheory.exp_size_def;
val _ = show "exp_size_APPEND" bvi_letProofTheory.exp_size_APPEND;
val _ = show "IMP_COMM" bvi_letProofTheory.IMP_COMM;
val _ = show "compile_APPEND" bvi_letProofTheory.compile_APPEND;
val _ = show "compile_CONS" bvi_letProofTheory.compile_CONS;
val _ = show "evaluate_SNOC_Rval" bvi_letProofTheory.evaluate_SNOC_Rval;
(* Replay the original local relation/lookup proof. *)
val env_rel_LOOKUP_SOME_replay = Q.prove
  (`!env env2 ax x n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = SOME x ==>
      v_rel x (EL n env) (EL n env2) (DROP n env) (DROP n env2)`,
   Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
   \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
   \\ Cases_on `n` \\ fs [env_rel_def]
   \\ first_x_assum match_mp_tac
   \\ Cases_on `h'` \\ fs [env_rel_def]);
val _ = show "env_rel_LOOKUP_SOME_replay" env_rel_LOOKUP_SOME_replay;
(* Replay the original local unmapped-index proof. *)
val env_rel_LLOOKUP_NONE_replay = Q.prove
  (`!ax env env2 n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = NONE /\
      n < LENGTH env ==>
      n+d < LENGTH env2 /\
      EL (n+d) env2 = EL n env`,
   Induct THEN1 (fs [env_rel_def,LLOOKUP_def,EL_DROP])
   \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
   \\ rw [] \\ Cases_on `n` \\ fs []
   \\ res_tac \\ fs [LLOOKUP_def] \\ rfs [] \\ fs [ADD_CLAUSES]);
val _ = show "env_rel_LLOOKUP_NONE_replay" env_rel_LLOOKUP_NONE_replay;
