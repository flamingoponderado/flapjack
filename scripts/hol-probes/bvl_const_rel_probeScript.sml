load "bvl_constProofTheory";
load "preamble";
open preamble bvl_constProofTheory bvl_constTheory bvlSemTheory bvlPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "value_rel=" v_rel_def;
val _ = show "env_rel=" env_rel_def;
val _ = show "env_rel_length=" env_rel_length;
val env_rel_LLOOKUP_NONE_replay = prove (``
  !ax env env2 n.
    env_rel (:'c) (:'ffi) ax env env2 /\
    (LLOOKUP ax n = NONE \/ LLOOKUP ax n = SOME NONE) ==>
    EL n env2 = EL n env``,
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [] \\ Cases_on `n` \\ fs [EL]);
val _ = show "env_rel_LLOOKUP_NONE_replay=" env_rel_LLOOKUP_NONE_replay;
val env_rel_LOOKUP_SOME_replay = prove (``
  !env env2 ax x n.
    env_rel (:'c) (:'ffi) ax env env2 /\
    LLOOKUP ax n = SOME (SOME x) ==>
    v_rel (:'c) (:'ffi) x (EL n env) (EL n env2) (DROP n env) (DROP n env2)``,
  Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
  \\ Cases_on `n` \\ fs [env_rel_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `h'` \\ fs [env_rel_def]);
val _ = show "env_rel_LOOKUP_SOME_replay=" env_rel_LOOKUP_SOME_replay;
val _ = show "evaluate_delete_var_Rerr_SING=" evaluate_delete_var_Rerr_SING;
val evaluate_delete_var_Rerr_replay = prove (``
  !xs s r e env2.
    evaluate (xs,env2,s) = (Rerr e,r) /\
    e <> Rabort Rtype_error ==>
    evaluate (MAP bvl_const$delete_var xs,env2,s) = (Rerr e,r)``,
  Induct \\ fs [] \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (drule evaluate_delete_var_Rerr_SING \\ fs [])
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [delete_var_def]
  \\ rw [] \\ fs []
  \\ fs [evaluate_def,do_app_def,do_int_app_def] \\ rw []
  \\ fs[AllCaseEqs()]);
val _ = show "evaluate_delete_var_Rerr_replay=" evaluate_delete_var_Rerr_replay;
val _ = show "evaluate_env_rel=" evaluate_env_rel;
