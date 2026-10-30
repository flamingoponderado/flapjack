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
val evaluate_delete_var_Rval_replay = prove (``
  !xs env2 s a r ax env.
    evaluate (xs,env2,s:('c,'ffi) bvlSem$state) = (Rval a,r) /\
    env_rel (:'c) (:'ffi) ax env env2 ==>
    ?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
        env_rel (:'c) (:'ffi) (extract_list xs ++ ax) (a ++ env) (b ++ env2)``,
  Induct \\ fs [env_rel_def,extract_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ Cases_on `evaluate ([h],env2,s)` \\ fs []
  THEN1 (imp_res_tac evaluate_IMP_LENGTH \\ Cases_on `a` \\ fs [])
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `?i. h = Var i` \\ fs []
  THEN1
   (rw [] \\ fs [delete_var_def,evaluate_def,do_app_def,do_int_app_def]
   \\ gvs[AllCaseEqs()]
    \\ res_tac \\ fs [extract_def,env_rel_def] \\ rw []
    \\ fs [v_rel_def,LLOOKUP_EQ_EL]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ fs [GSYM ADD1,ADD_CLAUSES,EL_APPEND2])
  \\ `delete_var h = h` by (Cases_on `h` \\ fs [delete_var_def]) \\ fs []
  \\ Cases_on `evaluate (xs,env2,r')` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ Cases_on `extract h xs` \\ fs [env_rel_def]
  \\ imp_res_tac evaluate_SING \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs [extract_def]
  \\ rename1 `bvl_const$extract (Op opp ll) _ = SOME xx`
  \\ Cases_on `opp` \\ fs [extract_def]
  >| map Cases_on [`i`,`b'`] \\ fs [extract_def] \\ rw []
  \\ every_case_tac \\ fs []
  \\ fs [v_rel_def,NULL_EQ,evaluate_def,do_app_def,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]);
val _ = show "evaluate_delete_var_Rval_replay=" evaluate_delete_var_Rval_replay;
val _ = show "evaluate_env_rel=" evaluate_env_rel;
