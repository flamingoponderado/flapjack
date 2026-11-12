(* Replays the original local lemmas and general compiler proof, then applies
   its original specialization before the theorem name is rebound. *)
load "preamble";
load "bvl_handleProofTheory";
open HolKernel Parse boolLib bossLib preamble;
open bvlSemTheory bvlPropsTheory bvl_handleTheory bvl_handleProofTheory indexedListsTheory;
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 1000000;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val opt_lemma = Q.prove (`x = y <=> (x = SOME () <=> y = SOME ())`,
  Cases_on `x` \\ Cases_on `y` \\ fs []);

val OptionalLetLet_IMP = Q.prove (`(ys,l,s',nr') = OptionalLetLet y (LENGTH env) lx s1 limit nr /\
    (∀env2 extra.
      env_rel l env env2 ⇒ evaluate ([y],env2 ++ extra,s) = res) /\
    env_rel l env env1 /\ b ==>
    evaluate (ys,env1 ++ extra,s) = res /\ b`,
  rw [OptionalLetLet_def,evaluate_def]
  \\ drule evaluate_LetLet \\ fs []
  \\ fs [GSYM db_varsTheory.vars_flatten_def,GSYM db_varsTheory.vars_to_list_def]
  \\ sg `db_to_set (vars_flatten lx) = db_to_set lx` \\ fs []
  \\ fs [spt_eq_thm,db_varsTheory.wf_db_to_set]
  \\ rw [] \\ once_rewrite_tac [opt_lemma]
  \\ rewrite_tac [GSYM db_varsTheory.lookup_db_to_set]
  \\ fs []);

val general_compile_correct = Q.prove(`
  !xs env s1 ys env1 res s2 extra l s nr.
      compile limit (LENGTH env) xs = (ys,l,s,nr) /\ env_rel l env env1 /\
      (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) ==>
      (evaluate (ys,env1 ++ extra,s1) = (res,s2)) /\
      (nr ==> !e. res <> Rerr (Rraise e))`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def]
  \\ fs [LET_THM] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [env_rel_mk_Union]
  \\ imp_res_tac compile_sing \\ rveq
  \\ imp_res_tac env_rel_length
  \\ TRY
   (imp_res_tac OptionalLetLet_limit \\ rveq \\ fs []
    \\ drule (GEN_ALL OptionalLetLet_IMP)
    \\ disch_then match_mp_tac
    \\ fs [] \\ rpt strip_tac
    \\ fs [evaluate_def])
  THEN1 (* Cons *)
   (Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ Cases_on `q` \\ fs []
    \\ rw[] \\ fs[] \\ res_tac \\ fs []
    \\ SIMP_TAC std_ss [Once evaluate_CONS] \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs [] \\ rveq
    \\ `n < LENGTH env1 + LENGTH extra` by DECIDE_TAC
    \\ fs [evaluate_def,rich_listTheory.EL_APPEND1]
    \\ fs [env_rel_def,LIST_RELi_EL_EQN])
  THEN1 (* If *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs []
    \\ rveq \\ fs []
    \\ imp_res_tac OptionalLetLet_nr
    \\ rw [] \\ res_tac
    \\ Cases_on `Boolv T = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def]
    \\ Cases_on `Boolv F = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Let *)
   (Cases_on `LENGTH xs = 0` \\ fs [LENGTH_NIL,NULL_EQ] \\ rveq
    \\ fs [evaluate_def,env_rel_mk_Union] THEN1 metis_tac []
    \\ fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac OptionalLetLet_nr
    \\ TRY
     (res_tac \\ fs [evaluate_def]
      \\ `env_rel l2 (a ++ env) (a ++ env2)` by
       (fs [env_rel_def,LIST_RELi_EL_EQN] \\ rw []
        \\ Cases_on `i < LENGTH a` \\ fs [EL_APPEND1,NOT_LESS,EL_APPEND2] \\ NO_TAC)
      \\ res_tac \\ fs [] \\ NO_TAC)
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs []
    \\ `env_rel l2 (a ++ env) (a ++ env1)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN] \\ rw []
      \\ Cases_on `i < LENGTH a` \\ fs [EL_APPEND1,NOT_LESS,EL_APPEND2] \\ NO_TAC)
    \\ res_tac \\ fs [])
  THEN1 (* Raise *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ imp_res_tac OptionalLetLet_nr
    \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Handle *)
   (rpt gen_tac \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
    \\ rename1 `compile limit (LENGTH env) [x1] = ([yy],l1,s3)`
    \\ Cases_on `nr1` \\ fs [] \\ rveq
    THEN1
     (Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `e` \\ fs [] \\ rfs [] \\ rveq \\ fs [])
    \\ fs [evaluate_def,env_rel_mk_Union]
    \\ drule evaluate_LetLet \\ fs []
    \\ every_case_tac \\ fs [ADD1] \\ rw [] \\ rfs[]
    \\ `env_rel l2 (a::env) (a::env1)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN]
      \\ Cases \\ fs [ADD1]) \\ res_tac \\ fs [])
  THEN1 (* Op *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ Cases_on `op = ThunkOp ForceThunk` \\ gvs []
    >- (
      gvs [AllCaseEqs()]
      \\ rpt strip_tac
      \\ simp [evaluate_def] \\ gvs [])
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ imp_res_tac OptionalLetLet_nr
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs [evaluate_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac do_app_err \\ fs [] \\ res_tac \\ fs [])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [] \\ rw [evaluate_def] \\ res_tac \\ fs [])
  THEN1 (* Force *)
   (rw [] \\ gvs []
    \\ gvs [AllCaseEqs(), evaluate_def, PULL_EXISTS]
    \\ imp_res_tac env_rel_length \\ gvs [EL_APPEND]
    \\ gvs [oneline dest_thunk_def, AllCaseEqs(), PULL_EXISTS, env_rel_def,
            LIST_RELi_EL_EQN])
  THEN1 (* Call *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ imp_res_tac OptionalLetLet_nr
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s1)` \\ Cases_on `q` \\ fs [] \\ rw[]
    \\ res_tac \\ fs [evaluate_def]));
val exported_compile_correct = general_compile_correct
  |> Q.SPECL [`xs`,`env`,`s1`,`ys`,`env`,`res`,`s2`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL,env_rel_refl];
val _ = show "OptionalLetLet_IMP_replay" OptionalLetLet_IMP;
val _ = show "general_compile_correct_replay" general_compile_correct;
val _ = show "exported_compile_correct_352_replay" exported_compile_correct;
