load "preamble"; load "word_to_stackProofTheory"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordPropsTheory
 wordSemTheory listTheory rich_listTheory sortingTheory sptreeTheory mllistTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val SORTS_SORT_key_val_compare = prove(``SORTS sort key_val_compare``,
  match_mp_tac sort_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare));
val list_rearrange_I = prove(``
  (list_rearrange I = I)``,
  fs [list_rearrange_def,FUN_EQ_THM]
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF,GENLIST_ID]);
val sourceStatement = ``
  !env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l``;
val replay = GEN_ALL(prove(sourceStatement,
  fs [env_to_list_def,LET_DEF,FUN_EQ_THM,list_rearrange_I] \\ rw []
  \\ pop_assum kall_tac
  \\ qspec_then `toAList env` mp_tac (SORTS_SORT_key_val_compare
        |> REWRITE_RULE [SORTS_DEF])
  \\ Q.SPEC_TAC (`sort key_val_compare (toAList env)`,`l`) \\ rw []
  \\ `PERM (MAP FST (toAList env)) (MAP FST l)` by (match_mp_tac PERM_MAP \\ fs [])
  \\ `ALL_DISTINCT (MAP FST l)` by metis_tac [ALL_DISTINCT_MAP_FST_toAList,
         sortingTheory.ALL_DISTINCT_PERM]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ Induct_on `l` \\ fs []
  \\ Cases_on `l` \\ fs [SORTED_DEF] \\ rw []
  \\ res_tac \\ fs [key_val_compare_def,LET_DEF]
  \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs []));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open environment theorem";
val _ = if aconv (concl replay) sourceStatement then () else raise Fail "statement drift";
val _ = (print "env_to_list_identity_statement="; print_term(concl replay); print "\n");
val _ = print("env_to_list_identity_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("env_to_list_identity_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
