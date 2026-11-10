(* Typed source statements for closure annotation correctness. *)
load "clos_annotateProofTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble clos_annotateTheory closPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "const_zero_typed=" clos_annotateTheory.const_0_def;
val _ = show "no_overlap_typed=" clos_annotateTheory.no_overlap_def;
val _ = show "alt_free_sing_typed=" clos_annotateTheory.alt_free_sing_def;
val _ = show "alt_free_def_typed=" clos_annotateTheory.alt_free_def;
val _ = show "alt_free_sing_eq_typed=" clos_annotateTheory.alt_free_sing_eq;
val _ = show "get_var_typed=" clos_annotateTheory.get_var_def;
val _ = show "shifted_env_typed=" clos_annotateTheory.shifted_env_def;
val _ = show "shift_def_typed=" clos_annotateTheory.shift_def;
val _ = show "shift_sing_eq_typed=" clos_annotateTheory.shift_sing_eq;
val _ = show "shift_sing_typed=" clos_annotateTheory.shift_sing_def;
val _ = show "annotate_def_typed=" clos_annotateTheory.annotate_def;
val _ = show "alt_fv_def_typed=" clos_annotateProofTheory.alt_fv_def;
val _ = show "alt_free_thm_typed=" clos_annotateProofTheory.alt_free_thm;
val _ = show "alt_fv1_def_typed=" clos_annotateProofTheory.alt_fv1_def;
val _ = show "alt_fv_nil_typed=" clos_annotateProofTheory.alt_fv_nil;
val _ = show "alt_fv_cons_typed=" clos_annotateProofTheory.alt_fv_cons;
val _ = show "alt_fv_REPLICATE_typed=" clos_annotateProofTheory.alt_fv_REPLICATE;
val _ = show "v_rel_rules_typed=" clos_annotateProofTheory.v_rel_rules;
val _ = show "annotate_sing_typed=" clos_annotateTheory.annotate_sing_def;
val _ = show "annotate_list_typed=" clos_annotateTheory.annotate_list_def;
val _ = show "annotate_sing_eq_typed=" clos_annotateTheory.annotate_sing_eq;
val _ = show "compile_def_typed=" clos_annotateTheory.compile_def;
val _ = show "compile_eq_typed=" clos_annotateTheory.compile_eq;
val _ = show "compile_inc_def_typed=" clos_annotateTheory.compile_inc_def;
val _ = show "compile_inc_eq_typed=" clos_annotateTheory.compile_inc_eq;
val _ = show "MAP_FST_compile_typed=" clos_annotateProofTheory.MAP_FST_compile;
val _ = show "semantics_annotate_typed=" clos_annotateProofTheory.semantics_annotate;
val _ = show "shift_obeys_max_app_typed=" clos_annotateProofTheory.shift_obeys_max_app;
val _ = show "alt_free_obeys_max_app_typed=" clos_annotateProofTheory.alt_free_obeys_max_app;
val _ = show "annotate_obeys_max_app_typed=" clos_annotateProofTheory.annotate_obeys_max_app;
val _ = show "obeys_max_app_ann_typed=" clos_annotateProofTheory.obeys_max_app_ann;
val _ = show "shift_no_Labels_typed=" clos_annotateProofTheory.shift_no_Labels;
val _ = show "alt_free_no_Labels_typed=" clos_annotateProofTheory.alt_free_no_Labels;
val _ = show "annotate_no_Labels_typed=" clos_annotateProofTheory.annotate_no_Labels;
val _ = show "no_Labels_ann_typed=" clos_annotateProofTheory.no_Labels_ann;
val _ = show "app_call_dests_def_typed=" closPropsTheory.app_call_dests_def;
val _ = show "app_call_dests_append_typed=" closPropsTheory.app_call_dests_append;
val _ = show "call_dests_shift_typed=" clos_annotateProofTheory.call_dests_shift;
val _ = show "code_locs_shift_typed=" clos_annotateProofTheory.code_locs_shift;
val _ = show "code_locs_alt_free_typed=" clos_annotateProofTheory.code_locs_alt_free;
val _ = show "code_locs_annotate_typed=" clos_annotateProofTheory.code_locs_annotate;
val _ = show "annotate_code_locs_typed=" clos_annotateProofTheory.annotate_code_locs;
val _ = show "code_locs_const_0_typed=" clos_annotateProofTheory.code_locs_const_0;
(* Replay the original local proofs: local declarations are not exported by
   clos_annotateProofTheory, so bind the first replay explicitly for the second. *)
val alt_free_code_locs_replay = prove (
  ``!xs. set (code_locs (FST (alt_free xs))) SUBSET set (code_locs xs)``,
  ho_match_mp_tac clos_annotateTheory.alt_free_ind
  >> simp[alt_free_def,code_locs_def,UNCURRY] >> rw[]
  >> Cases_on `alt_free [x]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free [x1]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free [x2]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free xs` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> fs[MAP_MAP_o,o_DEF,SUBSET_DEF,code_locs_def,GSYM MAP_K_REPLICATE]
  >> ONCE_REWRITE_TAC [code_locs_map]
  >> simp[MEM_FLAT,MEM_GENLIST,MEM_MAP,PULL_EXISTS,UNCURRY,HD_FST_alt_free]
  >> metis_tac[HD_FST_alt_free,FST,PAIR]);
val _ = show "alt_free_code_locs_local_typed=" alt_free_code_locs_replay;
val alt_free_code_locs_distinct_replay = prove (
  ``!xs. ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs (FST (alt_free xs)))``,
  recInduct alt_free_ind
  >> rw[alt_free_def,code_locs_def]
  >> rpt(pairarg_tac >> fs[])
  >> fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def] >> rw[]
  >> fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def,GSYM MAP_K_REPLICATE,code_locs_map,FLAT_MAP_NIL]
  >> TRY (
    rename1`GENLIST`
    >> fs[MEM_GENLIST,MAP_MAP_o,o_DEF,UNCURRY,HD_FST_alt_free,PULL_EXISTS]
    >> imp_res_tac alt_free_SING >> fs[] >> rveq
    >> fs[ALL_DISTINCT_FLAT,EL_MAP]
    >> fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >> rw[]
    >> metis_tac[SUBSET_DEF,alt_free_code_locs_replay,FST] )
  >> metis_tac[SUBSET_DEF,alt_free_code_locs_replay,FST,alt_free_SING,HD]);
val _ = show "alt_free_code_locs_distinct_local_typed=" alt_free_code_locs_distinct_replay;
val _ = show "code_locs_REP_const_0_typed=" clos_annotateProofTheory.code_locs_REP_const_0;
val _ = show "EVERY_shift_sing_typed=" clos_annotateProofTheory.EVERY_shift_sing;
val _ = show "HD_annotate_SING_typed=" clos_annotateProofTheory.HD_annotate_SING;
val _ = show "every_Fn_vs_SOME_shift_typed=" clos_annotateProofTheory.every_Fn_vs_SOME_shift;
val _ = show "every_Fn_vs_SOME_annotate_typed=" clos_annotateProofTheory.every_Fn_vs_SOME_annotate;
val _ = show "every_Fn_SOME_shift_typed=" clos_annotateProofTheory.every_Fn_SOME_shift;
val _ = show "every_Fn_SOME_const_0_typed=" clos_annotateProofTheory.every_Fn_SOME_const_0;
val _ = show "every_Fn_SOME_alt_free_typed=" clos_annotateProofTheory.every_Fn_SOME_alt_free;
val _ = show "every_Fn_SOME_annotate_typed=" clos_annotateProofTheory.every_Fn_SOME_annotate;
val _ = show "every_Fn_SOME_ann_typed=" clos_annotateProofTheory.every_Fn_SOME_ann;
(* env_set_default is local to the original proof script. *)
val env_set_default_replay = prove (
  ``x SUBSET clos_annotateProof$env_ok 0 0 sptree$LN [] env'``,
  full_simp_tac (srw_ss())
    [SUBSET_DEF, IN_DEF, clos_annotateProofTheory.v_rel_cases |> CONJUNCT2]);
val _ = show "env_set_default_local_typed=" env_set_default_replay;
(* Replay the local fold lemma using the original proof. *)
val foldr_mk_union_replay = prove (
  ``!ys aux l.
      FOLDR (\(x,l) (ts,alt_frees). (x::ts,db_vars$mk_Union l alt_frees)) (aux,l) ys =
      (MAP FST ys ++ aux, FOLDR db_vars$mk_Union l (MAP SND ys))``,
  Induct >> fs [FORALL_PROD]);
val _ = show "FOLDR_mk_Union_local_typed=" foldr_mk_union_replay;
(* Replay the local no-overlap bound from the source script. *)
val no_overlap_has_var_replay = prove (
  ``!n l2 x. clos_annotate$no_overlap n l2 /\ db_vars$has_var x l2 ==> n <= x``,
  Induct >> fs [no_overlap_def] >> rw [] >> res_tac
  >> Cases_on `x = n` >> fs []);
val _ = show "no_overlap_has_var_IMP_local_typed=" no_overlap_has_var_replay;
val _ = show "evaluate_shift_REPLICATE_const_0_typed=" clos_annotateProofTheory.evaluate_shift_REPLICATE_const_0;
(* Replay the source-local shifted-environment lookup proof. *)
val lookup_EL_shifted_env_replay = prove (
  ``!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
              (lookup (EL n y) (shifted_env k y) = SOME (k + n))``,
  Induct >> full_simp_tac(srw_ss())[] >> Cases_on `n`
  >> full_simp_tac(srw_ss())[shifted_env_def,sptreeTheory.lookup_insert]
  >> SRW_TAC [] [ADD1,AC ADD_COMM ADD_ASSOC]
  >> full_simp_tac(srw_ss())[MEM_EL] >> METIS_TAC []);
val _ = show "lookup_EL_shifted_env_local_typed=" lookup_EL_shifted_env_replay;
(* Replay the local elementwise shift/free-variable theorem. *)
val EL_shift_alt_free_replay = prove (
  ``!fns index. index < LENGTH fns ==>
      ([EL index (shift (FST (alt_free fns)) l m i)] =
       shift (FST (alt_free [EL index fns])) l m i)``,
  Induct >> full_simp_tac(srw_ss())[] >> REPEAT STRIP_TAC
  >> ONCE_REWRITE_TAC [alt_free_CONS]
  >> SIMP_TAC std_ss [Once shift_CONS]
  >> Cases_on `index` >> full_simp_tac(srw_ss())[]
  >> full_simp_tac(srw_ss())[LET_DEF,alt_free_def]
  >> REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  >> full_simp_tac(srw_ss())[SING_HD,LENGTH_FST_alt_free]);
val _ = show "EL_shift_alt_free_local_typed=" EL_shift_alt_free_replay;
(* Replay the local environment-compaction proof with its local prerequisites. *)
open closSemTheory;
val env_ok_def = clos_annotateProofTheory.v_rel_cases |> CONJUNCT2;
val lookup_EL_shifted_env = lookup_EL_shifted_env_replay;
val env_ok_shifted_env_replay = prove (
  ``clos_annotateProof$env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
    (lookup_vars (MAP (get_var m l i) (FILTER (\n. n < m + l) live)) env2 = SOME x) ==>
    clos_annotateProof$env_ok (m + l) 0 (shifted_env 0 (FILTER (\n. n < m + l) live)) env x k``,
  REPEAT STRIP_TAC
  >> Q.ABBREV_TAC `y = FILTER (\n. n < m + l) live`
  >> `ALL_DISTINCT y` by
       (UNABBREV_ALL_TAC >> MATCH_MP_TAC FILTER_ALL_DISTINCT >> full_simp_tac(srw_ss())[])
  >> Cases_on `~(k < m + l)` THEN1 (full_simp_tac(srw_ss())[env_ok_def,NOT_LESS] >> DECIDE_TAC)
  >> full_simp_tac(srw_ss())[]
  >> `MEM k y` by (UNABBREV_ALL_TAC >> full_simp_tac(srw_ss())[MEM_FILTER])
  >> POP_ASSUM MP_TAC
  >> simp [MEM_EL] >> STRIP_TAC
  >> POP_ASSUM (ASSUME_TAC o GSYM)
  >> Q.PAT_X_ASSUM `MEM k live` (K ALL_TAC)
  >> Q.PAT_X_ASSUM `Abbrev vvv` (K ALL_TAC)
  >> `(EL n (MAP (get_var m l i) y) = get_var m l i k) /\
      n < LENGTH (MAP (get_var m l i) y)` by full_simp_tac(srw_ss())[EL_MAP]
  >> Q.ABBREV_TAC `ys = (MAP (get_var m l i) y)`
  >> MP_TAC lookup_vars_MEM >> full_simp_tac(srw_ss())[] >> STRIP_TAC
  >> `clos_annotateProof$v_rel (EL k env) (EL (get_var m l i k) env2)` by
   (full_simp_tac(srw_ss())[env_ok_def] THEN1 (`F` by DECIDE_TAC) >> full_simp_tac(srw_ss())[get_var_def]
    >> `~(k < l)` by DECIDE_TAC >> full_simp_tac(srw_ss())[zlookup_def])
  >> Q.PAT_X_ASSUM `EL n x = yy` (ASSUME_TAC o GSYM) >> full_simp_tac(srw_ss())[]
  >> full_simp_tac(srw_ss())[env_ok_def] >> DISJ2_TAC
  >> TRY (`k < l + m` by DECIDE_TAC) >> full_simp_tac(srw_ss())[]
  >> SRW_TAC [] [] >> full_simp_tac(srw_ss())[lookup_EL_shifted_env]
  >> IMP_RES_TAC lookup_vars_SOME >> full_simp_tac(srw_ss())[]);
val _ = show "env_ok_shifted_env_local_typed=" env_ok_shifted_env_replay;
(* Replay the source-local extension lemma without relating the new prefixes. *)
val env_ok_EXTEND_IGNORE_replay = prove (
  ``(LENGTH env2 = LENGTH env1) /\ LENGTH env1 <= n /\ l1 = LENGTH env1 /\
    clos_annotateProof$env_ok m l i env1' env2' (n - l1) ==>
    clos_annotateProof$env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n``,
  SRW_TAC [] [] >> SIMP_TAC std_ss [env_ok_def] >> fs []
  >> Cases_on `n < LENGTH env1` >> fs []
  >> full_simp_tac(srw_ss())[NOT_LESS]
  >> full_simp_tac(srw_ss())[env_ok_def]
  >> fs [rich_listTheory.EL_APPEND2]);
val _ = show "env_ok_EXTEND_IGNORE_local_typed=" env_ok_EXTEND_IGNORE_replay;
(* Replay the corresponding extension proof for related prefixes. *)
val EVERY2_EL_local = LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst
                      |> UNDISCH |> CONJUNCT2 |> DISCH_ALL;
val env_ok_EXTEND_replay = prove (
  ``EVERY2 clos_annotateProof$v_rel env1 env2 /\ (l1 = LENGTH env1) /\
    (l1 <= n ==> clos_annotateProof$env_ok m l i env1' env2' (n - l1)) ==>
    clos_annotateProof$env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n``,
  SRW_TAC [] [] >> SIMP_TAC std_ss [env_ok_def]
  >> Cases_on `n < LENGTH env1` >> full_simp_tac(srw_ss())[] THEN1
   (DISJ2_TAC >> DISJ1_TAC >> REPEAT STRIP_TAC
    >> IMP_RES_TAC EVERY2_LENGTH
    >> full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]
    >> IMP_RES_TAC EVERY2_EL_local >> full_simp_tac(srw_ss())[] >> DECIDE_TAC)
  >> full_simp_tac(srw_ss())[NOT_LESS]
  >> full_simp_tac(srw_ss())[env_ok_def]
  THEN1 (DISJ1_TAC >> DECIDE_TAC)
  THEN1
   (DISJ2_TAC >> DISJ1_TAC
    >> IMP_RES_TAC EVERY2_LENGTH
    >> full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
    >> DECIDE_TAC)
  >> DISJ2_TAC >> DISJ2_TAC >> Q.EXISTS_TAC `v` >> full_simp_tac(srw_ss())[]
  >> IMP_RES_TAC EVERY2_LENGTH
  >> full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
  >> `n - (l + LENGTH env2) = n - LENGTH env2 - l` by DECIDE_TAC >> full_simp_tac(srw_ss())[]
  >> `LENGTH env2 <= l + LENGTH env2 + v` by DECIDE_TAC
  >> full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
  >> `l + LENGTH env2 + v - LENGTH env2 = l + v` by DECIDE_TAC >> full_simp_tac(srw_ss())[]
  >> DECIDE_TAC);
val _ = show "env_ok_EXTEND_local_typed=" env_ok_EXTEND_replay;
val _ = show "list_to_v_v_rel_typed=" clos_annotateProofTheory.list_to_v_v_rel;
(* Replay the local inversion theorem for primitive closure values. *)
val v_rel_Number_replay = prove (
  ``(clos_annotateProof$v_rel x (Number i) <=> (x = Number i)) /\
    (clos_annotateProof$v_rel (Number i) x <=> (x = Number i)) /\
    (clos_annotateProof$v_rel (ByteVector ws) x <=> (x = ByteVector ws)) /\
    (clos_annotateProof$v_rel x (Word64 w) <=> (x = Word64 w)) /\
    (clos_annotateProof$v_rel (Word64 w) x <=> (x = Word64 w))``,
  once_rewrite_tac [clos_annotateProofTheory.v_rel_cases] >> fs []);
val _ = show "v_rel_Number_local_typed=" v_rel_Number_replay;
(* Replay the local paired list-decoding theorem. *)
val v_to_list_replay = prove (
  ``!h h'. clos_annotateProof$v_rel h h' ==>
      (v_to_list h = NONE /\ v_to_list h' = NONE) \/
      ?x x'. (v_to_list h = SOME x) /\ (v_to_list h' = SOME x') /\
             EVERY2 clos_annotateProof$v_rel x x'``,
  HO_MATCH_MP_TAC v_to_list_ind
  >> full_simp_tac(srw_ss())[clos_annotateProofTheory.v_rel_simp]
  >> full_simp_tac(srw_ss())[v_to_list_def]
  >> REPEAT STRIP_TAC >> SRW_TAC [] []
  >> full_simp_tac(srw_ss())[v_to_list_def]
  >> Cases_on `v_to_list h'` >> full_simp_tac(srw_ss())[]
  >> Cases_on `v_to_list y'` >> full_simp_tac(srw_ss())[]
  >> CCONTR_TAC >> RES_TAC >> full_simp_tac(srw_ss())[]
  >> RES_TAC >> full_simp_tac(srw_ss())[] >> SRW_TAC [] [] >> fs[]);
val _ = show "v_to_list_local_typed=" v_to_list_replay;
val _ = show "v_to_bytes_typed=" clos_annotateProofTheory.v_to_bytes;
val _ = show "v_to_words_typed=" clos_annotateProofTheory.v_to_words;
val _ = show "REVERSE_compile_typed=" clos_annotateProofTheory.REVERSE_compile;
val _ = show "ALOOKUP_compile_typed=" clos_annotateProofTheory.ALOOKUP_compile;
val _ = show "compile_append_typed=" clos_annotateProofTheory.compile_append;
val _ = show "state_rel_def_typed=" clos_annotateProofTheory.state_rel_def;
val _ = show "do_install_thm_typed=" clos_annotateProofTheory.do_install_thm;
(* Replay the original local primitive simulation proof; it is not exported. *)
val do_app_lemma_replay = prove (
  ``state_rel s t /\ LIST_REL v_rel xs ys ==>
    case do_app opp xs s of
      Rval (x,s1) =>
        ?y t1. v_rel x y /\ state_rel s1 t1 /\ do_app opp ys t = Rval (y,t1)
    | Rerr err1 =>
        ?err2. do_app opp ys t = Rerr err2 /\ exc_rel v_rel err1 err2``,
  match_mp_tac simple_val_rel_do_app
  >> conj_tac >-
   (fs [simple_val_rel_def]
    >> once_rewrite_tac [clos_annotateProofTheory.v_rel_cases]
    >> fs [] >> rw [] >> fs [])
  >> fs [simple_state_rel_def,clos_annotateProofTheory.state_rel_def]
  >> rpt strip_tac >> fs [FLOOKUP_DEF]
  >- (`ref_rel v_rel (s.refs ' ptr) (t.refs ' ptr)` by fs []
    >> rpt (qpat_x_assum `!x. _` kall_tac) >> rfs []
    >> Cases_on `s.refs ' ptr` >> fs [ref_rel_def])
  >- (`ref_rel v_rel (s.refs ' ptr) (t.refs ' ptr)` by fs []
    >> rpt (qpat_x_assum `!x. _` kall_tac) >> rfs []
    >> Cases_on `s.refs ' ptr` >> fs [ref_rel_def])
  >- (`ref_rel v_rel (s.refs ' ptr) (t.refs ' ptr)` by fs []
    >> rpt (qpat_x_assum `!x. _` kall_tac) >> rfs []
    >> Cases_on `s.refs ' ptr` >> fs [ref_rel_def])
  >> rfs [] >> fs [FAPPLY_FUPDATE_THM] >> rveq
  >> fs [ref_rel_def] >> rw []);
val _ = show "do_app_lemma_local_typed=" do_app_lemma_replay;
val do_app_thm_replay = prove (
  ``state_rel s1 t1 /\ EVERY2 v_rel xs ys /\
    (do_app op xs s1 = Rval (v,s2)) ==>
    ?w t2. (do_app op ys t1 = Rval (w,t2)) /\
      v_rel v w /\ state_rel s2 t2``,
  rpt strip_tac
  >> drule (GEN_ALL do_app_lemma_replay)
  >> disch_then drule
  >> disch_then (qspec_then `op` mp_tac) >> fs []
  >> rpt strip_tac >> fs []);
val _ = show "do_app_thm_local_typed=" do_app_thm_replay;
(* Replay the source-local theorem, which is not exported by the theory. *)
val state_rel_clocks_eqs_replay = prove (
  ``state_rel s t ==> s.clock = t.clock``,
  gvs [clos_annotateProofTheory.state_rel_def]);
val _ = show "state_rel_clocks_eqs_local_typed=" state_rel_clocks_eqs_replay;
val _ = show "state_rel_max_app_typed=" clos_annotateProofTheory.state_rel_max_app;
val _ = show "annotate_correct_typed=" clos_annotateProofTheory.annotate_correct;
