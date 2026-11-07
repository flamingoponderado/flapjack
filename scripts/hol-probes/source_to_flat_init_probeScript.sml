load "preamble"; load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val fst_pair_map_i_replay = Q.prove (
  `FST ((I ## f) x) = FST x`, Cases_on `x` \\ simp []);
val _ = show_thm "fst_pair_map_i_replay=" fst_pair_map_i_replay;
val _ = show_thm "opt_bind_definition_typed=" miscTheory.opt_bind_def;
val opt_bind_lem_replay = Q.prove (
  `misc$opt_bind NONE = \x y. y`, rw [FUN_EQ_THM, miscTheory.opt_bind_def]);
val _ = show_thm "opt_bind_lem_replay=" opt_bind_lem_replay;
val env_updated_lem_replay = Q.prove (
  `env with v updated_by (\y. y) = (env : 'a flatSem$environment)`,
  rw [flatSemTheory.environment_component_equality]);
val _ = show_thm "env_updated_lem_replay=" env_updated_lem_replay;
val _ = show_thm "all_disjoint_cons_typed=" source_to_flatProofTheory.ALL_DISJOINT_CONS;
val _ = show_thm "idx_types_forall_typed=" source_to_flatProofTheory.idx_types_FORALL;
val _ = show_thm "bind_locals_fold_typed=" source_to_flatProofTheory.bind_locals_fold_nsBind;
val _ = show_thm "bool_value_injective_typed=" source_to_flatProofTheory.Boolv_11;
val _ = show_thm "evaluate_bool_typed=" source_to_flatProofTheory.evaluate_Bool;
val opt_case_bool_eq_replay = Q.prove (
  `option_CASE opt nc scc <=> (opt = NONE /\ nc) \/ (?x. opt = SOME x /\ scc x)`,
  Cases_on `opt` >> simp []);
val _ = show_thm "opt_case_bool_eq_replay=" opt_case_bool_eq_replay;
val _ = show_thm "all_disjoint_move_typed=" source_to_flatProofTheory.ALL_DISJOINT_MOVE;
val _ = show_thm "all_disjoint_subsets_typed=" source_to_flatProofTheory.ALL_DISJOINT_SUBSETS;
val _ = show_thm "pmatch_invariant_typed=" source_to_flatProofTheory.pmatch_invariant;
val alookup_alloc_defs_el_replay = Q.prove (
  `!funs l n m. ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\ n < LENGTH funs ==>
    ?tt. ALOOKUP (source_to_flat$alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
      SOME (source_to_flat$Glob tt (l + LENGTH funs - (n + 1)))`,
  gen_tac >> Induct_on `LENGTH funs` >> rw [] >> Cases_on `REVERSE funs` >>
  fs [source_to_flatTheory.alloc_defs_def] >> rw []
  >- (`LENGTH funs = n + 1` suffices_by decide_tac >>
      rfs [EL_MAP] >> `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
      fs [] >> rw [] >> CCONTR_TAC >> fs [] >> `n < LENGTH t` by decide_tac >>
      fs [EL_APPEND1, miscTheory.FST_triple] >>
      fs [ALL_DISTINCT_APPEND, MEM_MAP, FORALL_PROD] >> fs [MEM_EL, EL_REVERSE] >>
      `PRE (LENGTH t - n) < LENGTH t` by decide_tac >>
      fs [METIS_PROVE [] ``~x \/ y <=> x ==> y``] >> metis_tac [FST, pair_CASES, PAIR_EQ])
  >- (`funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >> fs [] >> rw [] >>
      Cases_on `n = LENGTH t` >> fs [EL_APPEND2] >> `n < LENGTH t` by decide_tac >>
      fs [EL_APPEND1, ADD1] >> first_x_assum (qspec_then `REVERSE t` mp_tac) >> simp [] >>
      fs [ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MAP_REVERSE] >>
      disch_then (qspec_then `l+1` assume_tac) >> fs []));
val _ = show_thm "alookup_alloc_defs_el_replay=" alookup_alloc_defs_el_replay;
val el_add_some_some_replay = Q.prove (
  `EL i (pre ++ MAP SOME xs ++ post) <> NONE <=>
    (EL i (pre ++ REPLICATE (LENGTH xs) NONE ++ post) <> NONE \/
      (LENGTH pre <= i /\ i < LENGTH pre + LENGTH xs))`,
  simp [source_to_flatProofTheory.EL_APPEND_IF] >> rw [] >> fs [EL_MAP]);
val _ = show_thm "el_add_some_some_replay=" el_add_some_some_replay;
val _ = show_thm "el_append_if_typed=" source_to_flatProofTheory.EL_APPEND_IF;
val _ = show_thm "all_disjoint_elem_typed=" source_to_flatProofTheory.ALL_DISJOINT_elem;
val _ = show_thm "all_disjoint_definition_typed=" source_to_flatProofTheory.ALL_DISJOINT_DEF;
val fst_snd_eq_case_replay = Q.prove (
  `FST = (\ (a, b). a) /\ SND = (\ (a, b). b)`,
  simp [FUN_EQ_THM, FORALL_PROD]);
val _ = show_thm "fst_snd_eq_case_replay=" fst_snd_eq_case_replay;
val _ = show_thm "inj_definition_typed=" pred_setTheory.INJ_DEF;
val _ = show_thm "some_f_inj_eq_typed=" source_to_flatProofTheory.some_f_inj_eq;
val _ = show_thm "alloc_tags_invariant_typed=" source_to_flatProofTheory.alloc_tags_invariant;
val _ = show_thm "alookup_map_3_typed=" source_to_flatProofTheory.ALOOKUP_MAP_3;
val _ = show_thm "alloc_tags1_imp_typed=" source_to_flatProofTheory.alloc_tags1_imp;
val nsAppend_foldl_prime_replay = Q.prove (
  `!l ns ns'. nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) ns' l) ns =
    FOLDL (\ns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  Induct_on `l` >> rw [] >> PairCases_on `h` >> rw []);
val _ = show_thm "nsAppend_foldl_prime_replay=" nsAppend_foldl_prime_replay;
val nsAppend_foldl_replay = Q.prove (
  `!l ns. FOLDL (\ns (l,cids). nsAppend l ns) ns l =
    nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty l) ns`,
  metis_tac [nsAppend_foldl_prime_replay, namespacePropsTheory.nsAppend_nsEmpty]);
val _ = show_thm "nsAppend_foldl_replay=" nsAppend_foldl_replay;
val build_tdefs_no_mod_replay = Q.prove (
  `!idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}`,
  Induct_on `tdefs` >> rw [semanticPrimitivesTheory.build_tdefs_def] >>
  PairCases_on `h` >> rw [semanticPrimitivesTheory.build_tdefs_def] >>
  pop_assum (qspec_then `idx+1` mp_tac) >> rw [namespacePropsTheory.nsDomMod_nsAppend_flat]);
val _ = show_thm "build_tdefs_no_mod_replay=" build_tdefs_no_mod_replay;
val _ = show_thm "abort_simps_typed=" source_to_flatProofTheory.abort_simps;
val _ = show_thm "nsLookup_nsBind_If_typed=" source_to_flatProofTheory.nsLookup_nsBind_If;
val not_abort_imp_cases_replay = Q.prove (
  `(~ source_to_flatProof$abort r ==> P) ==>
    ((?a. r = Rerr (Rabort a)) \/ (~ source_to_flatProof$abort r /\ P))`,
  simp [source_to_flatProofTheory.abort_def] >> every_case_tac >> simp []);
val _ = show_thm "not_abort_imp_cases_replay=" not_abort_imp_cases_replay;
val _ = show_thm "eval_state_ok=" source_to_flatProofTheory.init_eval_state_ok_def;
val _ = show_thm "type_entries=" source_to_flatProofTheory.init_genv_ty_els_def;
val _ = show_thm "constructor_entries=" source_to_flatProofTheory.init_genv_els_def;
val _ = show_thm "initial_env=" source_to_flatProofTheory.init_genv_def;
val _ = show_thm "initial_next=" source_to_flatProofTheory.init_genv_next;
val _ = show_thm "initial_global_inv=" source_to_flatProofTheory.init_global_env_inv_def;
val _ = show_thm "initial_global_imp=" source_to_flatProofTheory.init_global_env_inv_imp;
val _ = show_thm "precondition1=" source_to_flatProofTheory.precondition1_def;
val _ = show_thm "precondition1_change_clock=" source_to_flatProofTheory.precondition1_change_clock;
val _ = show_thm "precondition=" source_to_flatProofTheory.precondition_def;
val _ = show_thm "source_compile_semantics=" source_to_flatProofTheory.compile_semantics;
val _ = show_thm "source_compile_flat_correct=" source_to_flatProofTheory.compile_flat_correct;
val _ = show_thm "source_compile_correct=" source_to_flatProofTheory.compile_correct;
val _ = show_thm "source_compile_prog=" source_to_flatTheory.compile_prog_def;
val _ = show_thm "source_glob_alloc=" source_to_flatTheory.glob_alloc_def;
val _ = show_thm "source_alloc_env_ref=" source_to_flatTheory.alloc_env_ref_def;
val _ = show_thm "source_lookup_env_id=" source_to_flatTheory.lookup_env_id_def;
val _ = show_thm "source_store_env_id=" source_to_flatTheory.store_env_id_def;
val _ = show_thm "source_inc_compile_prog=" source_to_flatTheory.inc_compile_prog_def;
val _ = show_thm "spt_from_list=" sptreeTheory.fromList_def;
(* Initial environment theorem captures include HOL's inferred types. *)
val _ = show_thm "initial_env_ok=" source_to_flatProofTheory.init_genv_ok;
val _ = show_thm "initial_types_ok=" source_to_flatProofTheory.init_genv_tys_ok;
val _ = show_thm "keep_global_allocation=" source_to_flatProofTheory.keep_glob_alloc;
val _ = show_thm "elimination_keep=" flat_elimTheory.keep_def;
val _ = show_thm "incremental_nonempty=" source_to_flatProofTheory.inc_compile_prog_nonempty;
val _ = show_thm "flat_initial_state=" flatSemTheory.initial_state_def;
val _ = show_thm "flat_semantics=" flatSemTheory.semantics_def;
val _ = show_thm "compile_flat=" source_to_flatTheory.compile_flat_def;
val _ = show_thm "compile=" source_to_flatTheory.compile_def;
val _ = show_thm "incremental_compile=" source_to_flatTheory.inc_compile_def;
val _ = show_eval "evaluated_entries=" ``source_to_flatProof$init_genv_els``;
val _ = show_eval "evaluated_next=" ``source_to_flatProof$init_genv_next``;
val _ = show_eval "program_nonzero_next=" ``
  let c = source_to_flat$empty_config with
    next := (source_to_flat$empty_config.next with vidx := 4n) in
  let (c', code) = source_to_flat$compile_prog c [] in
    (c'.next.vidx, c'.envs.next, code)``;
val _ = show_eval "incremental_nonzero_next=" ``
  let c = source_to_flat$empty_config with
    next := (source_to_flat$empty_config.next with vidx := 4n) in
  let (c', code) = source_to_flat$inc_compile_prog (3n, 7n) c [] in
    (c'.next.vidx, c'.envs.next, code)``;
val _ = show_eval "incremental_empty=" ``SND (source_to_flat$inc_compile (0n,0n) source_to_flat$empty_config [])``;
val _ = show_thm "invariant_begin_alloc_blanks=" source_to_flatProofTheory.invariant_begin_alloc_blanks;
val _ = show_thm "invariant_imp_state_rel=" source_to_flatProofTheory.invariant_IMP_s_rel;
(* Replay the original local theorem, which is not exported by its theory. *)
val precondition_stamp_helper_local = Q.prove (
  `EVERY (\(_, stamp). case stamp of TypeStamp cn t => t < type_stamp
     | ExnStamp cn => cn < exn_stamp) source_to_flatProof$init_genv_els ==>
   (∀cn t. t ≥ type_stamp ==> TypeStamp cn t ∉ FRANGE (source_to_flatProof$init_genv).c) ∧
   (∀cn. cn ≥ exn_stamp ==> ExnStamp cn ∉ FRANGE (source_to_flatProof$init_genv).c)`,
  rw [source_to_flatProofTheory.init_genv_def] >> CCONTR_TAC >> fs [] >>
  dxrule_then assume_tac
    (MATCH_MP miscTheory.SUBSET_IMP (SPEC_ALL finite_mapTheory.FRANGE_FUPDATE_LIST_SUBSET)) >>
  fs [listTheory.MEM_MAP, pairTheory.EXISTS_PROD, listTheory.EVERY_MEM] >>
  res_tac >> fs []);
val _ = show_thm "precondition_stamp_helper_local=" precondition_stamp_helper_local;
val invariant_env_gen_inv_local = Q.prove (
  `source_to_flatProof$invariant interp g gen genv (idx,end_idx,os) s s_i1 ==>
   source_to_flatProof$env_gen_inv gen`,
  simp [source_to_flatProofTheory.invariant_def]);
val _ = show_thm "invariant_env_gen_inv_local=" invariant_env_gen_inv_local;
val abort_compile_dec_result_local = Q.prove (
  `source_to_flatProof$abort (semanticPrimitives$combine_dec_result env r) = source_to_flatProof$abort r`,
  Cases_on `r` >> simp [semanticPrimitivesTheory.combine_dec_result_def]);
val _ = show_thm "abort_compile_dec_result_local=" abort_compile_dec_result_local;

val _ = show_thm "declare_env_store_env_id=" source_to_flatProofTheory.declare_env_store_env_id;
val _ = show_thm "compile_funs_dom2=" source_to_flatProofTheory.compile_funs_dom2;
val _ = show_thm "nsAppend_to_nsBindList=" namespacePropsTheory.nsAppend_to_nsBindList;

load "preamble";
open preamble semanticPrimitivesTheory source_to_flatTheory namespaceTheory;
val find_recfun_local = Q.prove (
  `!x funs e comp_map y t.
    find_recfun x funs = SOME (y,e) ==>
    find_recfun x (compile_funs t comp_map funs) =
      SOME (y, compile_exp (x::t) (comp_map with v := nsBind y (Local None y) comp_map.v) e)`,
  induct_on `funs` >>
  srw_tac[][Once find_recfun_def, compile_exp_def] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]);
val _ = show_thm "find_recfun_local=" find_recfun_local;
val _ = show_thm "nsAppend_assoc=" namespacePropsTheory.nsAppend_assoc;
val _ = show_thm "nsLookup_nsBind=" namespacePropsTheory.nsLookup_nsBind;
val _ = show_thm "build_rec_env_merge=" semanticPrimitivesPropsTheory.build_rec_env_merge;
val _ = show_thm "nsAppend_nsEmpty=" namespacePropsTheory.nsAppend_nsEmpty;

(* Typed parsing of the local theorem; this does not replay its HOL proof. *)
val global_env_inv_extend_typed = ``!pat_env genv pat_env' tt g1 g2.
  source_to_flatProof$env_rel genv (namespace$alist_to_ns pat_env) pat_env' /\
  genv.v = g1 ++ MAP SOME (REVERSE (MAP SND pat_env')) ++ g2 /\
  ALL_DISTINCT (MAP FST pat_env) ==>
  source_to_flatProof$global_env_inv genv
    <|c := namespace$nsEmpty;
      v := namespace$alist_to_ns (source_to_flat$alloc_defs tt (LENGTH g1)
        (REVERSE (MAP FST pat_env')))|>
    {} <|v := namespace$alist_to_ns pat_env; c := namespace$nsEmpty|>``;
val _ = (print "global_env_inv_extend_typed="; print_term global_env_inv_extend_typed; print "\n");

(* Replay the original local allocation-lookup theorem. *)
open alistTheory listTheory source_to_flatTheory;
val alookup_alloc_defs_local = Q.prove (
  `!env x v l tt.
    ALOOKUP (REVERSE env) x = SOME v ==>
    ?n t. ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME (Glob t (l + n)) /\
      n < LENGTH (MAP FST env) /\
      EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v`,
  Induct_on `env` >>
  rw [ALOOKUP_APPEND, alloc_defs_append] >>
  every_case_tac >> fs [alloc_defs_def] >-
    (PairCases_on `h` >> fs [EL_APPEND_EQN]) >-
    (PairCases_on `h` >> fs [] >> first_x_assum drule >>
     disch_then (qspecl_then [`l`,`tt`] mp_tac) >> rw []) >-
    (PairCases_on `h` >> fs [] >> rw [] >> fs [ALOOKUP_NONE, MAP_REVERSE] >>
     drule ALOOKUP_MEM >> rw [] >>
     `MEM h0 (MAP FST (alloc_defs tt l (REVERSE (MAP FST env))))`
       by (rw [MEM_MAP] >> metis_tac [FST]) >> fs [fst_alloc_defs]) >-
    (first_x_assum drule >> disch_then (qspecl_then [`l`,`tt`] mp_tac) >> rw [EL_APPEND_EQN]));
val _ = show_thm "alookup_alloc_defs_local=" alookup_alloc_defs_local;

val _ = show_thm "can_pmatch_all_implies_rows=" source_to_flatProofTheory.can_pmatch_all_IMP_pmatch_rows;
