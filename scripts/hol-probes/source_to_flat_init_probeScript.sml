load "preamble"; load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val do_app_typed = ``∀genv s1 s2 op vs r (s1_i1 : ('a, 'b) flatSem$state) vs_i1.
  semanticPrimitives$do_app s1 op vs = SOME (s2, r) /\
  LIST_REL (source_to_flatProof$sv_rel genv) (FST s1) (TL s1_i1.refs) /\
  ~NULL s1_i1.refs /\ LIST_REL (source_to_flatProof$v_rel genv) vs vs_i1 /\
  SND s1 = s1_i1.ffi /\ source_to_flatProof$genv_c_ok genv.c /\
  op <> AallocEmpty /\ op <> Env_id ==>
  ∃r_i1 s2_i1.
    LIST_REL (source_to_flatProof$sv_rel genv) (FST s2) (TL s2_i1.refs) /\
    ~NULL s2_i1.refs /\ SND s2 = s2_i1.ffi /\
    s1_i1.globals = s2_i1.globals /\ TAKE 1 s1_i1.refs = TAKE 1 s2_i1.refs /\
    source_to_flatProof$result_rel source_to_flatProof$v_rel genv r r_i1 /\
    flatSem$do_app s1_i1 (source_to_flat$astOp_to_flatOp op) vs_i1 = SOME (s2_i1, r_i1)``;
val _ = (print "do_app_typed="; print_term do_app_typed; print "\n");
val do_app_rec_help_typed = ``!genv comp_map env_v_local env_v_local' env_v_top funs t.
  source_to_flatProof$env_rel genv env_v_local env_v_local'.v /\
  source_to_flatProof$global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env' /\
  LENGTH ts = LENGTH funs' + LENGTH env_v_local'.v ==>
  source_to_flatProof$env_rel genv
    (namespace$alist_to_ns
      (MAP (\(f,n,e). (f,semanticPrimitives$Recclosure
        (env' with v := namespace$nsAppend env_v_local env'.v) funs' f)) funs))
    (MAP (\(fn,n,e). (fn,flatSem$Recclosure env_v_local'
      (source_to_flat$compile_funs t
        (comp_map with v := FOLDR (\(x,v) e. namespace$nsBind x v e) comp_map.v
          (MAP2 (\t x. (x,source_to_flat$Local t x)) ts
            (MAP FST funs' ++ MAP FST env_v_local'.v))) funs') fn))
      (source_to_flat$compile_funs t
        (comp_map with v := FOLDR (\(x,v) e. namespace$nsBind x v e) comp_map.v
          (MAP2 (\t x. (x,source_to_flat$Local t x)) ts
            (MAP FST funs' ++ MAP FST env_v_local'.v))) funs))``;
val _ = (print "do_app_rec_help_typed="; print_term do_app_rec_help_typed; print "\n");
val do_app_rec_v_rel_eqns = CONJUNCT1 source_to_flatProofTheory.v_rel_more_eqns;
val (do_app_binders, do_app_body) = strip_forall do_app_typed;
val do_app_arith_inl = Q.prove (
  `EVERY (semanticPrimitives$check_type ty) vs /\ source_to_flatProof$genv_c_ok genv.c /\
    LIST_REL (source_to_flatProof$v_rel genv) vs vs_i1 /\
    semanticPrimitives$do_arith a ty vs = SOME (INL exn) ==>
    exn = semanticPrimitives$div_exn_v /\
    EVERY (semanticPrimitives$check_type ty) (MAP flatSem$flat_to_v vs_i1) /\
    ?e. semanticPrimitives$do_arith a ty (MAP flatSem$flat_to_v vs_i1) = SOME (INL e)`,
  strip_tac >> drule_all source_to_flatProofTheory.check_type_v_rel_MAP_flat_to_v >>
  strip_tac >> fs [] >>
  gvs [oneline semanticPrimitivesTheory.do_arith_def, AllCaseEqs()]);
val do_app_arith_inr = Q.prove (
  `EVERY (semanticPrimitives$check_type ty) vs /\ source_to_flatProof$genv_c_ok genv.c /\
    LIST_REL (source_to_flatProof$v_rel genv) vs vs_i1 /\
    semanticPrimitives$do_arith a ty vs = SOME (INR r) ==>
    EVERY (semanticPrimitives$check_type ty) (MAP flatSem$flat_to_v vs_i1) /\
    ?r'. semanticPrimitives$do_arith a ty (MAP flatSem$flat_to_v vs_i1) = SOME (INR r') /\
      source_to_flatProof$v_rel genv r (flatSem$v_to_flat r')`,
  strip_tac >> drule_all source_to_flatProofTheory.check_type_v_rel_MAP_flat_to_v >>
  strip_tac >> fs [] >> drule_all semanticPrimitivesPropsTheory.do_arith_check_type >>
  rpt strip_tac >> drule_all source_to_flatProofTheory.check_type_IMP_v_rel >> simp []);
val arith_op = ``ast$Arith a ty``;
val do_app_arith_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.rev (free_vars arith_op) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> arith_op] do_app_body);
val do_app_arith_replay = prove (do_app_arith_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  gvs [oneline semanticPrimitivesTheory.do_app_def, AllCaseEqs()] >>
  gvs [oneline flatSemTheory.do_app_def, AllCaseEqs()] >>
  reverse (rw []) >> fs [] >> simp [source_to_flatProofTheory.result_rel_cases, PULL_EXISTS]
  >- (drule_all do_app_arith_inr >> strip_tac >> simp []) >>
  drule_all do_app_arith_inl >> strip_tac >> gvs [] >> EVAL_TAC >>
  simp [Once source_to_flatProofTheory.v_rel_cases] >>
  gvs [source_to_flatProofTheory.genv_c_ok_def, source_to_flatProofTheory.has_exns_def,
       EVAL ``backend_common$div_tag``] >> EVAL_TAC);
val _ = show_thm "do_app_arith_replay=" do_app_arith_replay;
val do_app_equality_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Equality``] do_app_body);
val do_app_v_rel_lems = Q.prove (
  `!genv. source_to_flatProof$genv_c_ok genv.c ==>
    (!b. source_to_flatProof$v_rel genv (semanticPrimitives$Boolv b) (flatSem$Boolv b)) /\
    source_to_flatProof$v_rel genv semanticPrimitives$div_exn_v flatSem$div_exn_v /\
    source_to_flatProof$v_rel genv semanticPrimitives$chr_exn_v flatSem$chr_exn_v /\
    source_to_flatProof$v_rel genv semanticPrimitives$bind_exn_v flatSem$bind_exn_v /\
    source_to_flatProof$v_rel genv semanticPrimitives$sub_exn_v flatSem$subscript_exn_v`,
  rw [semanticPrimitivesTheory.div_exn_v_def, flatSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, flatSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, flatSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, flatSemTheory.subscript_exn_v_def,
      do_app_rec_v_rel_eqns, source_to_flatProofTheory.genv_c_ok_def,
      source_to_flatProofTheory.has_exns_def, source_to_flatProofTheory.has_bools_def,
      semanticPrimitivesTheory.Boolv_def, flatSemTheory.Boolv_def] >>
  every_case_tac >> simp [do_app_rec_v_rel_eqns]);
val do_app_conversion_inl = Q.prove (
  `semanticPrimitives$check_type ty1 v /\ source_to_flatProof$genv_c_ok genv.c /\
    source_to_flatProof$v_rel genv v v_i1 /\
    semanticPrimitives$do_conversion v ty1 ty2 = SOME (INL exn) ==>
    exn = semanticPrimitives$chr_exn_v /\
    semanticPrimitives$check_type ty1 (flatSem$flat_to_v v_i1) /\
    ?e. semanticPrimitives$do_conversion (flatSem$flat_to_v v_i1) ty1 ty2 = SOME (INL e)`,
  strip_tac >> drule_all source_to_flatProofTheory.check_type_v_rel_flat_to_v >>
  strip_tac >> fs [] >> gvs [oneline semanticPrimitivesTheory.do_conversion_def, AllCaseEqs()]);
val do_app_conversion_inr = Q.prove (
  `semanticPrimitives$check_type ty1 v /\ source_to_flatProof$genv_c_ok genv.c /\
    source_to_flatProof$v_rel genv v v_i1 /\
    semanticPrimitives$do_conversion v ty1 ty2 = SOME (INR r) ==>
    semanticPrimitives$check_type ty1 (flatSem$flat_to_v v_i1) /\
    ?r'. semanticPrimitives$do_conversion (flatSem$flat_to_v v_i1) ty1 ty2 = SOME (INR r') /\
      source_to_flatProof$v_rel genv r (flatSem$v_to_flat r')`,
  strip_tac >> drule_all source_to_flatProofTheory.check_type_v_rel_flat_to_v >>
  strip_tac >> fs [] >> drule_all semanticPrimitivesPropsTheory.do_conversion_check_type >>
  rpt strip_tac >> drule_all source_to_flatProofTheory.check_type_IMP_v_rel >> simp []);
val from_to_op = ``ast$FromTo ty1 ty2``;
val do_app_fromto_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.rev (free_vars from_to_op) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> from_to_op] do_app_body);
val do_app_fromto_replay = prove (do_app_fromto_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  gvs [oneline semanticPrimitivesTheory.do_app_def, AllCaseEqs()] >>
  gvs [oneline flatSemTheory.do_app_def, AllCaseEqs()] >>
  reverse (rw []) >> fs [] >> simp [source_to_flatProofTheory.result_rel_cases, PULL_EXISTS]
  >- (drule_all do_app_conversion_inr >> strip_tac >> simp []) >>
  drule_all do_app_conversion_inl >> strip_tac >> gvs [] >>
  imp_res_tac do_app_v_rel_lems >> gvs []);
val _ = show_thm "do_app_fromto_replay=" do_app_fromto_replay;
val do_app_eq_rel = Q.prove (
  `!genv. source_to_flatProof$genv_c_ok genv.c ==>
    (!v1 v2 r v1_i1 v2_i1.
      semanticPrimitives$do_eq v1 v2 = r /\ source_to_flatProof$v_rel genv v1 v1_i1 /\
      source_to_flatProof$v_rel genv v2 v2_i1 ==> flatSem$do_eq v1_i1 v2_i1 = r) /\
    (!vs1 vs2 r vs1_i1 vs2_i1.
      semanticPrimitives$do_eq_list vs1 vs2 = r /\ LIST_REL (source_to_flatProof$v_rel genv) vs1 vs1_i1 /\
      LIST_REL (source_to_flatProof$v_rel genv) vs2 vs2_i1 ==> flatSem$do_eq_list vs1_i1 vs2_i1 = r)`,
  ntac 2 strip_tac >> ho_match_mp_tac semanticPrimitivesTheory.do_eq_ind >> rpt strip_tac >>
  fs [flatSemTheory.Boolv_def, semanticPrimitivesTheory.do_eq_def, flatSemTheory.do_eq_def,
      source_to_flatProofTheory.v_rel_more_eqns] >>
  rveq >> fs [] >> rpt (irule COND_CONG >> rpt strip_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  fs [flatSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  TRY every_case_tac >> gs [semanticPrimitivesTheory.lit_same_type_def] >>
  metis_tac [SOME_11, source_to_flatProofTheory.genv_c_ok_def
    |> SIMP_RULE (srw_ss()) [semanticPrimitivesTheory.ctor_same_type_def]]);
val do_app_equality_replay = prove (do_app_equality_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac [source_to_flatProofTheory.Boolv_11, do_app_eq_rel,
    semanticPrimitivesTheory.eq_result_11, semanticPrimitivesTheory.eq_result_distinct, do_app_v_rel_lems]);
val _ = show_thm "do_app_equality_replay=" do_app_equality_replay;
val do_app_test_lemma = Q.prove (
  `semanticPrimitives$do_test test ty v1 v2 = Eq_val b /\
    source_to_flatProof$genv_c_ok genv.c /\
    source_to_flatProof$v_rel genv v1 w1 /\ source_to_flatProof$v_rel genv v2 w2 ==>
    flatSem$do_test test ty w1 w2 = Eq_val b`,
  strip_tac >>
  gvs [oneline semanticPrimitivesTheory.do_test_def, AllCaseEqs()] >>
  gvs [oneline flatSemTheory.do_test_def, AllCaseEqs()]
  >- (gvs [semanticPrimitivesTheory.check_type_def] >>
      fs [Once source_to_flatProofTheory.v_rel_cases] >> gvs [] >>
      fs [flatSemTheory.the_Litv_Float64_def] >>
      fs [semanticPrimitivesTheory.the_Litv_Float64_def] >> gvs [flatSemTheory.check_type_def])
  >- (drule_all (cj 1 do_app_eq_rel) >> simp [] >>
      imp_res_tac source_to_flatProofTheory.v_rel_check_type >> fs [])
  >- (gvs [oneline semanticPrimitivesTheory.dest_Litv_def, AllCaseEqs()] >>
      gvs [oneline flatSemTheory.dest_Litv_def, AllCaseEqs()] >> gvs [do_app_rec_v_rel_eqns]) >>
  gvs [oneline semanticPrimitivesTheory.dest_Litv_def, AllCaseEqs()] >>
  fs [Once source_to_flatProofTheory.v_rel_cases] >> gvs [flatSemTheory.dest_Litv_def]);
val test_op = ``ast$Test test ty``;
val do_app_test_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.rev (free_vars test_op) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> test_op] do_app_body);
val do_app_test_replay = prove (do_app_test_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  gvs [oneline semanticPrimitivesTheory.do_app_def, AllCaseEqs()] >>
  gvs [oneline flatSemTheory.do_app_def, AllCaseEqs()] >>
  rw [PULL_EXISTS] >> gvs [] >> drule_all do_app_test_lemma >> fs [] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems]);
val _ = show_thm "do_app_test_replay=" do_app_test_replay;
val do_app_opapp_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Opapp``] do_app_body);
val do_app_opapp_replay = prove (do_app_opapp_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems]);
val _ = show_thm "do_app_opapp_replay=" do_app_opapp_replay;
val do_app_opassign_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Opassign``] do_app_body);
val do_app_opassign_replay = prove (do_app_opassign_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_assign_def,
    semanticPrimitivesTheory.store_v_same_type_def, flatSemTheory.Unitv_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[GSYM ADD1, LUPDATE_def]
  >- metis_tac [EVERY2_LUPDATE_same, source_to_flatProofTheory.sv_rel_rules] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[]);
val _ = show_thm "do_app_opassign_replay=" do_app_opassign_replay;
val do_app_opref_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Opref``] do_app_body);
val do_app_opref_replay = prove (do_app_opref_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_alloc_def] >>
  srw_tac[][source_to_flatProofTheory.sv_rel_cases] >>
  full_simp_tac(srw_ss())[ADD1] >> metis_tac [LIST_REL_LENGTH]);
val _ = show_thm "do_app_opref_replay=" do_app_opref_replay;
val do_app_opderef_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Opderef``] do_app_body);
val do_app_opderef_replay = prove (do_app_opderef_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, ADD1] >>
  full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases, REWRITE_RULE [ADD1] EL] >>
  res_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][]);
val _ = show_thm "do_app_opderef_replay=" do_app_opderef_replay;
val do_app_aw8alloc_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8alloc``] do_app_body);
val do_app_aw8alloc_replay = prove (do_app_aw8alloc_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_alloc_def] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, ADD1, REWRITE_RULE [ADD1] EL] >>
  srw_tac[][source_to_flatProofTheory.sv_rel_cases, PULL_EXISTS, ADD1] >>
  metis_tac [LIST_REL_LENGTH, do_app_v_rel_lems]);
val _ = show_thm "do_app_aw8alloc_replay=" do_app_aw8alloc_replay;
val do_app_aw8sub_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8sub``] do_app_body);
val do_app_aw8sub_replay = prove (do_app_aw8sub_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def] >>
  full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL] >>
  imp_res_tac LIST_REL_LENGTH >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  srw_tac[][markerTheory.Abbrev_def, do_app_v_rel_lems]);
val _ = show_thm "do_app_aw8sub_replay=" do_app_aw8sub_replay;
val do_app_aw8length_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8length``] do_app_body);
val do_app_aw8length_replay = prove (do_app_aw8length_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def] >>
  full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL] >>
  imp_res_tac LIST_REL_LENGTH >> srw_tac[][] >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  srw_tac[][markerTheory.Abbrev_def]);
val _ = show_thm "do_app_aw8length_replay=" do_app_aw8length_replay;
val do_app_aw8update_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8update``] do_app_body);
val do_app_aw8update_replay = prove (do_app_aw8update_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, semanticPrimitivesTheory.store_assign_def, semanticPrimitivesTheory.store_v_same_type_def] >>
  full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL, REWRITE_RULE [ADD1] LUPDATE_def] >>
  imp_res_tac LIST_REL_LENGTH >> srw_tac[][flatSemTheory.Unitv_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> srw_tac[][] >> fsrw_tac[][] >>
  srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >> srw_tac[][do_app_v_rel_lems]);
val _ = show_thm "do_app_aw8update_replay=" do_app_aw8update_replay;
val do_app_copystrstr_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$CopyStrStr``] do_app_body);
val do_app_copystrstr_replay = prove (do_app_copystrstr_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [do_app_rec_v_rel_eqns, stringTheory.IMPLODE_EXPLODE_I, source_to_flatProofTheory.result_rel_cases] >>
  simp [do_app_v_rel_lems, do_app_rec_v_rel_eqns]);
val _ = show_thm "do_app_copystrstr_replay=" do_app_copystrstr_replay;
val do_app_copystraw8_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$CopyStrAw8``] do_app_body);
val do_app_copystraw8_replay = prove (do_app_copystraw8_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [do_app_rec_v_rel_eqns, stringTheory.IMPLODE_EXPLODE_I, source_to_flatProofTheory.result_rel_cases,
      PULL_EXISTS, semanticPrimitivesTheory.store_lookup_def, EXISTS_PROD,
      semanticPrimitivesTheory.store_assign_def, flatSemTheory.Unitv_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >>
  imp_res_tac LIST_REL_LENGTH >> rw [] >> imp_res_tac LIST_REL_EL_EQN >>
  rfs [source_to_flatProofTheory.sv_rel_cases, do_app_v_rel_lems, do_app_rec_v_rel_eqns, ADD1] >>
  simp [semanticPrimitivesTheory.store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def] >>
  match_mp_tac EVERY2_LUPDATE_same >> simp [source_to_flatProofTheory.sv_rel_cases]);
val _ = show_thm "do_app_copystraw8_replay=" do_app_copystraw8_replay;
val do_app_copyaw8str_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$CopyAw8Str``] do_app_body);
val do_app_copyaw8str_replay = prove (do_app_copyaw8str_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [do_app_rec_v_rel_eqns, stringTheory.IMPLODE_EXPLODE_I, source_to_flatProofTheory.result_rel_cases,
      PULL_EXISTS, semanticPrimitivesTheory.store_lookup_def, EXISTS_PROD,
      semanticPrimitivesTheory.store_assign_def, flatSemTheory.Unitv_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >>
  imp_res_tac LIST_REL_LENGTH >> rw [] >> imp_res_tac LIST_REL_EL_EQN >>
  rfs [source_to_flatProofTheory.sv_rel_cases, do_app_v_rel_lems, do_app_rec_v_rel_eqns]);
val _ = show_thm "do_app_copyaw8str_replay=" do_app_copyaw8str_replay;
val do_app_copyaw8aw8_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$CopyAw8Aw8``] do_app_body);
val do_app_copyaw8aw8_replay = prove (do_app_copyaw8aw8_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [do_app_rec_v_rel_eqns, stringTheory.IMPLODE_EXPLODE_I, source_to_flatProofTheory.result_rel_cases,
      PULL_EXISTS, semanticPrimitivesTheory.store_lookup_def, EXISTS_PROD,
      semanticPrimitivesTheory.store_assign_def, flatSemTheory.Unitv_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >>
  imp_res_tac LIST_REL_LENGTH >> rw [] >> TRY (asm_exists_tac >> simp []) >>
  imp_res_tac LIST_REL_EL_EQN >>
  rfs [source_to_flatProofTheory.sv_rel_cases, do_app_v_rel_lems, do_app_rec_v_rel_eqns] >>
  simp [semanticPrimitivesTheory.store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def] >>
  match_mp_tac EVERY2_LUPDATE_same >> simp [source_to_flatProofTheory.sv_rel_cases]);
val _ = show_thm "do_app_copyaw8aw8_replay=" do_app_copyaw8aw8_replay;
val do_app_xoraw8str_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$XorAw8Str_unsafe``] do_app_body);
val do_app_xoraw8str_replay = prove (do_app_xoraw8str_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [do_app_rec_v_rel_eqns, stringTheory.IMPLODE_EXPLODE_I, source_to_flatProofTheory.result_rel_cases,
      PULL_EXISTS, semanticPrimitivesTheory.store_lookup_def, EXISTS_PROD,
      semanticPrimitivesTheory.store_assign_def, flatSemTheory.Unitv_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >>
  imp_res_tac LIST_REL_LENGTH >> rw [] >> TRY (asm_exists_tac >> simp []) >>
  imp_res_tac LIST_REL_EL_EQN >>
  rfs [source_to_flatProofTheory.sv_rel_cases, do_app_v_rel_lems, do_app_rec_v_rel_eqns] >>
  simp [semanticPrimitivesTheory.store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def] >>
  match_mp_tac EVERY2_LUPDATE_same >> simp [source_to_flatProofTheory.sv_rel_cases]);
val _ = show_thm "do_app_xoraw8str_replay=" do_app_xoraw8str_replay;
val do_app_v_to_char_list = prove (
  ``!genv. source_to_flatProof$genv_c_ok genv.c ⇒ !v1 v2 vs1.
    source_to_flatProof$v_rel genv v1 v2 ∧ semanticPrimitives$v_to_char_list v1 = SOME vs1 ⇒
    flatSem$v_to_char_list v2 = SOME vs1``,
  ntac 2 strip_tac >> ho_match_mp_tac semanticPrimitivesTheory.v_to_char_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_char_list_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[source_to_flatProofTheory.v_rel_more_eqns, flatSemTheory.v_to_char_list_def] >>
  imp_res_tac source_to_flatProofTheory.genv_lookup_nil >>
  imp_res_tac source_to_flatProofTheory.genv_lookup_cons >>
  fs [] >> rw [flatSemTheory.v_to_char_list_def]);
val do_app_implode_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Implode``] do_app_body);
val do_app_implode_replay = prove (do_app_implode_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  imp_res_tac do_app_v_to_char_list >> srw_tac[][]);
val _ = show_thm "do_app_implode_replay=" do_app_implode_replay;
val do_app_explode_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Explode``] do_app_body);
val do_app_explode_replay = prove (do_app_explode_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  imp_res_tac do_app_v_to_char_list >> srw_tac[][] >>
  Cases_on `str` >> fs [] >> Induct_on `s` >>
  fs [semanticPrimitivesTheory.list_to_v_def, flatSemTheory.list_to_v_def] >>
  simp [Once source_to_flatProofTheory.v_rel_cases] >>
  fs [source_to_flatProofTheory.genv_c_ok_def, source_to_flatProofTheory.has_lists_def] >>
  simp [Once source_to_flatProofTheory.v_rel_cases]);
val _ = show_thm "do_app_explode_replay=" do_app_explode_replay;
val do_app_strsub_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Strsub``] do_app_body);
val do_app_strsub_replay = prove (do_app_strsub_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_rec_v_rel_eqns] >>
  srw_tac[][markerTheory.Abbrev_def] >> srw_tac[][markerTheory.Abbrev_def] >>
  full_simp_tac(srw_ss())[do_app_v_rel_lems] >>
  rename1 `explode str` >> Cases_on `str` >> fs []);
val _ = show_thm "do_app_strsub_replay=" do_app_strsub_replay;
val do_app_strlen_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Strlen``] do_app_body);
val do_app_strlen_replay = prove (do_app_strlen_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems]);
val _ = show_thm "do_app_strlen_replay=" do_app_strlen_replay;
val do_app_v_to_list = let open source_to_flatProofTheory in prove (
  ``!genv. genv_c_ok genv.c ⇒ !v1 v2 vs1.
    v_rel genv v1 v2 ∧ semanticPrimitives$v_to_list v1 = SOME vs1 ⇒
    ?vs2. flatSem$v_to_list v2 = SOME vs2 ∧ LIST_REL (v_rel genv) vs1 vs2``,
  ntac 2 strip_tac >> ho_match_mp_tac semanticPrimitivesTheory.v_to_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_list_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][] >> imp_res_tac genv_lookup_nil >> imp_res_tac genv_lookup_cons >>
  fs [] >> rw [flatSemTheory.v_to_list_def] >> res_tac >> fs []) end;
val do_app_vs_to_string = let open source_to_flatProofTheory in prove (
  ``∀v1 v2 s. LIST_REL (v_rel genv) v1 v2 ⇒
      semanticPrimitives$vs_to_string v1 = SOME s ⇒ flatSem$vs_to_string v2 = SOME s``,
  ho_match_mp_tac semanticPrimitivesTheory.vs_to_string_ind >>
  rw [semanticPrimitivesTheory.vs_to_string_def, flatSemTheory.vs_to_string_def] >>
  fs [do_app_rec_v_rel_eqns] >> pop_assum mp_tac >> TOP_CASE_TAC >> strip_tac >> rveq >> fs [] >>
  rw [flatSemTheory.vs_to_string_def]) end;
val do_app_strcat_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Strcat``] do_app_body);
val do_app_strcat_replay = prove (do_app_strcat_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  rw [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  fs [LIST_REL_def] >> imp_res_tac do_app_v_to_list >> fs [] >>
  imp_res_tac do_app_vs_to_string >> fs [source_to_flatProofTheory.result_rel_cases, do_app_rec_v_rel_eqns]);
val _ = show_thm "do_app_strcat_replay=" do_app_strcat_replay;
val do_app_vfromlist_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$VfromList``] do_app_body);
val do_app_vfromlist_replay = prove (do_app_vfromlist_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_rec_v_rel_eqns] >>
  imp_res_tac do_app_v_to_list >> srw_tac[][]);
val _ = show_thm "do_app_vfromlist_replay=" do_app_vfromlist_replay;
val do_app_vsub_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Vsub``] do_app_body);
val do_app_vsub_replay = prove (do_app_vsub_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  srw_tac[][markerTheory.Abbrev_def] >> srw_tac[][markerTheory.Abbrev_def] >>
  full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, do_app_v_rel_lems]);
val _ = show_thm "do_app_vsub_replay=" do_app_vsub_replay;
val do_app_vsubunsafe_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Vsub_unsafe``] do_app_body);
val do_app_vsubunsafe_replay = prove (do_app_vsubunsafe_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  srw_tac[][markerTheory.Abbrev_def] >> srw_tac[][markerTheory.Abbrev_def] >>
  full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, do_app_v_rel_lems]);
val _ = show_thm "do_app_vsubunsafe_replay=" do_app_vsubunsafe_replay;
val do_app_vlength_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Vlength``] do_app_body);
val do_app_vlength_replay = prove (do_app_vlength_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  srw_tac[][] >> metis_tac [LIST_REL_LENGTH]);
val _ = show_thm "do_app_vlength_replay=" do_app_vlength_replay;
val do_app_aalloc_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aalloc``] do_app_body);
val do_app_aalloc_replay = prove (do_app_aalloc_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_alloc_def] >>
  srw_tac[][source_to_flatProofTheory.sv_rel_cases, LIST_REL_REPLICATE_same, ADD1] >>
  metis_tac [LIST_REL_LENGTH, do_app_v_rel_lems]);
val _ = show_thm "do_app_aalloc_replay=" do_app_aalloc_replay;
val do_app_aallocfixed_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$AallocFixed``] do_app_body);
val do_app_aallocfixed_replay = prove (do_app_aallocfixed_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_alloc_def] >>
  srw_tac[][source_to_flatProofTheory.sv_rel_cases, LIST_REL_REPLICATE_same, ADD1] >>
  metis_tac [LIST_REL_LENGTH, do_app_v_rel_lems]);
val _ = show_thm "do_app_aallocfixed_replay=" do_app_aallocfixed_replay;
val do_app_asub_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Asub``] do_app_body);
val do_app_asub_replay = prove (do_app_asub_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN, do_app_v_rel_lems] >>
  decide_tac);
val _ = show_thm "do_app_asub_replay=" do_app_asub_replay;
val do_app_asubunsafe_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Asub_unsafe``] do_app_body);
val do_app_asubunsafe_replay = prove (do_app_asubunsafe_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN, do_app_v_rel_lems] >>
  decide_tac);
val _ = show_thm "do_app_asubunsafe_replay=" do_app_asubunsafe_replay;
val do_app_alength_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Alength``] do_app_body);
val do_app_alength_replay = prove (do_app_alength_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, source_to_flatProofTheory.sv_rel_cases] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1] >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> res_tac >>
  full_simp_tac(srw_ss())[source_to_flatProofTheory.sv_rel_cases] >>
  metis_tac [semanticPrimitivesTheory.store_v_distinct, semanticPrimitivesTheory.store_v_11, LIST_REL_LENGTH]);
val _ = show_thm "do_app_alength_replay=" do_app_alength_replay;
val do_app_aupdate_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aupdate``] do_app_body);
val do_app_aupdate_replay = prove (do_app_aupdate_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, semanticPrimitivesTheory.store_assign_def,
    semanticPrimitivesTheory.store_v_same_type_def, flatSemTheory.Unitv_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN, do_app_v_rel_lems] >>
  srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >> srw_tac[][] >> decide_tac);
val _ = show_thm "do_app_aupdate_replay=" do_app_aupdate_replay;
val do_app_aupdateunsafe_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aupdate_unsafe``] do_app_body);
val do_app_aupdateunsafe_replay = prove (do_app_aupdateunsafe_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, semanticPrimitivesTheory.store_assign_def,
    semanticPrimitivesTheory.store_v_same_type_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
  drule_then drule source_to_flatProofTheory.LIST_REL_IMP_EL2 >> disch_tac >> every_case_tac >>
  full_simp_tac(srw_ss())[source_to_flatProofTheory.sv_rel_cases] >> imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[flatSemTheory.Unitv_def] >>
  DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >>
  full_simp_tac(srw_ss())[flatSemTheory.Unitv_def, source_to_flatProofTheory.sv_rel_cases] >>
  DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >> gvs [] >> decide_tac);
val _ = show_thm "do_app_aupdateunsafe_replay=" do_app_aupdateunsafe_replay;
val do_app_aw8subunsafe_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8sub_unsafe``] do_app_body);
val do_app_aw8subunsafe_replay = prove (do_app_aw8subunsafe_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
  imp_res_tac LIST_REL_LENGTH >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> rfs[] >>
  srw_tac[][markerTheory.Abbrev_def, do_app_v_rel_lems]);
val _ = show_thm "do_app_aw8subunsafe_replay=" do_app_aw8subunsafe_replay;
val do_app_aw8updateunsafe_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$Aw8update_unsafe``] do_app_body);
val do_app_aw8updateunsafe_replay = prove (do_app_aw8updateunsafe_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases, do_app_v_rel_lems] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_lookup_def, semanticPrimitivesTheory.store_assign_def,
    semanticPrimitivesTheory.store_v_same_type_def] >>
  fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
  imp_res_tac LIST_REL_LENGTH >> srw_tac[][] >> every_case_tac >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, flatSemTheory.Unitv_def, source_to_flatProofTheory.sv_rel_cases] >>
  res_tac >> srw_tac[][] >> fsrw_tac[][] >>
  srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
  srw_tac[][do_app_v_rel_lems] >> CCONTR_TAC >> rfs [] >> rveq >> fs []);
val _ = show_thm "do_app_aw8updateunsafe_replay=" do_app_aw8updateunsafe_replay;
val shift_op = ``ast$Shift w sh n``;
val do_app_shift_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.rev (free_vars shift_op) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> shift_op] do_app_body);
val do_app_shift_replay = prove (do_app_shift_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def, astTheory.getOpClass_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns] >>
  fs [flatSemTheory.do_app_def] >>
  TRY (rename1 `shift8_lookup s11 w11 n11`) >>
  TRY (rename1 `shift64_lookup s11 w11 n11`) >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns] >>
  Cases_on `w11` >> Cases_on `s11` >>
  fs [semanticPrimitivesTheory.shift8_lookup_def, semanticPrimitivesTheory.shift64_lookup_def,
      source_to_flatProofTheory.result_rel_cases, Once do_app_rec_v_rel_eqns]);
val _ = show_thm "do_app_shift_replay=" do_app_shift_replay;
val do_app_configGC_typed = list_mk_forall
  (List.take (do_app_binders, 3) @ List.drop (do_app_binders, 4),
   subst [List.nth (do_app_binders, 3) |-> ``ast$ConfigGC``] do_app_body);
val do_app_configGC_replay = prove (do_app_configGC_typed,
  rpt gen_tac >> Cases_on `s1` >> Cases_on `s1_i1.refs` >> simp [] >> Cases_on `s1_i1` >>
  simp [source_to_flatTheory.astOp_to_flatOp_def] >>
  srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[do_app_rec_v_rel_eqns, source_to_flatProofTheory.result_rel_cases,
    flatSemTheory.Unitv_def]);
val _ = show_thm "do_app_configGC_replay=" do_app_configGC_replay;
val do_app_rec_help_replay = prove (do_app_rec_help_typed,
  Induct_on `funs`
  >- srw_tac[][do_app_rec_v_rel_eqns, source_to_flatTheory.compile_exp_def] >>
  rw [] >> PairCases_on `h` >> fs [source_to_flatTheory.compile_exp_def] >>
  simp [do_app_rec_v_rel_eqns] >>
  simp [Once source_to_flatProofTheory.v_rel_cases] >>
  MAP_EVERY qexists_tac [`comp_map`, `env'`, `env_v_local`, `t`, `ts`] >>
  simp [source_to_flatTheory.compile_exp_def, source_to_flatProofTheory.bind_locals_def] >>
  simp_tac (std_ss) [GSYM APPEND, namespaceTheory.nsBindList_def]);
val _ = show_thm "do_app_rec_help_replay=" do_app_rec_help_replay;
val global_env_inv_add_locals_replay = Q.prove (
  `!genv comp_map locals1 locals2 env.
    source_to_flatProof$global_env_inv genv comp_map locals1 env ==>
    source_to_flatProof$global_env_inv genv comp_map (locals2 UNION locals1) env`,
  srw_tac[][source_to_flatProofTheory.v_rel_global_eqn] >> metis_tac []);
val _ = show_thm "global_env_inv_add_locals_replay=" global_env_inv_add_locals_replay;
(* The theorem is local to the original proof; preserve its inferred types. *)
val global_env_inv_extend2_typed = ``!genv comp_map env new_vars env' locals env_c.
  set (MAP (Short o FST) new_vars) = namespace$nsDom env' /\
  source_to_flatProof$global_env_inv genv comp_map locals env /\
  source_to_flatProof$global_env_inv genv
    (comp_map with v := namespace$alist_to_ns new_vars) locals <|v := env'; c := env_c|> ==>
  source_to_flatProof$global_env_inv genv
    (comp_map with v := namespace$nsBindList new_vars comp_map.v) locals
    (env with v := namespace$nsAppend env' env.v)``;
val _ = (print "global_env_inv_extend2_typed="; print_term global_env_inv_extend2_typed; print "\n");
val global_env_inv_extend2_replay = prove (global_env_inv_extend2_typed,
  rw [source_to_flatProofTheory.v_rel_global_eqn, GSYM namespacePropsTheory.nsAppend_to_nsBindList] >>
  fs [namespacePropsTheory.nsLookup_nsAppend_some, namespacePropsTheory.nsLookup_alist_to_ns_none,
      namespacePropsTheory.nsLookup_alist_to_ns_some] >>
  res_tac >> fs [] >> rw [] >> fs [] >> rveq >> fs [] >>
  goal_assum (first_assum o mp_then (Pat `EL _ _ = _`) mp_tac) >>
  simp [] >> Cases_on `x` >> fs [] >> rw []
  >- (`Short n' ∉ namespace$nsDom env'` by
        metis_tac [namespacePropsTheory.nsLookup_nsDom, NOT_SOME_NONE] >>
      qexists_tac `t` >> disj2_tac >> rw [ALOOKUP_NONE] >>
      qpat_x_assum `_ = namespace$nsDom _` (assume_tac o GSYM) >>
      fs [MEM_MAP] >> fs [namespaceTheory.id_to_mods_def])
  >- (fs [namespaceTheory.id_to_mods_def] >> Cases_on `p1` >> fs [] >> rw []));
val _ = show_thm "global_env_inv_extend2_replay=" global_env_inv_extend2_replay;
val lookup_build_rec_env_lem_replay = Q.prove (
  `!x cl_env funs' funs.
    ALOOKUP (MAP (\(fn,n,e). (fn,semanticPrimitives$Recclosure cl_env funs' fn)) funs) x = SOME v ==>
    v = semanticPrimitives$Recclosure cl_env funs' x`,
  Induct_on `funs` >> srw_tac[][] >> PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[]);
val _ = show_thm "lookup_build_rec_env_lem_replay=" lookup_build_rec_env_lem_replay;
val sem_env_eq_lemma_replay = Q.prove (
  `!(env:'a sem_env) x. (env with v := x) = <| v := x; c := env.c |>`,
  rw [] >> rw [semanticPrimitivesTheory.sem_env_component_equality]);
val _ = show_thm "sem_env_eq_lemma_replay=" sem_env_eq_lemma_replay;
val eta2_replay = Q.prove (`!f x. (\y. f x y) = f x`, metis_tac []);
val _ = show_thm "eta2_replay=" eta2_replay;
val ctor_same_type_refl_replay = Q.prove (
  `flatSem$ctor_same_type x x`,
  Cases_on `x` >> rw [flatSemTheory.ctor_same_type_def] >>
  rename [`SOME x`] >> Cases_on `x` >> rw [flatSemTheory.ctor_same_type_def]);
val _ = show_thm "ctor_same_type_refl_replay=" ctor_same_type_refl_replay;
val ctor_same_type_snd_replay = Q.prove (
  `flatSem$ctor_same_type (SOME x) (SOME y) = (SND x = SND y)`,
  Cases_on `x` \\ Cases_on `y` \\ simp [flatSemTheory.ctor_same_type_def]);
val _ = show_thm "ctor_same_type_snd_replay=" ctor_same_type_snd_replay;
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
