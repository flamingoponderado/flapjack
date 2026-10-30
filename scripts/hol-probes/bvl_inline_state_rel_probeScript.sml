(* Typed original tick-removal state relation. *)
load "preamble";
load "bvl_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "state_rel=" bvl_inlineProofTheory.state_rel_def;
val _ = show "evaluate_remove_ticks=" bvl_inlineProofTheory.evaluate_remove_ticks;
val _ = show "remove_ticks_cc=" bvl_inlineProofTheory.remove_ticks_cc_def;
val _ = show "remove_ticks_co=" bvl_inlineProofTheory.remove_ticks_co_def;
val _ = show "evaluate_compile_prog=" bvl_inlineProofTheory.evaluate_compile_prog;
val _ = show "mk_tick=" bvlTheory.mk_tick_def;
val _ = show "mk_tick_zero=" (EVAL ``bvl$mk_tick 0 (bvl$Var 4)``);
val _ = show "mk_tick_three=" (EVAL ``bvl$mk_tick 3 (bvl$Var 4)``);
val _ = show "exp_rel_rules=" bvl_inlineProofTheory.exp_rel_rules;
val _ = show "subspt_exp_rel=" bvl_inlineProofTheory.subspt_exp_rel;
val _ = show "exp_rel_swap=" bvl_inlineProofTheory.exp_rel_swap;
val _ = show "exp_rel_refl=" bvl_inlineProofTheory.exp_rel_refl;
val _ = show "tick_inline=" bvl_inlineTheory.tick_inline_def;
val _ = show "tick_inline_sing_def=" bvl_inlineTheory.tick_inline_sing_def;
val _ = show "tick_inline_sing=" bvl_inlineTheory.tick_inline_sing;
val _ = show "exp_rel_tick_inline=" bvl_inlineProofTheory.exp_rel_tick_inline;
val _ = show "is_small_aux=" bvl_inlineTheory.is_small_aux_def;
val _ = show "is_small_sing_def=" bvl_inlineTheory.is_small_sing_def;
val _ = show "is_small_sing=" bvl_inlineTheory.is_small_sing;
val _ = show "is_small=" bvl_inlineTheory.is_small_def;
val _ = show "is_rec=" bvl_inlineTheory.is_rec_def;
val _ = show "is_rec_sing_def=" bvl_inlineTheory.is_rec_sing_def;
val _ = show "is_rec_sing=" bvl_inlineTheory.is_rec_sing;
val _ = show "must_inline=" bvl_inlineTheory.must_inline_def;
val _ = show "tick_inline_all=" bvl_inlineTheory.tick_inline_all_def;
val _ = show "tick_compile_prog=" bvl_inlineTheory.tick_compile_prog_def;
val _ = show "tick_inline_all_names=" bvl_inlineProofTheory.tick_inline_all_names;
val _ = show "tick_compile_prog_res_range=" bvl_inlineProofTheory.tick_compile_prog_res_range;
val _ = show "in_cc=" bvl_inlineProofTheory.in_cc_def;
val _ = show "in_state_rel=" bvl_inlineProofTheory.in_state_rel_def;
val _ = show "evaluate_inline=" bvl_inlineProofTheory.evaluate_inline;
val _ = show "evaluate_mk_tick=" bvlPropsTheory.evaluate_mk_tick;
val _ = show "evaluate_mono=" bvlPropsTheory.evaluate_mono;
val _ = show "evaluate_expand_env=" bvlPropsTheory.evaluate_expand_env;
val _ = show "in_co=" bvl_inlineProofTheory.in_co_def;
val _ = show "MAP_FST_tick_inline_all=" bvl_inlineProofTheory.MAP_FST_tick_inline_all;
val _ = show "do_app_Rval_swap=" bvlPropsTheory.do_app_Rval_swap;
val _ = show "do_app_Rerr_swap=" bvlPropsTheory.do_app_Rerr_swap;
val _ = show "must_inline_yes=" (EVAL ``bvl_inline$must_inline 3 5 (bvl$Call 0 (SOME 4) [bvl$Var 1])``);
val _ = show "must_inline_rec=" (EVAL ``bvl_inline$must_inline 3 5 (bvl$Call 0 (SOME 3) [bvl$Var 1])``);
val _ = show "must_inline_zero=" (EVAL ``bvl_inline$must_inline 3 0 (bvl$Var 1)``);
val _ = show "tick_inline_generic_cache=" (EVAL ``bvl_inline$tick_inline_sing
  (sptree$insert 3 (T, bvl$Var 8) sptree$LN) (bvl$Call 2 (SOME 3) [bvl$Var 1])``);
val _ = show "tick_inline_uncached=" (EVAL ``bvl_inline$tick_inline_sing
  (sptree$LN : (bool # bvl$exp) sptree$num_map) (bvl$Call 2 (SOME 3) [bvl$Var 1])``);
val do_app_lemma_goal = ``
  bvl_inlineProof$state_rel t' r ==>
    case bvlSem$do_app op (REVERSE a) r of
    | semanticPrimitives$Rerr err => bvlSem$do_app op (REVERSE a) t' = semanticPrimitives$Rerr err
    | semanticPrimitives$Rval (v,r2) => ?t2. bvl_inlineProof$state_rel t2 r2 /\
        bvlSem$do_app op (REVERSE a) t' = semanticPrimitives$Rval (v,t2)``;
val _ = (print "do_app_lemma_typed_goal="; print_term do_app_lemma_goal; print "\n");
open bvlSemTheory bvlPropsTheory bvl_inlineTheory bvl_inlineProofTheory;
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "fromAList_def"];
val tick_inline_all_acc = prove(
  ``!limit cs t aux.
      tick_inline_all limit cs t aux =
        let (cs1,xs) = tick_inline_all limit cs t [] in
          (cs1, REVERSE aux ++ xs)``,
  Induct_on `t` \\ fs [tick_inline_all_def] \\ rpt strip_tac
  \\ PairCases_on `h` \\ simp_tac std_ss  [tick_inline_all_def]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [] \\ pairarg_tac \\ fs []);


val exp_rel_rw = prove(
  ``exp_rel (union (union src_code (insert p1 (p2,p3) LN)) (fromAList in1))
      [exp] [exp2] <=>
    exp_rel (union src_code (fromAList ((p1,p2,p3)::in1))) [exp] [exp2]``,
  match_mp_tac exp_rel_swap
  \\ fs [lookup_union,lookup_insert,fromAList_def,case_eq_thms,lookup_def]
  \\ Cases_on `lookup k src_code` \\ fs []
  \\ CCONTR_TAC \\ fs []);

val local_program_relation_goal = ``
  !limit cs0 in1 cs1 in2 k arity exp src_code.
      tick_compile_prog limit cs0 in1 = (cs1,in2) /\
      ALOOKUP in1 k = SOME (arity,exp) /\
      ALL_DISTINCT (MAP FST in1) /\
      (!k arity v.
         lookup k cs0 = SOME (arity,v) ==>
         ?exp. lookup k src_code = SOME (arity,exp) /\
               exp_rel src_code [exp] [v]) /\
      DISJOINT (domain src_code) (set (MAP FST in1)) /\
      DISJOINT (domain cs0) (set (MAP FST in1)) ==>
      ∃exp2.
        ALOOKUP in2 k = SOME (arity,exp2) /\
        exp_rel (union src_code (fromAList in1)) [exp] [exp2]``;
val _ = (print "tick_compile_prog_IMP_exp_rel_typed_goal="; print_term local_program_relation_goal; print "\n");
val local_program_relation_replay = prove (local_program_relation_goal,
  Induct_on `in1`
  \\ fs [FORALL_PROD,tick_compile_prog_def,tick_inline_all_def]
  \\ once_rewrite_tac [tick_inline_all_acc]
  \\ fs [] \\ rpt gen_tac
  \\ pairarg_tac \\ fs [] \\ strip_tac \\ rveq
  \\ fs [] \\ rw [] \\ fs []
  THEN1
   (match_mp_tac subspt_exp_rel
    \\ qexists_tac `src_code`
    \\ conj_tac THEN1 fs [subspt_lookup,lookup_union]
    \\ match_mp_tac exp_rel_tick_inline \\ metis_tac [])
  \\ first_x_assum drule
  \\ disch_then (qspec_then `k` mp_tac) \\ fs []
  \\ qmatch_goalsub_rename_tac `(p1,p2,p3) :: in1`
  \\ disch_then (qspec_then `union src_code (insert p1 (p2,p3) LN)` mp_tac)
  \\ fs [exp_rel_rw] \\ disch_then match_mp_tac
  \\ reverse (IF_CASES_TAC \\ fs [])
  THEN1
   (fs [DISJOINT_DEF,EXTENSION,domain_union] \\ rw []
    \\ fs [lookup_union,lookup_insert,lookup_def,case_eq_thms]
    THEN1
     (first_x_assum drule \\ strip_tac \\ fs []
      \\ match_mp_tac (subspt_exp_rel |> ONCE_REWRITE_RULE [CONJ_COMM])
      \\ asm_exists_tac \\ fs []
      \\ fs [subspt_lookup,lookup_union])
    \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
  \\ reverse (rw [])
  \\ fs [lookup_insert,case_eq_thms] \\ rveq
  THEN1
   (rename1 `must_inline k2 _ _`
    \\ fs [lookup_union,case_eq_thms,GSYM lookup_NONE_domain]
    \\ match_mp_tac subspt_exp_rel
    \\ qexists_tac `src_code`
    \\ conj_tac THEN1 fs [subspt_lookup,lookup_union]
    \\ match_mp_tac exp_rel_tick_inline \\ metis_tac [])
  \\ fs [lookup_union,case_eq_thms,GSYM lookup_NONE_domain,lookup_insert,
         lookup_def]
  \\ first_x_assum drule \\ strip_tac \\ fs []
  \\ match_mp_tac (subspt_exp_rel |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ asm_exists_tac \\ fs []
  \\ fs [subspt_lookup,lookup_union]);
val _ = show "tick_compile_prog_IMP_exp_rel_replay=" local_program_relation_replay;
val state_rel_alt = state_rel_def;
val state_rel_def = state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM CONJ_ASSOC];
val tick_compile_prog_IMP = prove(
  ``tick_compile_prog limit q0 ((k,prog)::t) = (cs1,prog1) ==>
    ?p1 vs. prog1 = (k,p1)::vs /\ MAP FST vs = MAP FST t``,
  Cases_on `prog` \\ strip_tac \\ fs [tick_compile_prog_def]
  \\ imp_res_tac tick_inline_all_names \\ fs []
  \\ Cases_on `prog1` \\ fs []
  \\ Cases_on `h` \\ fs []);

val tick_compile_prog_IMP_exp_rel = local_program_relation_replay;
val in_do_app_lemma_goal = ``
  in_state_rel limit s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => (err <> Rabort Rtype_error ==> do_app op a t1 = Rerr err)
    | Rval (v,s2) => ?t2. in_state_rel limit s2 t2 /\
                          do_app op a t1 = Rval (v,t2)``;
val _ = (print "in_do_app_lemma_typed_goal="; print_term in_do_app_lemma_goal; print "\n");
val in_do_app_lemma_replay = prove (in_do_app_lemma_goal,
  Cases_on `op = Install`
  THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [state_rel_def] \\ rveq \\ fs []
    \\ fs [state_component_equality,in_state_rel_def]
    \\ fs [shift_seq_def,o_DEF] \\ rfs []
    \\ Cases_on `s1.compile_oracle 0` \\ fs []
    \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
    \\ PairCases_on `q` \\ fs [domain_union]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ fs [domain_fromAList,in_cc_def]
    \\ pairarg_tac \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ qpat_x_assum `_ = FST _` (assume_tac o GSYM) \\ fs []
    \\ drule tick_compile_prog_IMP \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ qpat_abbrev_tac `in1 = (k,prog)::t`
    \\ qpat_abbrev_tac `in2 = (k,p1)::vs`
    \\ fs [lookup_union,case_eq_thms]
    \\ reverse (rw [])
    THEN1
     (first_x_assum drule \\ strip_tac \\ fs []
      \\ match_mp_tac subspt_exp_rel \\ metis_tac [subspt_union])
    THEN1
     (reverse (Cases_on `lookup k' t1.code`) \\ fs []
      THEN1 (fs [domain_lookup,EXTENSION] \\ metis_tac [NOT_SOME_NONE])
      \\ fs [lookup_fromAList]
      \\ `DISJOINT (domain q0) (set (MAP FST in1))` by
       (fs [subspt_def,EXTENSION,DISJOINT_DEF,Abbr`in1`] \\ metis_tac [])
      \\ `ALL_DISTINCT (MAP FST in1)` by fs [Abbr `in1`]
      \\ match_mp_tac tick_compile_prog_IMP_exp_rel
      \\ asm_exists_tac \\ fs []
      \\ reverse conj_tac
      THEN1 (unabbrev_all_tac \\ fs [DISJOINT_DEF,EXTENSION] \\ metis_tac [])
      \\ rw [] \\ fs [subspt_lookup]
      \\ first_x_assum drule \\ strip_tac
      \\ rename1 `lookup k2 t1.code = SOME (arity2,v)`
      \\ Cases_on `lookup k2 s1.code`
      THEN1 (fs [domain_eq] \\ res_tac \\ fs [])
      \\ PairCases_on `x` \\ res_tac \\ fs []
      \\ rveq \\ fs [])
    \\ drule (tick_compile_prog_res_range |> SIMP_RULE std_ss [])
    \\ disch_then match_mp_tac \\ fs []
    \\ unabbrev_all_tac \\ fs []
    \\ CCONTR_TAC \\ fs [EXTENSION] \\ rveq \\ fs []
    \\ fs [subspt_def] \\ res_tac
    \\ fs [DISJOINT_DEF,EXTENSION]
    \\ metis_tac [])
  \\ strip_tac \\ reverse (Cases_on `do_app op a s1`) \\ fs []
  \\ `t1 = t1 with <| globals := s1.globals ;
                               refs := s1.refs ;
                               clock := s1.clock ;
                               ffi := s1.ffi |>` by
         fs [in_state_rel_def,state_component_equality]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  THEN1 (strip_tac \\ match_mp_tac do_app_Rerr_swap \\ fs [in_state_rel_def])
  \\ rename1 `_ = Rval x`
  \\ PairCases_on `x` \\ fs []
  \\ drule (do_app_Rval_swap |> GEN_ALL
      |> INST_TYPE [alpha|->gamma,beta|->delta,gamma|->alpha,delta|->beta])
  \\ fs []
  \\ disch_then (qspec_then `t1` mp_tac)
  \\ impl_tac THEN1 fs [in_state_rel_def]
  \\ fs [] \\ disch_then kall_tac
  \\ fs [in_state_rel_def]
  \\ imp_res_tac do_app_const \\ fs []);
val _ = show "in_do_app_lemma_replay=" in_do_app_lemma_replay;
val do_app_lemma_replay = prove (do_app_lemma_goal,
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [state_rel_def] \\ rveq \\ fs []
    \\ fs [state_component_equality]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `t'.compile_oracle 0` \\ fs []
      \\ Cases_on `r'` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ simp [map_fromAList, map_insert] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs []
    \\ rfs [FORALL_PROD,shift_seq_def,domain_map]
    \\ metis_tac [list_nchotomy,PAIR])
  \\ strip_tac \\ Cases_on `do_app op (REVERSE a) t'`
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [state_rel_alt]
    \\ disch_then (qspecl_then [`map (I ## (λx. HD (remove_ticks [x]))) t'.code`,
        `r.compile`,`(I ## MAP (I ## I ## (λx. HD (remove_ticks [x])))) ∘
          t'.compile_oracle`] mp_tac)
    \\ qpat_x_assum `r = _` (assume_tac o GSYM) \\ fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = r` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [state_rel_alt]
  \\ disch_then (qspecl_then [`map (I ## (λx. HD (remove_ticks [x]))) t'.code`,
      `r.compile`,`(I ## MAP (I ## I ## (λx. HD (remove_ticks [x])))) ∘
        t'.compile_oracle`] mp_tac)
  \\ qpat_x_assum `r = _` (assume_tac o GSYM) \\ fs []);
val _ = show "do_app_lemma_replay=" do_app_lemma_replay;
