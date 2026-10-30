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
val _ = show "in_cc=" bvl_inlineProofTheory.in_cc_def;
val _ = show "in_state_rel=" bvl_inlineProofTheory.in_state_rel_def;
val _ = show "evaluate_inline=" bvl_inlineProofTheory.evaluate_inline;
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
val state_rel_alt = state_rel_def;
val state_rel_def = state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM CONJ_ASSOC];
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
