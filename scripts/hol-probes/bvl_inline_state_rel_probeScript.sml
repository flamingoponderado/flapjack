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
