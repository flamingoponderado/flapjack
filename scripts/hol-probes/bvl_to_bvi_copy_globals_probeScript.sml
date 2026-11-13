load "bvl_to_bviProofTheory";
load "preamble";
open preamble bvl_to_bviTheory bvlSemTheory bviSemTheory bviPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj",
  "fromAList_def", "domain_union", "domain_insert", "domain_inter"];
val _ = augment_srw_ss [rewrites [SNOC_APPEND]];
val iEval_def = bviSemTheory.evaluate_def;
val iEvalOp_def = bviSemTheory.do_app_def;
val bEvalOp_def = bvlSemTheory.do_app_def;
val copy_globals_replay = prove (``∀n l1 s.
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code) ∧
   FLOOKUP s.refs p = SOME (ValueArray ls) ∧
   FLOOKUP s.refs p1 = SOME (ValueArray l1) ∧
   p ≠ p1 ∧
   n < LENGTH ls ∧ n < LENGTH l1
   ⇒
   ∃c.
     evaluate ([SND CopyGlobals_code],
               [RefPtr b1 p1; RefPtr b p; Number &n],
               inc_clock c s) =
     (Rval [Unit], s with refs := s.refs |+ (p1, ValueArray (TAKE (SUC n) ls ++ DROP (SUC n) l1)))`` ,
  Induct >> srw_tac[][] >> srw_tac[][CopyGlobals_code_def] >>
  srw_tac[][iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,do_int_app_def,
  bvl_to_bvi_id,backend_commonTheory.small_enough_int_def,bvl_to_bvi_with_refs] >- (
    qexists_tac`0`>>simp[inc_clock_ZERO,state_component_equality] >>
    rpt AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_LUPDATE] >>
    srw_tac[][] >> simp[EL_APPEND2,EL_DROP] >>
    Cases_on`ls`>>full_simp_tac(srw_ss())[]) >>
  simp[find_code_def] >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`l2 = LUPDATE x y z` >>
  qpat_abbrev_tac`rf = s.refs |+ X` >>
  first_x_assum(qspecl_then[`l2`,`s with refs := rf`]mp_tac) >>
  impl_tac >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    simp[Abbr`l2`] ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with refs := rf)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n:int` by (
    simp[ADD1] >> intLib.COOPER_TAC ) >>
  simp[state_component_equality] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE] >>
  srw_tac[][] >>
  simp[LIST_EQ_REWRITE,Abbr`l2`] >> srw_tac[][] >>
  Cases_on`x < SUC n` >> simp[EL_APPEND1,EL_TAKE] >>
  simp[EL_APPEND2,EL_DROP,EL_LUPDATE] >>
  Cases_on`x = SUC n` >> simp[EL_APPEND1,EL_TAKE,EL_APPEND2,EL_DROP]);
val _ = if null (hyp copy_globals_replay) then
  (print "copy_globals_replay="; print_term (concl copy_globals_replay); print "\n")
  else raise Fail "copy_globals_replay has hypotheses";
val copy_globals_generalized = Q.GEN `ls` copy_globals_replay;
val _ = if null (hyp copy_globals_generalized) then
  (print "copy_globals_generalized="; print_term (concl copy_globals_generalized); print "\n")
  else raise Fail "copy_globals_generalized has hypotheses";

val evaluate_CopyGlobals_code = copy_globals_generalized;
val alloc_global_replay = prove (``FLOOKUP s.refs p = SOME (ValueArray (Number(&(SUC n))::ls)) ∧ n ≤ LENGTH ls ∧
   s.global = SOME p ∧
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code)
   ⇒
   ∃p1 c extra.
     (p1 ≠ p ⇒ p1 ∉ FDOM s.refs) ∧
     n+k+1 ≤ LENGTH ls + extra ∧
     evaluate ([SND AllocGlobal_code],[Number (& k)],inc_clock c s) =
       (Rval [Unit],
        s with <| global := SOME p1; refs := s.refs
          |+ (p, ValueArray ((Number(&(SUC(n+k))))::ls))
          |+ (p1, ValueArray ((Number(&(SUC(n+k))))::
                              ls ++ (REPLICATE extra (Number 0))))|>)``,
  strip_tac
  \\ simp [AllocGlobal_code_def]
  \\ simp [Once iEval_def,iEvalOp_def]
  \\ ntac 7 $ simp [Once iEval_def,iEvalOp_def,inc_clock_def,do_app_aux_def]
  \\ simp [Once iEval_def,iEvalOp_def,inc_clock_def,do_app_aux_def,do_int_app_def]
  \\ simp [EVAL “small_enough_int 0”]
  \\ simp [Once iEval_def,iEvalOp_def,inc_clock_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ rename [‘evaluate
                ([Op (IntOp Add) [Var 0; Var 2]],
                 [Number (&SUC n); RefPtr T p; Number (&k)],_)’]
  \\ ntac 4 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,inc_clock_def,do_app_aux_def,bvlSemTheory.do_app_def,do_int_app_def]
  \\ ntac 3 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,inc_clock_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ simp [bvl_to_bvi_id]
  \\ ntac 8 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ simp [EVAL “small_enough_int 0”]
  \\ ntac 5 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def,integerTheory.INT_ADD,do_int_app_def]
  \\ fs [ADD1] \\ CASE_TAC
  >-
   (gvs [bvl_to_bvi_def,bvi_to_bvl_def,iEval_def,state_component_equality]
    \\ qexists_tac ‘0’ \\ gvs [LUPDATE_def])
  \\ gvs [bvl_to_bvi_def,bvi_to_bvl_def]
  \\ ntac 5 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ simp [EVAL “small_enough_int 0”]
  \\ ntac 5 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def,integerTheory.INT_ADD,do_int_app_def]
  \\ gvs [bvl_to_bvi_def,bvi_to_bvl_def]
  \\ ntac 2 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def,integerTheory.INT_ADD]
  \\ ntac 10 $ simp [Once iEval_def]
  \\ simp [iEvalOp_def,do_app_aux_def,bvlSemTheory.do_app_def,do_int_app_def]
  \\ simp [EVAL “small_enough_int 0”,EVAL “small_enough_int 1”]
  \\ simp [do_int_app_def]
  \\ gvs [bvl_to_bvi_def,bvi_to_bvl_def,find_code_def,dec_clock_def]
  \\ qabbrev_tac ‘new_p = LEAST ptr. ptr ≠ p ∧ ptr ∉ FDOM s.refs’
  \\ qexists_tac ‘new_p’ \\ fs []
  \\ Q.REFINE_EXISTS_TAC ‘ccc+1’ \\ fs []
  \\ gvs [AllCaseEqs()]
  \\ qpat_abbrev_tac ‘new_refs = _ |+ _ |+ _’
  \\ simp [GSYM integerTheory.INT_ADD,int_arithTheory.elim_minus_ones]
  \\ qabbrev_tac ‘s1 = s with <| refs := new_refs ; global := SOME new_p; ffi := s.ffi |>’
  \\ ‘lookup CopyGlobals_location s1.code = SOME (3,SND CopyGlobals_code)’
        by fs [Abbr‘s1’]
  \\ old_drule (GEN_ALL evaluate_CopyGlobals_code)
  \\ disch_then $ qspecl_then [‘new_p’,‘p’] mp_tac
  \\ ‘p ≠ new_p ∧ new_p ∉ FDOM s.refs’ by
    (`∃x. (λptr. ptr NOTIN FDOM (s.refs |+ (p,ARB))) x` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
     \\ old_drule WhileTheory.LEAST_INTRO \\ fs [])
  \\ fs []
  \\ simp [Abbr‘s1’,FLOOKUP_UPDATE,Abbr‘new_refs’,inc_clock_def]
  \\ disch_then $ qspecl_then [‘T’,‘T’,‘LENGTH ls’] mp_tac
  \\ impl_tac >- gvs []
  \\ strip_tac \\ gvs [LUPDATE_def]
  \\ qexists_tac ‘c’ \\ fs []
  \\ simp [state_component_equality]
  \\ qmatch_goalsub_abbrev_tac ‘REPLICATE kk’
  \\ qexists_tac ‘kk’ \\ fs [Abbr‘kk’]
  \\ simp [integerTheory.INT_ADD]);
val _ = if null (hyp alloc_global_replay) then
  (print "alloc_global_replay="; print_term (concl alloc_global_replay); print "\n")
  else raise Fail "alloc_global_replay has hypotheses";
