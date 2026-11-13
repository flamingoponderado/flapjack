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
