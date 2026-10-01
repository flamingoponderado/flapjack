load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory reg_allocTheory;
val merge_moves_frame2 = GEN_ALL(prove(``∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∧
  domain ssaR' = domain ssaR ∧
  ∀x. MEM x ls ∧ x ∈ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaR'``, Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >> TRY
    (full_simp_tac(srw_ss())[domain_inter]>>srw_tac[][]>>
    qpat_x_assum`A=domain ssaL` (sym_sub_tac)>>
    qpat_x_assum`A=domain ssaR` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[domain_lookup]>>
    full_simp_tac(srw_ss())[optionTheory.SOME_11]>>
    res_tac>>
    rev_full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][]>>
    metis_tac[domain_lookup,lookup_insert]));
val merge_moves_frame3 = GEN_ALL(prove(``∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  ∀x. ¬MEM x ls ∨ x ∉ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaL ∧
    lookup x ssaR' = lookup x ssaR``, Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(metis_tac[])>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame2>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  `h ∈ domain r3 ∧ h ∈ domain r2` by full_simp_tac(srw_ss())[domain_lookup]>>
  full_simp_tac(srw_ss())[domain_inter]>>
  metis_tac[]));
val _ = (print "frame3_full_source_replay="; print_thm merge_moves_frame3; print "\n");
val _ = (print "frame3_empty="; print_thm (Q.SPECL [`[]`,`8`,`LN:num num_map`,`LN:num num_map`] merge_moves_frame3); print "\n");
fun application label names left right key = let
 val th = Q.SPECL [names,`8`,left,right] merge_moves_frame3
 val merge = Parse.Term [QUOTE "merge_moves ", ANTIQUOTE (Parse.Term names), QUOTE " ", ANTIQUOTE (Parse.Term left), QUOTE " ", ANTIQUOTE (Parse.Term right), QUOTE " 8"]
 val expanded = CONV_RULE (SIMP_CONV pure_ss [EVAL merge,LET_THM,pairTheory.UNCURRY_DEF]) th
 val specialised = SPEC (Parse.Term key) expanded
 val _ = if is_imp(concl specialised) then () else raise Fail "original guard lost"
 val result = MATCH_MP specialised (prove(fst(dest_imp(concl specialised)), EVAL_TAC))
 val _ = if null(hyp result) then () else raise Fail "unexpected hypothesis"
 in print(label ^ "="); print_term(rconc(EQT_INTRO result)); print "\n" end;
val _ = application "frame3_absent" `[0;0]:num list` `LS 1:num num_map` `LS 3:num num_map` `2:num`;
val _ = application "frame3_outside" `[0]:num list` `LN:num num_map` `LS 3:num num_map` `0:num`;
val _ = (print "frame3_absent_result="; print_term(rconc(EVAL ``merge_moves [0;0] (LS 1:num num_map) (LS 3:num num_map) 8``)); print "\n");
val _ = (print "frame3_outside_result="; print_term(rconc(EVAL ``merge_moves [0] (LN:num num_map) (LS 3:num num_map) 8``)); print "\n");
val _ = (print "frame3_common_guard="; print_term(rconc(EVAL ``~MEM 0 [0] \/ 0 NOTIN domain (inter (LS 1:num num_map) (LS 3:num num_map))``)); print "\n");
