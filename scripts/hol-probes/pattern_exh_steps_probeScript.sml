load "pattern_exhTheory";
load "pattern_compTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = if null (hyp pattern_exhTheory.exh_steps_def) then
  (print "exh_steps="; print_term (concl pattern_exhTheory.exh_steps_def); print "\n")
  else raise Fail "exh_steps_def has hypotheses";
val _ = print "exh_steps_examples=";
val _ = print_term (rhs (concl (EVAL ``
  [pattern_exh$exh_steps []; pattern_exh$exh_steps [[]];
   pattern_exh$exh_steps [[pattern_semantics$Any]];
   pattern_exh$exh_steps_list [ []; [[pattern_semantics$Any]] ];
   pattern_exh$exh_steps [[pattern_semantics$Ref pattern_semantics$Any]]]
``)));
val _ = print "\n";
val _ = if null (hyp pattern_exhTheory.pand_def) then
  (print "pand="; print_term (concl pattern_exhTheory.pand_def); print "\n")
  else raise Fail "pand_def has hypotheses";
val _ = print "pmatch_result_type=";
val _ = print_type (type_of ``pattern_common$PMatchSuccess``);
val _ = print "\n";
val _ = print "pmatch_result_cases=";
val _ = print_term (concl pattern_commonTheory.pmatchResult_nchotomy);
val _ = print "\n";
val _ = print "pmatch_result_distinct=";
val _ = print_term (concl pattern_commonTheory.pmatchResult_distinct);
val _ = print "\n";
val pand_simps_replay = prove (
  ``!x y. pattern_exh$pand pattern_common$PMatchSuccess y = y /\
    pattern_exh$pand x pattern_common$PMatchSuccess = x /\
    pattern_exh$pand pattern_common$PTypeFailure y = pattern_common$PTypeFailure /\
    pattern_exh$pand x pattern_common$PTypeFailure = pattern_common$PTypeFailure``,
  Cases_on `x` >> fs [pattern_exhTheory.pand_def]);
val pand_type_replay = prove (
  ``!x y. (pattern_exh$pand x y = pattern_common$PTypeFailure) <=>
    x = pattern_common$PTypeFailure \/ y = pattern_common$PTypeFailure``,
  Cases_on `x` >> Cases_on `y` >> fs [pattern_exhTheory.pand_def]);
val pand_success_replay = prove (
  ``!x y. (pattern_exh$pand x y = pattern_common$PMatchSuccess) <=>
    x = pattern_common$PMatchSuccess /\ y = pattern_common$PMatchSuccess``,
  Cases_on `x` >> Cases_on `y` >> fs [pattern_exhTheory.pand_def]);
val pand_assoc_replay = prove (
  ``!x y z. pattern_exh$pand (pattern_exh$pand x y) z =
    pattern_exh$pand x (pattern_exh$pand y z)``,
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> fs [pattern_exhTheory.pand_def]);
fun show_local label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_local "pand_simps=" pand_simps_replay;
val _ = show_local "pand_type=" pand_type_replay;
val _ = show_local "pand_success=" pand_success_replay;
val _ = show_local "pand_assoc=" pand_assoc_replay;
val _ = if null (hyp pattern_exhTheory.exh_rows_eq) then
  (print "exh_rows_eq="; print_term (concl pattern_exhTheory.exh_rows_eq); print "\n")
  else raise Fail "exh_rows_eq has hypotheses";
val mats_append_replay = prove (
  ``!xs ys. pattern_exh$exh_mats (xs ++ ys) <=>
      pattern_exh$exh_mats xs /\ pattern_exh$exh_mats ys``,
  Induct >> fs [pattern_exhTheory.exh_matrix_def] >> metis_tac []);
val _ = if null (hyp mats_append_replay) then
  (print "exh_mats_append="; print_term (concl mats_append_replay); print "\n")
  else raise Fail "matrix append replay has hypotheses";
val all_replay = prove (
  ``!ms. pattern_exh$exh_all ms <=> pattern_exh$exh_mats ms``,
  ho_match_mp_tac pattern_exhTheory.exh_all_ind >>
  rw [pattern_exhTheory.exh_all_def, pattern_exhTheory.exh_matrix_def] >>
  simp [Once pattern_exhTheory.exh_matrix_def] >>
  every_case_tac >> fs [mats_append_replay]);
val _ = if null (hyp all_replay) then
  (print "exh_all_thm="; print_term (concl all_replay); print "\n")
  else raise Fail "worklist replay has hypotheses";
val append_replay = prove (
  ``!xs ys. pattern_exh$exh_steps_list (xs ++ ys) =
      pattern_exh$exh_steps_list xs + pattern_exh$exh_steps_list ys``,
  Induct >> simp [pattern_exhTheory.exh_steps_def]);
val _ = if null (hyp append_replay) then
  (print "exh_steps_list_append="; print_term (concl append_replay); print "\n")
  else raise Fail "append replay has hypotheses";
val _ = if null (hyp pattern_exhTheory.exh_all_def) then
  (print "exh_all="; print_term (concl pattern_exhTheory.exh_all_def); print "\n")
  else raise Fail "exh_all_def has hypotheses";
val _ = print "exh_all_examples=";
val _ = print_term (rhs (concl (EVAL ``
  [pattern_exh$exh_all []; pattern_exh$exh_all [[]];
   pattern_exh$exh_all [[[]]];
   pattern_exh$exh_all [[[pattern_semantics$Any]]];
   pattern_exh$exh_all [[[pattern_semantics$Ref pattern_semantics$Any]]]]
``)));
val _ = print "\n";
val _ = print "term_constructor_type=";
val _ = print_type (type_of ``pattern_semantics$Term``);
val _ = print "\n";
val _ = print "litv_constructor_type=";
val _ = print_type (type_of ``pattern_semantics$Litv``);
val _ = print "\n";
val _ = show_local "term_cases=" pattern_semanticsTheory.term_nchotomy;
val _ = show_local "term_distinct=" pattern_semanticsTheory.term_distinct;
val _ = show_local "is_sibling=" pattern_semanticsTheory.is_sibling_def;
val _ = show_local "pmatch=" pattern_semanticsTheory.pmatch_def;
val pmatch_any_replay = prove (
  ``!refs v. pattern_semantics$pmatch refs pattern_semantics$Any v = pattern_common$PMatchSuccess``,
  simp [pattern_semanticsTheory.pmatch_def]);
val _ = show_local "pmatch_any=" pmatch_any_replay;
val pmatch_list_nil_replay = prove (
  ``!refs v vs p ps.
    (pattern_semantics$pmatch_list refs [] [] = pattern_common$PMatchSuccess) /\
    (pattern_semantics$pmatch_list refs [] (v::vs) = pattern_common$PTypeFailure) /\
    (pattern_semantics$pmatch_list refs (p::ps) [] = pattern_common$PTypeFailure)``,
  simp [pattern_semanticsTheory.pmatch_def]);
val _ = show_local "pmatch_list_nil=" pmatch_list_nil_replay;
val pmatch_list_cons_replay = prove (
  ``!refs p ps v vs. pattern_semantics$pmatch_list refs (p::ps) (v::vs) =
    pattern_exh$pand (pattern_semantics$pmatch refs p v) (pattern_semantics$pmatch_list refs ps vs)``,
  simp [pattern_semanticsTheory.pmatch_def] >>
  Cases_on `pattern_semantics$pmatch refs p v` >> fs [pattern_exhTheory.pand_def] >>
  Cases_on `pattern_semantics$pmatch_list refs ps vs` >> fs []);
val _ = show_local "pmatch_list_cons=" pmatch_list_cons_replay;
val _ = show_local "pmatch_comp_length=" pattern_compTheory.pmatch_list_LENGTH;
val pmatch_exh_length_replay = prove (
  ``!refs ps vs. pattern_semantics$pmatch_list refs ps vs <> pattern_common$PTypeFailure ==>
    LENGTH ps = LENGTH vs``,
  metis_tac [pattern_compTheory.pmatch_list_LENGTH]);
val _ = show_local "pmatch_exh_length=" pmatch_exh_length_replay;
val pmatch_list_append_replay = prove (
  ``!ps us qs ws refs. LENGTH ps = LENGTH us ==>
    pattern_semantics$pmatch_list refs (ps ++ qs) (us ++ ws) =
    pattern_exh$pand (pattern_semantics$pmatch_list refs ps us)
      (pattern_semantics$pmatch_list refs qs ws)``,
  Induct >> Cases_on `us` >> fs [pmatch_list_nil_replay,
    pmatch_list_cons_replay, pand_assoc_replay, pand_simps_replay]);
val _ = show_local "pmatch_list_append=" pmatch_list_append_replay;
val length_anys_replay = prove (
  ``!n. LENGTH (pattern_exh$anys n) = n``,
  Induct >> fs [pattern_exhTheory.anys_def]);
val _ = show_local "length_anys=" length_anys_replay;
val pmatch_list_anys_replay = prove (
  ``!n vs refs. pattern_semantics$pmatch_list refs (pattern_exh$anys n) vs =
    (if LENGTH vs = n then pattern_common$PMatchSuccess else pattern_common$PTypeFailure)``,
  Induct >> Cases_on `vs` >> fs [pattern_exhTheory.anys_def,
    pattern_semanticsTheory.pmatch_def]);
val _ = show_local "pmatch_list_anys=" pmatch_list_anys_replay;
val mem_ctor_nub_replay = prove (
  ``!l x. MEM x (pattern_exh$ctor_nub l) <=> MEM x l``,
  Induct >> fs [pattern_exhTheory.ctor_nub_def] >> rw [] >> metis_tac []);
val _ = show_local "mem_ctor_nub=" mem_ctor_nub_replay;
val mem_ctor_keep_replay = prove (
  ``!xs ys x. MEM x (pattern_exh$ctor_keep xs ys) <=> MEM x xs /\ MEM x ys``,
  Induct >> fs [pattern_exhTheory.ctor_keep_def] >> rw [] >> metis_tac []);
val _ = show_local "mem_ctor_keep=" mem_ctor_keep_replay;
val mem_tag_ctors_replay = prove (
  ``!sibs t a. MEM (pattern_exh$TagC t a) (pattern_exh$tag_ctors sibs) <=> MEM (t,a) sibs``,
  Induct >> fs [pattern_exhTheory.tag_ctors_def, pairTheory.FORALL_PROD] >> metis_tac []);
val _ = show_local "mem_tag_ctors=" mem_tag_ctors_replay;
val mem_spec_mats_replay = prove (
  ``!cs c rows. MEM c cs ==> MEM (pattern_exh$spec_mat c rows) (pattern_exh$spec_mats cs rows)``,
  Induct >> fs [pattern_exhTheory.spec_mats_def] >> metis_tac []);
val _ = show_local "mem_spec_mats=" mem_spec_mats_replay;
val mem_add_head_replay = prove (
  ``!yss x ys. MEM ys (pattern_exh$add_head x yss) <=> ?zs. MEM zs yss /\ ys = x::zs``,
  Induct >> fs [pattern_exhTheory.add_head_def] >> metis_tac []);
val _ = show_local "mem_add_head=" mem_add_head_replay;
val mem_mk_prods_replay = prove (
  ``!xs yss zs. MEM zs (pattern_exh$mk_prods xs yss) <=>
    ?x ys. MEM x xs /\ MEM ys yss /\ zs = x::ys``,
  Induct >> fs [pattern_exhTheory.mk_prods_def, mem_add_head_replay] >> metis_tac []);
val _ = show_local "mem_mk_prods=" mem_mk_prods_replay;
val mem_mk_refs_replay = prove (
  ``!ps q. MEM q (pattern_exh$mk_refs ps) <=> ?p. MEM p ps /\ q = pattern_semantics$Ref p``,
  Induct >> fs [pattern_exhTheory.mk_refs_def] >> metis_tac []);
val _ = show_local "mem_mk_refs=" mem_mk_refs_replay;
val mem_mk_conses_replay = prove (
  ``!pss t q. MEM q (pattern_exh$mk_conses t pss) <=> ?ps. MEM ps pss /\ q = pattern_semantics$Cons t ps``,
  Induct >> fs [pattern_exhTheory.mk_conses_def] >> metis_tac []);
val _ = show_local "mem_mk_conses=" mem_mk_conses_replay;
val mem_mk_rows_replay = prove (
  ``!ps r. MEM r (pattern_exh$mk_rows ps) <=> ?p. MEM p ps /\ r = [p]``,
  Induct >> fs [pattern_exhTheory.mk_rows_def] >> metis_tac []);
val _ = show_local "mem_mk_rows=" mem_mk_rows_replay;
val length_expand_list_replay = prove (
  ``!ps qs. MEM qs (pattern_exh$expand_list ps) ==> LENGTH qs = LENGTH ps``,
  Induct >> fs [pattern_exhTheory.expand_def, mem_mk_prods_replay] >> rw [] >> res_tac >> fs []);
val _ = show_local "length_expand_list=" length_expand_list_replay;
val _ = augment_srw_ss [rewrites [pand_simps_replay, pand_type_replay,
  pand_success_replay, pmatch_any_replay, pmatch_list_nil_replay,
  pmatch_list_cons_replay, pmatch_list_anys_replay, mem_ctor_nub_replay,
  mem_ctor_keep_replay, mem_add_head_replay, mem_mk_prods_replay,
  mem_mk_refs_replay, mem_mk_conses_replay, mem_mk_rows_replay]];
val expand_thm_replay = prove (
  ``(!p q refs v.
      MEM q (pattern_exh$expand p) /\ pattern_semantics$pmatch refs p v <> pattern_common$PTypeFailure ==>
      pattern_semantics$pmatch refs q v <> pattern_common$PTypeFailure /\
      (pattern_semantics$pmatch refs q v = pattern_common$PMatchSuccess ==>
       pattern_semantics$pmatch refs p v = pattern_common$PMatchSuccess)) /\
    (!ps qs refs vs.
      MEM qs (pattern_exh$expand_list ps) /\ pattern_semantics$pmatch_list refs ps vs <> pattern_common$PTypeFailure ==>
      pattern_semantics$pmatch_list refs qs vs <> pattern_common$PTypeFailure /\
      (pattern_semantics$pmatch_list refs qs vs = pattern_common$PMatchSuccess ==>
       pattern_semantics$pmatch_list refs ps vs = pattern_common$PMatchSuccess))``,
  ho_match_mp_tac pattern_semanticsTheory.pat_induction >> rpt conj_tac
  >- fs [pattern_exhTheory.expand_def]
  >- (rw [pattern_exhTheory.expand_def] >> imp_res_tac length_expand_list_replay >>
      Cases_on `v` >> fs [pattern_semanticsTheory.pmatch_def] >>
      Cases_on `o'` >> Cases_on `o''` >> fs [pattern_semanticsTheory.pmatch_def] >>
      TRY (Cases_on `x`) >> fs [pattern_semanticsTheory.pmatch_def] >>
      rw [] >> rfs [] >> res_tac >> fs [])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `pattern_semantics$pmatch refs p v <> pattern_common$PTypeFailure /\
       pattern_semantics$pmatch refs p' v <> pattern_common$PTypeFailure` by
        (qpat_x_assum `pattern_semantics$pmatch refs (pattern_semantics$Or _ _) _ <> _` mp_tac >>
         fs [pattern_semanticsTheory.pmatch_def] >> every_case_tac >> fs []) >>
      fs [pattern_exhTheory.expand_def] >> res_tac >> fs [pattern_semanticsTheory.pmatch_def] >>
      Cases_on `pattern_semantics$pmatch refs p v` >>
      Cases_on `pattern_semantics$pmatch refs p' v` >> fs [])
  >- fs [pattern_exhTheory.expand_def]
  >- (fs [pattern_exhTheory.expand_def] >> rw [] >>
      Cases_on `v` >> fs [pattern_semanticsTheory.pmatch_def] >>
      Cases_on `FLOOKUP refs n` >> fs [pattern_semanticsTheory.pmatch_def] >> res_tac >> fs [])
  >- fs [pattern_exhTheory.expand_def]
  >> fs [pattern_exhTheory.expand_def] >> rw [] >> Cases_on `vs` >> fs [] >> res_tac >> fs []);
val _ = show_local "expand_thm=" expand_thm_replay;
val _ = show_local "dest_val=" pattern_exhTheory.dest_val_def;
val dest_val_eq_some_replay = prove (
  ``!refs v c as. pattern_exh$dest_val refs v = SOME (c,as) <=>
    (?t. v = pattern_semantics$Term (SOME t) as /\ c = pattern_exh$TagC t (LENGTH as)) \/
    (v = pattern_semantics$Term NONE as /\ c = pattern_exh$TupC (LENGTH as)) \/
    (?r w. v = pattern_semantics$RefPtr r /\ FLOOKUP refs r = SOME w /\ as = [w] /\ c = pattern_exh$RefC)``,
  rpt gen_tac >> Cases_on `v` >> fs [pattern_exhTheory.dest_val_def]
  >- (Cases_on `o'` >> fs [pattern_exhTheory.dest_val_def] >> metis_tac [])
  >> CASE_TAC >> fs [] >> metis_tac []);
val _ = show_local "dest_val_eq_some=" dest_val_eq_some_replay;
val length_dest_val_replay = prove (
  ``!refs v c as. pattern_exh$dest_val refs v = SOME (c,as) ==> LENGTH as = pattern_exh$ctor_arity c``,
  fs [dest_val_eq_some_replay] >> rw [] >> fs [pattern_exhTheory.ctor_arity_def]);
val _ = show_local "length_dest_val=" length_dest_val_replay;
