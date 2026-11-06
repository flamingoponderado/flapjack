load "pattern_exhTheory";
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
