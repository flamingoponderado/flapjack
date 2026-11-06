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
