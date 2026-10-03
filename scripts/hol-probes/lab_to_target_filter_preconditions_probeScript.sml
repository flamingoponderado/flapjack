load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory labPropsTheory lab_filterTheory;
val th = prove (``∀code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (filter_skip code)``,
Induct>>TRY(Cases)>>fs[lab_filterTheory.filter_skip_def]>>rw[]>>
  Induct_on`l`>>fs[]>>rw[]);
val _ = show_types := true;
val _ = print "all_enc_ok_pre_filter_skip=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "all_enc_ok_pre_filter_skip_types=";
val _ = app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";")) (fst (strip_forall (concl th)) @ free_vars (concl th));
val _ = print "\n";
val _ = print ("all_enc_ok_pre_filter_skip_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n");
val _ = show_types := false;
val _ = print "all_enc_ok_pre_filter_skip_proved=";
val _ = print_term (rhs (concl (EQT_INTRO (prove (concl th, ACCEPT_TAC th)))));
val _ = print "\n";
