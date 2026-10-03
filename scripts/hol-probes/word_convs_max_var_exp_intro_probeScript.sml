load "preamble"; load "wordConvsTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory
 wordsTheory arithmeticTheory listTheory;
val _ = Globals.linewidth := 1000000;
(* Replay original local theorem with its unchanged proof. GEN_ALL closes P. *)
val original = GEN_ALL (Q.prove(`
 ∀exp. P 0 ∧ every_var_exp P exp ⇒ P (max_var_exp exp)`,
  ho_match_mp_tac max_var_exp_ind>>fs[max_var_exp_def,every_var_exp_def]>>
  srw_tac[][]
  >- (match_mp_tac MAX_LIST_intro>> fs[EVERY_MAP,EVERY_MEM])
  >> metis_tac [MAX_CASES]));
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "max_var_exp_intro_statement="; print_term(concl original); print "\n");
val _ = print("max_var_exp_intro_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("max_var_exp_intro_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");

(* Full exported original theorem, fetched from the read-only HOL theory. *)
val full = GEN_ALL (DB.fetch "wordConvs" "max_var_intro");
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open full theorem";
val _ = (print "max_var_intro_statement="; print_term(concl full); print "\n");
val _ = print("max_var_intro_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
val _ = print("max_var_intro_hypotheses=" ^ Int.toString(length(hyp full)) ^ "\n");
