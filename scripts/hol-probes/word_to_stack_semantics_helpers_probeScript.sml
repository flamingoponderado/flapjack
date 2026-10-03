load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory
  wordSemTheory stackSemTheory wordLangTheory stackLangTheory wordConvsTheory
  wordPropsTheory miscTheory sptreeTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val th = GEN_ALL(prove(``state_rel ac a 0 0 s t lens extra ⇒
  state_rel ac a 0 0 (s with clock := k) (t with clock := k) lens extra``,
rw[state_rel_def]\\metis_tac[]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "state_rel_with_clock_statement="; print_term(concl th));
val _ = print("state_rel_with_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("state_rel_with_clock_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``wordSem$evaluate (Call NONE dest args handler, s) = (res, s') ⇒
  (∀n. res ≠ SOME (Break n)) ∧ (∀n. res ≠ SOME (Continue n))``,
simp[wordSemTheory.evaluate_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  rw[] >> strip_tac >> fs[bad_fun_return_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "word_Call_NONE_not_Break_Continue_statement="; print_term(concl th));
val _ = print("word_Call_NONE_not_Break_Continue_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("word_Call_NONE_not_Break_Continue_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``stackSem$evaluate (Call NONE dest handler, s) = (res, s') ⇒
  (∀n. res ≠ SOME (Break n)) ∧ (∀n. res ≠ SOME (Continue n))``,
simp[stackSemTheory.evaluate_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  rw[] >> strip_tac >> fs[stackSemTheory.bad_fun_return_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "stack_Call_NONE_not_Break_Continue_statement="; print_term(concl th));
val _ = print("stack_Call_NONE_not_Break_Continue_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("stack_Call_NONE_not_Break_Continue_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
