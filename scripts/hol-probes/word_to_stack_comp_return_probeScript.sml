load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory
  wordSemTheory stackSemTheory wordLangTheory stackLangTheory;
val _ = Globals.linewidth := 1000000;
val whole = GEN_ALL (Q.SPECL [`wordLang$Return register names`, `s`] word_to_stackProofTheory.comp_correct);
val _ = if null(hyp whole) andalso null(free_vars(concl whole)) then () else raise Fail "open case";
val _ = (print "return_full_original_simulation="; print_term(concl whole); print "\n");
val _ = print("return_full_original_proved=" ^ term_to_string(rhs(concl(EQT_INTRO whole))) ^ "\n");
val _ = print("return_full_original_hypotheses=" ^ Int.toString(length(hyp whole)) ^ "\n");
