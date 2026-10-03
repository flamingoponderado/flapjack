load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble stackSemTheory word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val clockLaw = prove(``∀x t.
 evaluate(wStackLoad x Skip,t with clock:= clk) =
 (I ## (\s. s with clock := clk)) (evaluate(wStackLoad x Skip,t))``,
 Induct>>fs[wStackLoad_def,FORALL_PROD,stackSemTheory.evaluate_def,LET_THM]>>rw[]);
val _ = if null(hyp clockLaw) then () else raise Fail "open premise";
val _ = (print "load_clock_statement="; print_thm clockLaw; print "\n");
val _ = print("load_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO clockLaw))) ^ "\n");
val _ = print("load_clock_hypotheses=" ^ Int.toString(length(hyp clockLaw)) ^ "\n");
