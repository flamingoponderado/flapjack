load "preamble"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble stackPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "code_bitmaps_full_statement="; print_term(concl evaluate_code_bitmaps));
val _ = print("code_bitmaps_full_hypotheses=" ^ Int.toString(length(hyp evaluate_code_bitmaps)) ^ "\n");
val _ = (print "code_bitmaps_callreturn_statement="; print_term(concl(ISPEC
  ``stackLang$Call (SOME (retH,link,l1,l2)) dest handler:64 stackLang$prog``
  evaluate_code_bitmaps)));
