load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory wordSemTheory stackSemTheory wordLangTheory stackLangTheory;
val _ = Globals.linewidth := 1000000;
val handler = GEN_ALL(prove(``  evaluate (c,s) = (res,s1) ∧ cont_loop res ⇒ s1.handler = s.handler``,
  rpt strip_tac \\
  qspecl_then [`c`,`s`] mp_tac wordPropsTheory.evaluate_stack_swap \\
  simp[] \\
  Cases_on `res` \\ gvs[] \\
  rename1 `cont_loop (SOME x')` \\
  Cases_on `x'` \\ gvs[] \\ strip_tac \\ fs[]));
val _ = (print "loop_handler_full="; print_thm handler; print "\n");
val _ = print("loop_handler_hypotheses=" ^ Int.toString(length(hyp handler)) ^ "\n");
val _ = print("loop_handler_proved=" ^ term_to_string(rhs(concl(EQT_INTRO handler))) ^ "\n");
