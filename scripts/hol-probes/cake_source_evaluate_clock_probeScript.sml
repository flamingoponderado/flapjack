load "evaluateTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "fix_type="; print_type (type_of ``evaluate$fix_clock``); print "\n");
val _ = (print "list_type="; print_type (type_of ``evaluate$list_result``); print "\n");
val replay = prove (``∀s x s1 res.
  evaluate$fix_clock s x = (s1,res) ⇒ s1.clock ≤ s.clock``,
  rpt gen_tac THEN Cases_on `x` THEN fs[evaluateTheory.fix_clock_def] THEN rw[] THEN fs[]);
val _ = (print "clock_lemma="; print_thm replay; print "\n");
val _ = (print "eval_clock_lemma="; print_thm evaluateTheory.fix_clock_do_eval_res; print "\n");
val _ = (print "full_evaluate_ind="; print_thm evaluateTheory.full_evaluate_ind; print "\n");
val _ = (print "evaluate_ind="; print_thm evaluateTheory.evaluate_ind; print "\n");
val _ = (print "evaluate_clock="; print_thm evaluateTheory.evaluate_clock; print "\n");
val raiseReplay = prove (``∀(s:'ffi semanticPrimitives$state) env e r s2.
  evaluate s env [Raise e] = (s2,r) ⇒ s2.clock ≤ s.clock``,
  metis_tac [evaluateTheory.evaluate_clock]);
val _ = (print "raise_clock="; print_thm raiseReplay; print "\n");
val fixed = rhs (concl (EVAL ``(FST (evaluate$fix_clock
  ((ARB:'ffi semanticPrimitives$state) with clock := 3)
  (((ARB:'ffi semanticPrimitives$state) with clock := 7),T))).clock``));
val _ = (print "fixed="; print_term fixed; print "\n");
val zero = rhs (concl (EVAL ``(evaluate$dec_clock
  ((ARB:'ffi semanticPrimitives$state) with clock := 0)).clock``));
val _ = (print "zero="; print_term zero; print "\n");
val failure = rhs (concl (EVAL ``evaluate$list_result (Rerr (Rraise (1:num)) : (bool,num) result)``));
val _ = (print "failure="; print_term failure; print "\n");
