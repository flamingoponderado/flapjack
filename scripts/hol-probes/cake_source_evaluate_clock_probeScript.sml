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
val fixed = rhs (concl (EVAL ``(FST (evaluate$fix_clock
  ((ARB:'ffi semanticPrimitives$state) with clock := 3)
  (((ARB:'ffi semanticPrimitives$state) with clock := 7),T))).clock``));
val _ = (print "fixed="; print_term fixed; print "\n");
val zero = rhs (concl (EVAL ``(evaluate$dec_clock
  ((ARB:'ffi semanticPrimitives$state) with clock := 0)).clock``));
val _ = (print "zero="; print_term zero; print "\n");
val failure = rhs (concl (EVAL ``evaluate$list_result (Rerr (Rraise (1:num)) : (bool,num) result)``));
val _ = (print "failure="; print_term failure; print "\n");
