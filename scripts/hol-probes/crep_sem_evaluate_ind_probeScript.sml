(*
  Direct HOL capture of the auto-generated crepSem$evaluate_ind induction
  principle.

  crepSemScript.sml:440 defines

      val evaluate_ind = save_thm("evaluate_ind",
                    REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

  so the per-constructor statement is produced by tdefn and is not textually
  present in the source.  This probe prints the conclusion of the constant so
  the Lean case principle can be compared clause-for-clause (motive arity,
  clause hypotheses, relation guards, branch-split structure).

  Reference: cakeml/pancake/semantics/crepSemScript.sml:440 (and the
  evaluate_def at :240 / rewritten theorem at :443).
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val _ = print "evaluate_ind=";
val _ = print_term (concl evaluate_ind);
val _ = print "\n";
