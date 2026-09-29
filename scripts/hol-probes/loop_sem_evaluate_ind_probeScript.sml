(*
  Direct HOL capture of the auto-generated loopSem$evaluate_ind induction
  principle.

  loopSemScript.sml:497 defines

      Theorem evaluate_ind[allow_rebind] =
        REWRITE_RULE [fix_clock_evaluate] evaluate_ind

  so the per-constructor statement is produced by tdefn and is not textually
  present in the source.  This probe prints the conclusion of the constant so
  the Lean case principle can be compared clause-for-clause (motive arity,
  clause hypotheses, relation guards, branch-split structure).

  Reference: cakeml/pancake/semantics/loopSemScript.sml:497 (and the
  rewritten theorem at :497).
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val _ = print "evaluate_ind=";
val _ = print_term (concl evaluate_ind);
val _ = print "\n";
