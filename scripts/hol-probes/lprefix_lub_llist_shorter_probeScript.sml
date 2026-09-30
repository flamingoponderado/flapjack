(*)
  Direct HOL observations for the finite instances of `llist_shorter` used by
  the pinned external script `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`
  (`llist_shorter_def` at :122-129, `llist_shorter_fromList` at :163-169).

  `llist_shorter` pattern-matches on `(LLENGTH ll1, LLENGTH ll2)`.  For the
  finite `fromList` inputs used here, the source definition is reduced with the
  companion library theorem `LLENGTH_fromList` (the same technique the
  `loop_sem_lprefix_lub_probe` uses for `LNTH_fromList`), then `EVAL` computes
  the resulting `LENGTH` comparison.  This gives an original-HOL finite oracle
  for the Lean `llistShorter_fromList` port.
*)
load "bossLib";
load "preamble";
load "loopSemTheory";
open bossLib HolKernel Parse preamble;
open lprefix_lubTheory;

fun print_eval label q =
  let
    val source = SIMP_CONV (srw_ss())
      [lprefix_lubTheory.llist_shorter_def,
       llistTheory.LLENGTH_fromList] q
    val th = EVAL (rconc source)
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "llist_shorter_shorter"
  ``llist_shorter (llist$fromList [1;2]) (llist$fromList [1;2;3])``;
val _ = print_eval "llist_shorter_equal_length"
  ``llist_shorter (llist$fromList [1;2;3]) (llist$fromList [4;5;6])``;
val _ = print_eval "llist_shorter_longer"
  ``llist_shorter (llist$fromList [1;2;3]) (llist$fromList [1;2])``;
val _ = print_eval "llist_shorter_two_empty"
  ``llist_shorter (llist$fromList ([] : num list)) (llist$fromList ([] : num list))``;
val _ = print_eval "llist_shorter_nil_nonempty"
  ``llist_shorter (llist$fromList ([] : num list)) (llist$fromList [1])``;
val _ = print_eval "llist_shorter_nonempty_nil"
  ``llist_shorter (llist$fromList [1]) (llist$fromList ([] : num list))``;
val _ = print_eval "llist_shorter_reverse_longer"
  ``llist_shorter (llist$fromList [3;2;1]) (llist$fromList [1;2])``;
val _ = print_eval "llist_shorter_equal_nonempty"
  ``llist_shorter (llist$fromList [7;8]) (llist$fromList [8;7])``;
