(* Fresh direct original Spt-pair maximum observations. *)
load "bossLib";
load "preamble";
load "wordLangTheory";
open bossLib HolKernel Parse preamble wordLangTheory;
fun out label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = out "cm_empty" ``cutsets_max (LN,LN) = 0``;
val _ = out "cm_left" ``cutsets_max (insert 5 () LN,LN) = 5``;
val _ = out "cm_right" ``cutsets_max (LN,insert 17 () LN) = 17``;
val _ = out "cm_both" ``cutsets_max (insert 5 () LN,insert 17 () LN) = 17``;
val _ = out "cm_zero" ``cutsets_max (LS (),LN) = 0``;
val _ = out "cm_nonwf" ``cutsets_max (BN LN LN,LN) = 0``;
val _ = out "cm_raw" ``cutsets_max (BS LN () (LS ()),LN) = 1``;
val _ = out "cm_deep" ``cutsets_max (insert 87 () (insert 5 () LN),insert 17 () LN) = 87``;
