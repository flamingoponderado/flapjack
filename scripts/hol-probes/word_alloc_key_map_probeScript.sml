load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;

fun print_eval label q =
  (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "key_map_mixed"
  ``MAP FST (sptree$toAList
      (apply_nummap_key (\n. n + 1)
        (sptree$fromAList [(0,()); (1,()); (2,()); (3,()); (4,()); (9,())])))``;
val _ = print_eval "key_map_collision"
  ``MAP FST (sptree$toAList
      (apply_nummap_key (\n. n MOD 3)
        (sptree$fromAList [(9,()); (2,()); (1,()); (0,()); (9,()); (4,())])))``;
val _ = print_eval "key_map_done" ``T``;
