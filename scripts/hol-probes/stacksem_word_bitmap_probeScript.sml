(* Original HOL word bitmap clauses, y19g.3. Run read-only from the prebuilt
   compiler/backend/semantics theory directory through regenerate.sh. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "length_zero" ``stackSem$bit_length (0w:word8)``;
val _ = print_eval "length_one" ``stackSem$bit_length (1w:word8)``;
val _ = print_eval "length_high" ``stackSem$bit_length (128w:word8)``;
val _ = print_eval "bitmap_empty" ``stackSem$read_bitmap ([]:word8 list)``;
val _ = print_eval "bitmap_zero" ``stackSem$read_bitmap ([0w]:word8 list)``;
val _ = print_eval "bitmap_one" ``stackSem$read_bitmap ([1w]:word8 list)``;
val _ = print_eval "bitmap_order" ``stackSem$read_bitmap ([13w]:word8 list)``;
val _ = print_eval "bitmap_trailing" ``stackSem$read_bitmap ([13w;255w]:word8 list)``;
val _ = print_eval "bitmap_missing_continuation" ``stackSem$read_bitmap ([128w]:word8 list)``;
val _ = print_eval "bitmap_continuation" ``stackSem$read_bitmap ([129w;5w]:word8 list)``;
val _ = print_eval "bitmap_width_one" ``stackSem$read_bitmap ([1w;0w]:word1 list)``;
