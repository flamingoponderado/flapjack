load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;
fun out label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = out "nc_length" ``(<| bitmaps_length := 0; stack_frame_size := LN |> : word_to_stack$config).bitmaps_length = 0``;
val _ = out "nc_empty" ``(<| bitmaps_length := 0; stack_frame_size := LN |> : word_to_stack$config).stack_frame_size = LN``;
val _ = out "nc_single" ``(<| bitmaps_length := 17; stack_frame_size := LS 19 |> : word_to_stack$config).stack_frame_size = LS 19``;
val _ = out "nc_nonwf" ``(<| bitmaps_length := 3; stack_frame_size := BN LN LN |> : word_to_stack$config).stack_frame_size = BN LN LN``;
val _ = out "nc_raw" ``(<| bitmaps_length := 5; stack_frame_size := BS LN 7 (LS 9) |> : word_to_stack$config).stack_frame_size = BS LN 7 (LS 9)``;
val _ = out "nc_update_length" ``((<| bitmaps_length := 5; stack_frame_size := LS 9 |> : word_to_stack$config) with bitmaps_length := 11).stack_frame_size = LS 9``;
val _ = out "nc_update_tree" ``((<| bitmaps_length := 5; stack_frame_size := LS 9 |> : word_to_stack$config) with stack_frame_size := BN (LS 13) LN).bitmaps_length = 5``;
