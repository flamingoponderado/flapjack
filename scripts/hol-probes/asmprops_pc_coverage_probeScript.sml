(* Direct original asmProps all_pcs boundary observations. *)
load "bossLib";
load "preamble";
load "asmPropsTheory";
open bossLib HolKernel Parse preamble asmPropsTheory;
fun print_eval label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "pcs_empty" ``MAP (\x. (n2w x : 8 word) IN all_pcs 0 (254w:8 word) 0) [254;255;0]``;
val _ = print_eval "pcs_byte_wrap" ``MAP (\x. (n2w x : 8 word) IN all_pcs 4 (254w:8 word) 0) [253;254;255;0;1;2]``;
val _ = print_eval "pcs_stride_short" ``MAP (\x. (n2w x : 8 word) IN all_pcs 3 (254w:8 word) 2) [254;2;6]``;
val _ = print_eval "pcs_stride_exact" ``MAP (\x. (n2w x : 8 word) IN all_pcs 4 (254w:8 word) 2) [254;2;6]``;
val _ = print_eval "pcs_stride_tail" ``MAP (\x. (n2w x : 8 word) IN all_pcs 5 (254w:8 word) 2) [254;2;6]``;
val _ = print_eval "pcs_stride_twice" ``MAP (\x. (n2w x : 8 word) IN all_pcs 8 (254w:8 word) 2) [254;2;6]``;
val _ = print_eval "pcs_stride_extra" ``MAP (\x. (n2w x : 8 word) IN all_pcs 9 (254w:8 word) 2) [254;2;6;10]``;
val _ = print_eval "pcs_dimension_stride" ``MAP (\x. (n2w x : 8 word) IN all_pcs 513 (7w:8 word) 8) [7;8;0]``;
val _ = print_eval "pcs_large_stride" ``MAP (\x. (n2w x : 8 word) IN all_pcs 3 (7w:8 word) 12) [7;8;0]``;
val _ = print_eval "pcs_width1_duplicates" ``MAP (\x. (n2w x : 1 word) IN all_pcs 5 (1w:1 word) 0) [0;1]``;
val _ = print_eval "pcs_width1_stride" ``MAP (\x. (n2w x : 1 word) IN all_pcs 5 (1w:1 word) 1) [0;1]``;
val _ = print_eval "pcs_width32_wrap" ``MAP (\x. (n2w x : 32 word) IN all_pcs 17 (4294967288w:32 word) 4) [4294967288;8;24]``;
val _ = print_eval "pcs_width64_wrap" ``MAP (\x. (n2w x : 64 word) IN all_pcs 17 (18446744073709551608w:64 word) 4) [18446744073709551608;8;24]``;
