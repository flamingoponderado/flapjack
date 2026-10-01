(* DIRECT original generic ASM assertions; no translated evaluator. *)
load "bossLib";
load "preamble";
load "asmPropsTheory";
open bossLib HolKernel Parse preamble asmPropsTheory;
val _ = computeLib.add_funs [asserts_eval, asserts2_def];
fun print_eval label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "assert_zero_skip_p" ``asserts 0 (\k s:num. s+k+1) 0 (\s. F) (\s. s=1)``;
val _ = print_eval "assert_zero_runs_next" ``asserts 0 (\k s:num. s+k+1) 0 (\s. T) (\s. s=0)``;
val _ = print_eval "assert_order_ok" ``asserts 3 (\k s:num. 10*s+k) 1 (\s. s<=1321) (\s. s=13210)``;
val _ = print_eval "assert_order_bad" ``asserts 3 (\k s:num. 10*s+k) 1 (\s. s<1321) (\s. s=13210)``;
val _ = print_eval "assert_count_fold" ``FOLDR (\k s:num. 10*s+k) 13 (COUNT_LIST 3)``;
val _ = print_eval "assert_prefixes" ``MAP (\k. FOLDR (\i s:num. 10*s+i) 1 (REVERSE (GENLIST ((-) 3) (SUC k)))) [0;1;2]``;
val _ = print_eval "assert_weaken_bound" ``asserts 3 (\k s:num. if k<=3 then 10*s+k else 0) 1 (\s. s<=2000) (\s. s=13210)``;
val _ = print_eval "assert_state_bool" ``asserts 2 (\k s:bool. ~s) T (\s. T) (\s. s=F)``;
val _ = print_eval "assert2_zero" ``asserts2 0 (\k b:bool. if b then k else k+10) (\s:num. EVEN s) 0 (\s b. F)``;
val _ = print_eval "assert2_mixed_ok" ``asserts2 2 (\k b:bool. if b then k else k+10) (\s:num. EVEN s) 0 (\s b. b=EVEN s)``;
val _ = print_eval "assert2_mixed_bad" ``asserts2 2 (\k b:bool. if b then k else k+10) (\s:num. EVEN s) 0 (\s b. s<2)``;
val _ = print_eval "assert2_changed_above" ``asserts2 2 (\k b:bool. if k<=2 then (if b then k else k+10) else 99) (\s:num. EVEN s) 0 (\s b. b=EVEN s)``;
val _ = print_eval "assert2_first_pair" ``(0:num, EVEN 0)``;
val _ = print_eval "assert2_constant_ok" ``asserts2 4 (\k b:bool. if b then 1 else 2) (\s:num. EVEN s) 0 (\s b. b=EVEN s)``;
val _ = print_eval "assert2_every_pairs" ``MAP (\j. let s = FUNPOW ((\b:bool. if b then 1 else 2) o (\s:num. EVEN s)) j 0 in (s,EVEN s)) [0;1;2;3]``;
val _ = print_eval "assert2_first_bad" ``asserts2 1 (\k b:bool. if b then k else k+10) (\s:num. EVEN s) 0 (\s b. ~b)``;
