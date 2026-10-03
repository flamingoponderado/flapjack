load "preamble"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble stackPropsTheory stackSemTheory sptreeTheory;
val _ = Globals.linewidth := 1000000;
val full = GEN_ALL (prove(concl evaluate_mono,
  rw[] \\
  imp_res_tac evaluate_code_bitmaps \\
  rw[] \\
  irule subspt_FOLDL_union));
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = (print "mono_full_statement="; print_term(concl full));
val _ = print("mono_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
fun row label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))));
val _ = row "mono_union_overlap" ``lookup 0 (union (fromAList [(0,11:num)]) (fromAList [(0,22:num);(1,33)]))``;
val _ = row "mono_union_fresh" ``lookup 1 (union (fromAList [(0,11:num)]) (fromAList [(0,22:num);(1,33)]))``;
val _ = row "mono_prefix_append" ``isPREFIX ([255w;0w]:word8 list) [255w;0w;1w]``;
val _ = row "mono_prefix_truncate" ``isPREFIX ([255w;0w]:word8 list) [255w]``;
