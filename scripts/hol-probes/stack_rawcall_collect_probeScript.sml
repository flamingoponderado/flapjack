load "preamble"; load "stack_rawcallTheory";
open HolKernel Parse bossLib preamble stack_rawcallTheory;
val _ = Globals.linewidth := 1000000;
fun emit label tm = (print(label ^ "="); print_term(rconc(EVAL tm)));
val _ = emit "collect_bare_rejected" ``seq_stack_alloc (StackAlloc 4:64 stackLang$prog)``;
val _ = emit "collect_seq_zero" ``seq_stack_alloc (Seq (StackAlloc 0) Skip:64 stackLang$prog)``;
val _ = emit "collect_nested_rejected" ``seq_stack_alloc (Seq Skip (Seq (StackAlloc 4) Skip):64 stackLang$prog)``;
val _ = emit "collect_duplicates" ``MAP (\n. lookup n (collect_info [(7,Seq (StackAlloc 4) Skip);(7,StackAlloc 9);(7,Seq (StackAlloc 6) Skip);(9,Seq (StackAlloc 0) Skip):num # 64 stackLang$prog] (insert 3 8 LN))) [3;7;9;11]``;
