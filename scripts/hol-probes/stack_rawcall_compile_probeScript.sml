load "preamble"; load "stack_rawcallTheory";
open HolKernel Parse bossLib preamble stack_rawcallTheory;
val _ = Globals.linewidth := 1000000;
fun emit label tm = (print(label ^ "="); print_term(rconc(EVAL tm)));
val _ = emit "raw_compile_empty" ``compile ([]: (num # 64 stackLang$prog) list)``;
val _ = emit "raw_compile_forward" ``compile [(3,Loop(Seq(StackFree 4)(Call NONE (INL 7) NONE)));(7,Seq(StackAlloc 4)Skip):num # 64 stackLang$prog]``;
val _ = emit "raw_compile_duplicates" ``compile [(3,Loop(Seq(StackFree 4)(Call NONE (INL 7) NONE)));(7,Seq(StackAlloc 4)Skip);(7,StackAlloc 9);(7,Seq(StackAlloc 6)Skip):num # 64 stackLang$prog]``;
val _ = emit "raw_compile_bare" ``compile [(3,Loop(Seq(StackFree 4)(Call NONE (INL 7) NONE)));(7,StackAlloc 4):num # 64 stackLang$prog]``;
val _ = emit "raw_compile_zero_top" ``compile [(9,Seq(StackAlloc 0)Skip);(3,Seq(StackFree 0)(Call NONE (INL 9) NONE)):num # 64 stackLang$prog]``;
