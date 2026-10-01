load "preamble";
load "word_to_stackProofTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory word_to_stackProofTheory stackPropsTheory stackLangTheory;
val _ = Globals.linewidth := 1000;
val push_source = GEN_ALL (prove (``  no_shmemop (PushHandler perf l1 l2 kff)``,
  PairCases_on ‘kff’
  >> Cases_on ‘perf’
  >> simp [PushHandler_def, list_Seq_def, no_shmemop_def]));
val _ = (print "hn_push_source=";print_thm push_source;print "\n");
val pop_source = GEN_ALL (prove (``  no_shmemop (PopHandler perf kff prog) ⇔
    no_shmemop prog``,
  PairCases_on ‘kff’
  >> Cases_on ‘perf’
  >> simp [PopHandler_def, no_shmemop_def]));
val _ = (print "hn_pop_source=";print_thm pop_source;print "\n");
val args_source = GEN_ALL (prove (``  no_shmemop (StackHandlerArgs perf dest arg_count kff)``,
  PairCases_on ‘kff’
  >> Cases_on ‘perf’
  >> simp [StackHandlerArgs_def, StackArgs_def,
           stack_move_no_shmemop_lem, no_shmemop_def]));
val _ = (print "hn_args_source=";print_thm args_source;print "\n");
fun typ label t = (print(label ^ "=");print_type(type_of t);print "\n");
val _ = typ "hn_push_type" ``PushHandler``;
val _ = typ "hn_pop_type" ``PopHandler``;
val _ = typ "hn_args_type" ``StackHandlerArgs``;
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val _ = out "hn_push_64_F" ``no_shmemop (PushHandler F 7 9 (2,T,"ignored") : 64 stackLang$prog)``;
val _ = out "hn_pop_64_F_safe" ``(no_shmemop (PopHandler F (2,T,"ignored") (Skip) : 64 stackLang$prog), no_shmemop (Skip:64 stackLang$prog))``;
val _ = out "hn_pop_64_F_forbidden" ``(no_shmemop (PopHandler F (2,T,"ignored") (ShMemOp Load 0 (Addr 1 0w)) : 64 stackLang$prog), no_shmemop (ShMemOp Load 0 (Addr 1 0w):64 stackLang$prog))``;
val _ = out "hn_push_64_T" ``no_shmemop (PushHandler T 7 9 (2,T,"ignored") : 64 stackLang$prog)``;
val _ = out "hn_pop_64_T_safe" ``(no_shmemop (PopHandler T (2,T,"ignored") (Skip) : 64 stackLang$prog), no_shmemop (Skip:64 stackLang$prog))``;
val _ = out "hn_pop_64_T_forbidden" ``(no_shmemop (PopHandler T (2,T,"ignored") (ShMemOp Load 0 (Addr 1 0w)) : 64 stackLang$prog), no_shmemop (ShMemOp Load 0 (Addr 1 0w):64 stackLang$prog))``;
val _ = out "hn_push_1_F" ``no_shmemop (PushHandler F 7 9 (0,[1;2;3],F) : 1 stackLang$prog)``;
val _ = out "hn_pop_1_F_safe" ``(no_shmemop (PopHandler F (0,[1;2;3],F) (Skip) : 1 stackLang$prog), no_shmemop (Skip:1 stackLang$prog))``;
val _ = out "hn_pop_1_F_forbidden" ``(no_shmemop (PopHandler F (0,[1;2;3],F) (ShMemOp Load 0 (Addr 1 0w)) : 1 stackLang$prog), no_shmemop (ShMemOp Load 0 (Addr 1 0w):1 stackLang$prog))``;
val _ = out "hn_push_1_T" ``no_shmemop (PushHandler T 7 9 (0,[1;2;3],F) : 1 stackLang$prog)``;
val _ = out "hn_pop_1_T_safe" ``(no_shmemop (PopHandler T (0,[1;2;3],F) (Skip) : 1 stackLang$prog), no_shmemop (Skip:1 stackLang$prog))``;
val _ = out "hn_pop_1_T_forbidden" ``(no_shmemop (PopHandler T (0,[1;2;3],F) (ShMemOp Load 0 (Addr 1 0w)) : 1 stackLang$prog), no_shmemop (ShMemOp Load 0 (Addr 1 0w):1 stackLang$prog))``;
val _ = out "hn_args_direct_zero" ``no_shmemop (StackHandlerArgs F (INL T:bool+unit) 0 (0,0,0) : 32 stackLang$prog)``;
val _ = out "hn_args_direct_perf" ``no_shmemop (StackHandlerArgs T (INL T:bool+unit) 7 (2,3,4) : 64 stackLang$prog)``;
val _ = out "hn_args_indirect_small" ``no_shmemop (StackHandlerArgs F (INR ():bool+unit) 9 (0,0,0) : 1 stackLang$prog)``;
val _ = out "hn_args_indirect_huge" ``no_shmemop (StackHandlerArgs T (INR ():bool+unit) 5 (0,1208925819614629174706176,1208925819614629174706179) : 80 stackLang$prog)``;
