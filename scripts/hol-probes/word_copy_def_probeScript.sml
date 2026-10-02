(* Original HOL word_copy (word_copyScript.sml:33-388): types and EVAL results of
   copy_prop and copy_prop_prog (program and final copy_state) on small 64-bit programs
   covering Move chains and overlap, every copy_prop_inst arith/mem/FP clause shape,
   Set/Get store equivalences, If merging, Loop reset, ShareInst, OpCurrHeap, buffer
   writes, StoreConsts/LocValue removal, and the Call/Alloc/Assign resets. *)
load "bossLib";
load "preamble";
load "word_copyTheory";
open bossLib HolKernel Parse preamble word_copyTheory;
val _ = Globals.linewidth := 4000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label term = (print (label ^ "="); print_type (type_of term); print "\n");
val _ = observe_type "wc_cp_type" ``word_copy$copy_prop``;
val _ = observe_type "wc_cpp_type" ``word_copy$copy_prop_prog``;
val _ = observe "wc_binop" ``copy_prop (Seq (Move 0 [(5,1)]) (Inst (Arith (Binop Add 9 1 (Reg 1)))) : 64 wordLang$prog)``;
val _ = observe "wc_binop_self" ``copy_prop (Seq (Move 0 [(5,1)]) (Inst (Arith (Binop Add 5 9 (Reg 1)))) : 64 wordLang$prog)``;
val _ = observe "wc_chain" ``copy_prop (Seq (Move 0 [(5,1)]) (Seq (Move 0 [(9,5)]) (Return 1 [1;5;9])) : 64 wordLang$prog)``;
val _ = observe "wc_chain_state" ``SND (copy_prop_prog (Seq (Move 0 [(5,1)]) (Move 0 [(9,5)]) : 64 wordLang$prog) empty_eq)``;
val _ = observe "wc_overlap" ``copy_prop_prog (Seq (Move 0 [(5,1);(1,5)]) (Return 1 [1]) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_multi" ``copy_prop_prog (Seq (Move 2 [(5,1);(9,13)]) (Raise 13) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_nonalloc" ``copy_prop_prog (Seq (Move 0 [(4,1)]) (Raise 1) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_const" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Inst (Const 1 3w)) (Return 1 [5])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_shift" ``copy_prop (Seq (Move 0 [(5,1)]) (Seq (Inst (Arith (Shift Lsl 9 1 (Reg 1)))) (Inst (Arith (Shift Asr 5 1 (Reg 1))))) : 64 wordLang$prog)``;
val _ = observe "wc_div" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Inst (Arith (Div 9 1 1))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_carry" ``copy_prop_prog (Seq (Move 0 [(5,1);(9,13)]) (Inst (Arith (AddCarry 5 1 13 17))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_carry_self" ``copy_prop (Seq (Move 0 [(5,1)]) (Inst (Arith (AddCarry 5 9 1 17))) : 64 wordLang$prog)``;
val _ = observe "wc_overflow" ``copy_prop (Seq (Move 0 [(5,1)]) (Seq (Inst (Arith (AddOverflow 9 1 1 17))) (Inst (Arith (SubOverflow 21 1 1 25)))) : 64 wordLang$prog)``;
val _ = observe "wc_longmul" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Inst (Arith (LongMul 9 13 1 1))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_longdiv" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Inst (Arith (LongDiv 9 13 1 1 1))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_mem" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Inst (Mem Load 9 (Addr 1 8w))) (Seq (Inst (Mem Store 1 (Addr 1 0w))) (Seq (Inst (Mem Load8 13 (Addr 1 1w))) (Seq (Inst (Mem Store8 1 (Addr 1 2w))) (Seq (Inst (Mem Load16 17 (Addr 1 3w))) (Seq (Inst (Mem Store16 1 (Addr 1 4w))) (Seq (Inst (Mem Load32 21 (Addr 1 5w))) (Inst (Mem Store32 1 (Addr 1 6w))))))))))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_mem_kill" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Inst (Mem Load 1 (Addr 1 8w))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_fp" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Inst (FP (FPLess 9 2 3))) (Seq (Inst (FP (FPMovFromReg 4 1 13))) (Seq (Inst (FP (FPMovFromReg 6 1 5))) (Seq (Inst (FP (FPAdd 7 8 9))) (Inst (FP (FPMovToReg 21 25 3)))))))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_fp_kill" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Inst (FP (FPEqual 1 2 3))) (Seq (Move 0 [(9,13)]) (Inst (FP (FPLessEqual 13 2 3))))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_skip_inst" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Inst Skip) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_set_get" ``copy_prop_prog (Seq (Set NextFree (Var 5)) (Get 9 NextFree) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_get_same" ``copy_prop_prog (Seq (Set NextFree (Var 5)) (Get 5 NextFree) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_get_none" ``copy_prop_prog (Get 9 (Temp 3w) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_set_class" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Set Handler (Var 1)) (Get 9 Handler)) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_set_nonalloc" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Set Handler (Var 2)) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_set_exp" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Set Handler (Const 2w)) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_if" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (If Equal 1 (Reg 1) (Move 0 [(9,5)]) (Seq (Move 0 [(9,5)]) (Move 0 [(13,1)]))) (Return 1 [1;9;13])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_if_imm" ``copy_prop_prog (Seq (Set NextFree (Var 5)) (If Less 5 (Imm 3w) (Get 9 NextFree) Skip) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_loop" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Loop LN (Seq (Move 0 [(9,13)]) (Seq (Raise 13) (Continue 0))) LN) (Return 1 [1]))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_mt" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (MustTerminate (Seq Tick (Seq (Break 2) (Raise 1)))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_share" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (ShareInst Load 9 (Op Add [Var 1; Const 4w])) (Seq (ShareInst Store 13 (Var 1)) (ShareInst Load8 17 (Op Sub [Var 1; Const 4w])))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_heap" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (OpCurrHeap Add 9 1) (Seq (OpCurrHeap Add 5 1) (Return 1 [1]))) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_buffers" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (CodeBufferWrite 1 1) (DataBufferWrite 1 9)) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_consts" ``copy_prop_prog (Seq (Move 0 [(5,1);(9,13)]) (Seq (StoreConsts 2 3 4 6 [(T,1w)]) (Seq (LocValue 7 3) (Return 1 [1;13])))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_consts_kill" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (StoreConsts 5 3 4 6 []) (Return 1 [1]))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_locvalue_kill" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (LocValue 1 3) (Return 1 [1]))  : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_call" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Call NONE (SOME 7) [1] NONE) (Return 1 [1])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_alloc" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Alloc 1 (LN,LN)) (Return 1 [1])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_assign" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Assign 9 (Var 1)) (Return 1 [1])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_store" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Store (Var 1) 1) (Return 1 [1])) : 64 wordLang$prog) empty_eq``;
val _ = observe "wc_install" ``copy_prop_prog (Seq (Move 0 [(5,1)]) (Seq (Install 2 3 4 6 (LN,LN)) (Raise 1)) : 64 wordLang$prog) empty_eq``;
