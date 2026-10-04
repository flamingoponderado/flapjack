load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "program_source_type="; print_type(type_of ``word_cse``); print "\n");
val _ = (print "program_source_definition="; print_thm word_cse_def; print "\n");
val _ = (print "program_wrapper_type="; print_type(type_of ``word_common_subexp_elim``); print "\n");
val _ = (print "program_wrapper_definition="; print_thm word_common_subexp_elim_def; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "program_seq" ``word_common_subexp_elim ((Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog) = ((Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Move 0 [(11,7)])) :64 prog)``;
val _ = out "state_seq" ``let (data,_) = word_cse empty_data ((Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_must" ``word_common_subexp_elim ((MustTerminate (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5)))))) :64 prog) = ((MustTerminate (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Move 0 [(11,7)]))) :64 prog)``;
val _ = out "state_must" ``let (data,_) = word_cse empty_data ((MustTerminate (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5)))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_if_same" ``word_common_subexp_elim ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 7 9 (Reg 5))))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog) = ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 7 9 (Reg 5))))) (Move 0 [(11,7)])) :64 prog)``;
val _ = out "state_if_same" ``let (data,_) = word_cse empty_data ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 7 9 (Reg 5))))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_if_different" ``word_common_subexp_elim ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Sub 7 9 (Reg 5))))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog) = ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Sub 7 9 (Reg 5))))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog)``;
val _ = out "state_if_different" ``let (data,_) = word_cse empty_data ((Seq (If Less 3 (Reg 5) (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Sub 7 9 (Reg 5))))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_loop" ``word_common_subexp_elim ((Seq (Loop (sptree$fromAList [(9,())]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) (sptree$fromAList [(11,())])) (Inst (Arith (Binop Add 13 9 (Reg 5))))) :64 prog) = ((Seq (Loop (sptree$fromAList [(9,())]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Move 0 [(11,7)])) (sptree$fromAList [(11,())])) (Inst (Arith (Binop Add 13 9 (Reg 5))))) :64 prog)``;
val _ = out "state_loop" ``let (data,_) = word_cse empty_data ((Seq (Loop (sptree$fromAList [(9,())]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))) (sptree$fromAList [(11,())])) (Inst (Arith (Binop Add 13 9 (Reg 5))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_move" ``word_common_subexp_elim ((Seq (Move 0 [(9,5)]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5)))))) :64 prog) = ((Seq (Move 0 [(9,5)]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Move 0 [(11,7)]))) :64 prog)``;
val _ = out "state_move" ``let (data,_) = word_cse empty_data ((Seq (Move 0 [(9,5)]) (Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5)))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_memory" ``word_common_subexp_elim ((Seq (Inst (Mem Load 7 (Addr 9 0w))) (Inst (Mem Load 11 (Addr 9 0w)))) :64 prog) = ((Seq (Inst (Mem Load 7 (Addr 9 0w))) (Move 0 [(11,7)])) :64 prog)``;
val _ = out "state_memory" ``let (data,_) = word_cse empty_data ((Seq (Inst (Mem Load 7 (Addr 9 0w))) (Inst (Mem Load 11 (Addr 9 0w)))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_heap" ``word_common_subexp_elim ((Seq (OpCurrHeap Add 7 9) (OpCurrHeap Add 11 9)) :64 prog) = ((Seq (OpCurrHeap Add 7 9) (Move 0 [(11,7)])) :64 prog)``;
val _ = out "state_heap" ``let (data,_) = word_cse empty_data ((Seq (OpCurrHeap Add 7 9) (OpCurrHeap Add 11 9)) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_assign" ``word_common_subexp_elim ((Seq (Assign 7 (Load (Op Add [Var 9;Const 0w]))) (Assign 7 (Load (Op Add [Var 9;Const 0w])))) :64 prog) = ((Seq (Assign 7 (Load (Op Add [Var 9;Const 0w]))) (Assign 7 (Load (Op Add [Var 9;Const 0w])))) :64 prog)``;
val _ = out "state_assign" ``let (data,_) = word_cse empty_data ((Seq (Assign 7 (Load (Op Add [Var 9;Const 0w]))) (Assign 7 (Load (Op Add [Var 9;Const 0w])))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_get_set" ``word_common_subexp_elim ((Seq (Get 9 HeapLength) (Seq (Get 11 HeapLength) (Seq (Set CurrHeap (Var 3)) (Get 13 HeapLength)))) :64 prog) = ((Seq (Get 9 HeapLength) (Seq (Move 1 [(11,9)]) (Seq (Set CurrHeap (Var 3)) (Get 13 HeapLength)))) :64 prog)``;
val _ = out "state_get_set" ``let (data,_) = word_cse empty_data ((Seq (Get 9 HeapLength) (Seq (Get 11 HeapLength) (Seq (Set CurrHeap (Var 3)) (Get 13 HeapLength)))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_call_0_0" ``word_common_subexp_elim ((Call (NONE) (SOME 9) [9;5] (NONE)) :64 prog) = ((Call (NONE) (SOME 9) [9;5] (NONE)) :64 prog)``;
val _ = out "state_call_0_0" ``let (data,_) = word_cse empty_data ((Call (NONE) (SOME 9) [9;5] (NONE)) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_call_0_1" ``word_common_subexp_elim ((Call (NONE) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog) = ((Call (NONE) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog)``;
val _ = out "state_call_0_1" ``let (data,_) = word_cse empty_data ((Call (NONE) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_call_1_0" ``word_common_subexp_elim ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (NONE)) :64 prog) = ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (NONE)) :64 prog)``;
val _ = out "state_call_1_0" ``let (data,_) = word_cse empty_data ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (NONE)) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_call_1_1" ``word_common_subexp_elim ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog) = ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog)``;
val _ = out "state_call_1_1" ``let (data,_) = word_cse empty_data ((Call (SOME ([7],(sptree$fromAList [(9,())],sptree$fromAList [(11,())]),(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),1,2)) (SOME 9) [9;5] (SOME (5,(Seq (Inst (Arith (Binop Add 7 9 (Reg 5)))) (Inst (Arith (Binop Add 11 9 (Reg 5))))),3,4))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
val _ = out "program_flat_controls" ``word_common_subexp_elim ((Seq Skip (Seq (Store (Var 9) 5) (Seq (Raise 9) (Seq (Return 5 [9;7]) (Seq Tick (Seq (Alloc 7 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (Install 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (CodeBufferWrite 3 5) (Seq (DataBufferWrite 7 9) (Seq (FFI (strlit "x") 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (StoreConsts 3 5 7 9 [(T,1w);(F,2w)]) (Seq (ShareInst Load 7 (Var 9)) (Seq (ShareInst Store 5 (Var 9)) (Seq (Break 1) (Continue 2))))))))))))))) :64 prog) = ((Seq Skip (Seq (Store (Var 9) 5) (Seq (Raise 9) (Seq (Return 5 [9;7]) (Seq Tick (Seq (Alloc 7 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (Install 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (CodeBufferWrite 3 5) (Seq (DataBufferWrite 7 9) (Seq (FFI (strlit "x") 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (StoreConsts 3 5 7 9 [(T,1w);(F,2w)]) (Seq (ShareInst Load 7 (Var 9)) (Seq (ShareInst Store 5 (Var 9)) (Seq (Break 1) (Continue 2))))))))))))))) :64 prog)``;
val _ = out "state_flat_controls" ``let (data,_) = word_cse empty_data ((Seq Skip (Seq (Store (Var 9) 5) (Seq (Raise 9) (Seq (Return 5 [9;7]) (Seq Tick (Seq (Alloc 7 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (Install 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (CodeBufferWrite 3 5) (Seq (DataBufferWrite 7 9) (Seq (FFI (strlit "x") 3 5 7 9 (sptree$fromAList [(9,())],sptree$fromAList [(11,())])) (Seq (StoreConsts 3 5 7 9 [(T,1w);(F,2w)]) (Seq (ShareInst Load 7 (Var 9)) (Seq (ShareInst Store 5 (Var 9)) (Seq (Break 1) (Continue 2))))))))))))))) :64 prog)
  in (MAP (\k. sptree$lookup k data.to_canonical) [3;5;7;9;11;13],
      MAP (\k. sptree$lookup k data.to_latest) [3;5;7;9;11;13],
      MAP (ALOOKUP data.gets_mem) [CurrHeap;HeapLength],
      MAP (\k. balanced_map$lookup listCmp k data.instrs_mem)
        [instToNumList (Arith (Binop Add 0 9 (Reg 5)):64 inst);
         instToNumList (Arith (Binop Add 0 5 (Reg 5)):64 inst);OpCurrHeapToNumList Add 9],
      MAP (\k. balanced_map$lookup listCmp k data.loads_mem) [loadToNumList Load 9 (0w:64 word)],
      sptree$size data.to_canonical,sptree$size data.to_latest,LENGTH data.gets_mem,
      balanced_map$size data.instrs_mem,balanced_map$size data.loads_mem)``;
