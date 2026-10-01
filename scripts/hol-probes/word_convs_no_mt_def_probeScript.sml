load "preamble";
load "wordConvsTheory";
open bossLib HolKernel Parse preamble wordConvsTheory;
val clauses = CONJUNCTS no_mt_def;
val _ = if length clauses = 26 then () else raise Fail "wrong source clause count";
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
fun report label index lhs =
  let val select = fn t => if is_eq t then fst (dest_eq t) else t
      val th = PART_MATCH select (List.nth (clauses,index)) lhs
      val _ = if null (hyp th) andalso aconv (select (concl th)) lhs then ()
              else raise Fail "wrong original clause instance"
  in out label (pairSyntax.mk_pair (lhs,concl th)) end;
val _ = report "wcnm_01_mt" 0 ``wordConvs$no_mt (wordLang$MustTerminate (wordLang$MustTerminate wordLang$Skip) : 64 wordLang$prog)``;
val _ = report "wcnm_02_seq" 1 ``wordConvs$no_mt (wordLang$Seq (wordLang$MustTerminate wordLang$Skip) wordLang$Skip : 64 wordLang$prog)``;
val _ = report "wcnm_03_loop" 2 ``wordConvs$no_mt (wordLang$Loop LN (wordLang$MustTerminate wordLang$Skip) LN : 64 wordLang$prog)``;
val _ = report "wcnm_04_if" 3 ``wordConvs$no_mt (wordLang$If asm$Equal 2 (asm$Reg 3) (wordLang$MustTerminate wordLang$Skip) wordLang$Skip : 64 wordLang$prog)``;
val _ = report "wcnm_05_call" 4 ``wordConvs$no_mt (wordLang$Call NONE NONE [1;2] (SOME (7,wordLang$MustTerminate wordLang$Skip,8,9)) : 64 wordLang$prog)``;
val _ = report "wcnm_06_alloc" 5 ``wordConvs$no_mt (wordLang$Alloc 3 (LN,LN) : 64 wordLang$prog)``;
val _ = report "wcnm_07_loc" 6 ``wordConvs$no_mt (wordLang$LocValue 2 3 : 64 wordLang$prog)``;
val _ = report "wcnm_08_share" 7 ``wordConvs$no_mt (wordLang$ShareInst asm$Load 8 (wordLang$Var 9) : 64 wordLang$prog)``;
val _ = report "wcnm_09_install" 8 ``wordConvs$no_mt (wordLang$Install 1 2 3 4 (LN,LN) : 64 wordLang$prog)``;
val _ = report "wcnm_10_skip" 9 ``wordConvs$no_mt (wordLang$Skip : 64 wordLang$prog)``;
val _ = report "wcnm_11_move" 10 ``wordConvs$no_mt (wordLang$Move 5 [(1,2);(2,3)] : 64 wordLang$prog)``;
val _ = report "wcnm_12_inst" 11 ``wordConvs$no_mt (wordLang$Inst (asm$Const 2 7w) : 64 wordLang$prog)``;
val _ = report "wcnm_13_assign" 12 ``wordConvs$no_mt (wordLang$Assign 2 (wordLang$Const 7w) : 64 wordLang$prog)``;
val _ = report "wcnm_14_get" 13 ``wordConvs$no_mt (wordLang$Get 2 CurrHeap : 64 wordLang$prog)``;
val _ = report "wcnm_15_set" 14 ``wordConvs$no_mt (wordLang$Set CurrHeap (wordLang$Const 7w) : 64 wordLang$prog)``;
val _ = report "wcnm_16_store" 15 ``wordConvs$no_mt (wordLang$Store (wordLang$Var 2) 3 : 64 wordLang$prog)``;
val _ = report "wcnm_17_consts" 16 ``wordConvs$no_mt (wordLang$StoreConsts 2 3 4 5 [(T,7w);(F,8w)] : 64 wordLang$prog)``;
val _ = report "wcnm_18_raise" 17 ``wordConvs$no_mt (wordLang$Raise 3 : 64 wordLang$prog)``;
val _ = report "wcnm_19_return" 18 ``wordConvs$no_mt (wordLang$Return 4 [5;6] : 64 wordLang$prog)``;
val _ = report "wcnm_20_break" 19 ``wordConvs$no_mt (wordLang$Break 7 : 64 wordLang$prog)``;
val _ = report "wcnm_21_continue" 20 ``wordConvs$no_mt (wordLang$Continue 8 : 64 wordLang$prog)``;
val _ = report "wcnm_22_tick" 21 ``wordConvs$no_mt (wordLang$Tick : 64 wordLang$prog)``;
val _ = report "wcnm_23_heap" 22 ``wordConvs$no_mt (wordLang$OpCurrHeap asm$Add 2 3 : 64 wordLang$prog)``;
val _ = report "wcnm_24_code" 23 ``wordConvs$no_mt (wordLang$CodeBufferWrite 2 3 : 64 wordLang$prog)``;
val _ = report "wcnm_25_data" 24 ``wordConvs$no_mt (wordLang$DataBufferWrite 4 5 : 64 wordLang$prog)``;
val _ = report "wcnm_26_ffi" 25 ``wordConvs$no_mt (wordLang$FFI (mlstring$implode "io") 2 3 4 5 (LN,LN) : 64 wordLang$prog)``;
val _ = report "wcnm_call_none_none_width1" 4 ``wordConvs$no_mt (wordLang$Call NONE NONE [1;2] NONE : 1 wordLang$prog)``;
val _ = report "wcnm_call_return_only_width1" 4 ``wordConvs$no_mt (wordLang$Call (SOME ([1;2],(LN,LN),wordLang$MustTerminate wordLang$Skip,8,9)) NONE [1;2] NONE : 1 wordLang$prog)``;
val _ = report "wcnm_call_both_present_width1" 4 ``wordConvs$no_mt (wordLang$Call (SOME ([1;2],(LN,LN),wordLang$Skip,8,9)) NONE [1;2] (SOME (7,wordLang$MustTerminate wordLang$Skip,8,9)) : 1 wordLang$prog)``;
