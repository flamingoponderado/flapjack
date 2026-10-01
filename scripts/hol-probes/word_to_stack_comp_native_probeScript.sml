(* Direct original comp_def453-555 observations, read-only prebuilt theory.
   These rows support NativeCompile regression review, not cross-prover equivalence. *)
load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;
fun out label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = out "comp_skip" ``comp (c:64 asm$asm_config) F wordLang$Skip (List [4w],1) (4,0,0) = (stackLang$Skip,(List [4w],1))``;
val _ = out "comp_must" ``comp (c:64 asm$asm_config) F (wordLang$MustTerminate Tick) (List [4w],1) (4,0,0) = (stackLang$Tick,(List [4w],1))``;
val _ = out "comp_seq" ``comp (c:64 asm$asm_config) F (wordLang$Seq Skip Tick) (List [4w],1) (4,0,0) = (stackLang$Seq Skip Tick,(List [4w],1))``;
val _ = out "comp_loop" ``comp (c:64 asm$asm_config) F (wordLang$Loop LN Tick LN) (List [4w],1) (4,0,0) = (stackLang$Loop Tick,(List [4w],1))``;
val _ = out "comp_return" ``comp (c:64 asm$asm_config) F (wordLang$Return 0 []) (List [4w],1) (4,0,0) = (stackLang$Return 0,(List [4w],1))``;
val _ = out "comp_raise" ``comp (c:64 asm$asm_config) F (wordLang$Raise 77) (List [4w],1) (4,0,0) = (stackLang$Call NONE (INL raise_stub_location) NONE,(List [4w],1))``;
val _ = out "comp_set_bitmap" ``comp (c:64 asm$asm_config) F (wordLang$Set BitmapBase (Var 0)) (List [4w],1) (4,0,0) = (stackLang$Skip,(List [4w],1))``;
val _ = out "comp_set_bad" ``comp (c:64 asm$asm_config) F (wordLang$Set CurrHeap (Const 9w)) (List [4w],1) (4,0,0) = (stackLang$Skip,(List [4w],1))``;
val _ = out "comp_assign_fallback" ``comp (c:64 asm$asm_config) F (wordLang$Assign 1 (Const 9w)) (List [4w],1) (4,0,0) = (stackLang$Skip,(List [4w],1))``;
val _ = out "comp_install" ``comp (c:64 asm$asm_config) F (wordLang$Install 2 4 4 6 (LN,LN)) (List [4w],1) (4,0,0) = (stackLang$Install 1 2 2 3 0,(List [4w],1))``;
val _ = out "comp_tailcall" ``comp (c:64 asm$asm_config) F (wordLang$Call NONE (SOME 9) [] NONE) (List [4w],1) (4,0,0) = (stackLang$Seq Skip (Call NONE (INL 9) NONE),(List [4w],1))``;
val _ = out "comp_share_bad" ``comp (c:64 asm$asm_config) F (wordLang$ShareInst Load 0 (Const 9w)) (List [4w],1) (4,0,0) = (stackLang$Skip,(List [4w],1))``;
val _ = out "comp_if_valid" ``comp ((c:64 asm$asm_config) with valid_imm := (\op w. T)) F (wordLang$If Equal 0 (Imm 9w) Tick Skip) (List [4w],1) (4,0,0) = (stackLang$If Equal 0 (Imm 9w) Tick Skip,(List [4w],1))``;
val _ = out "comp_if_materialize" ``comp ((c:64 asm$asm_config) with valid_imm := (\op w. F)) F (wordLang$If Equal 0 (Imm 9w) Tick Skip) (List [4w],1) (4,0,0) = (stackLang$Seq (Inst (Const 5 9w)) (If Equal 0 (Reg 5) Tick Skip),(List [4w],1))``;
val _ = out "comp_returning" ``comp (c:64 asm$asm_config) F (wordLang$Call (SOME ([],(LN,LN),Tick,7,8)) (SOME 9) [] NONE) (List [4w],1) (4,0,0) = (stackLang$Seq Skip (Seq Skip (Seq (StackAlloc 0) (Seq Skip (Call (SOME (Seq Skip Tick,0,7,8)) (INL 9) NONE)))),(List [4w],1))``;
val _ = out "comp_handler" ``comp (c:64 asm$asm_config) F (wordLang$Call (SOME ([],(LN,LN),Tick,7,8)) (SOME 9) [] (SOME (99,Seq Tick Skip,11,12))) (List [4w],1) (4,0,0) = (stackLang$Seq Skip (Seq Skip (Seq (PushHandler F 11 12 (4,0,0)) (Seq (StackHandlerArgs F (INL 9:num+num) 1 (4,0,0)) (Seq Skip (Call (SOME (Seq Skip (PopHandler F (4,0,0) Tick),0,7,8)) (INL 9) (SOME (Seq Tick Skip,11,12))))))),(List [4w],1))``;
val _ = out "comp_seq_bitmaps" ``SND(SND(comp (c:64 asm$asm_config) F (wordLang$Seq (Alloc 0 (LN,LN)) (Alloc 0 (LN,LN))) (List [4w],1) (4,1,2))) = 3``;
val _ = out "comp_if_bitmaps" ``SND(SND(comp ((c:64 asm$asm_config) with valid_imm := (\op w. T)) F (wordLang$If Equal 0 (Imm 9w) (Alloc 0 (LN,LN)) (Alloc 0 (LN,LN))) (List [4w],1) (4,1,2))) = 3``;
val _ = out "comp_call_bitmaps" ``SND(SND(comp (c:64 asm$asm_config) F (wordLang$Call (SOME ([],(LN,LN),Alloc 0 (LN,LN),7,8)) (SOME 9) [] (SOME (99,Alloc 0 (LN,LN),11,12))) (List [4w],1) (4,1,2))) = 4``;
