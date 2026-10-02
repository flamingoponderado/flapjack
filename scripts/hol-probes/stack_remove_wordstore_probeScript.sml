load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("ws_def=" ^ term_to_string (concl word_store_def) ^ "\n");
val _ = print ("ws_type=" ^ type_to_string (type_of ``stack_removeProof$word_store``) ^ "\n");
val _ = print ("ws_store_list=" ^ term_to_string (concl store_list_def) ^ "\n");
fun vector label term = print (label ^ "=" ^ term_to_string (rhs (concl (EVAL term))) ^ "\n");
fun check label q = let val th = prove (q,
  rpt gen_tac >> simp [word_store_def,store_list_def,finite_mapTheory.FLOOKUP_UPDATE] >> AP_TERM_TAC >> EVAL_TAC)
  in print (label ^ "=" ^ term_to_string (rhs (concl (EQT_INTRO th))) ^ "\n") end;
val _ = vector "ws_empty8" ``MAP (\name. case FLOOKUP (FEMPTY:store_name |-> 8 word_loc) name of NONE => Word 0w | SOME value => value) stack_remove$store_list``;
val _ = vector "ws_mixed8" ``MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:8 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list``;
val _ = vector "ws_mixed1" ``MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:1 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list``;
val _ = vector "ws_mixed80" ``MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:80 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list``;
val _ = check "ws_generic_empty" ``!base:'a word. word_store base (FEMPTY:store_name |-> 'b word_loc) = word_list_rev base (REPLICATE 48 (Word (0w:'b word)))``;
val _ = check "ws_independent64_8" ``word_store (0w:64 word) (FEMPTY |+ (NextFree,Word (255w:8 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) = word_list_rev 0w ([Word 255w;Word 0w;Word 0w;Loc 5 7;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 1w] ++ REPLICATE 30 (Word 0w) ++ [Loc 9 11])``;
val _ = check "ws_independent1_80" ``word_store (0w:1 word) (FEMPTY |+ (NextFree,Word (255w:80 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) = word_list_rev 0w ([Word 255w;Word 0w;Word 0w;Loc 5 7;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 1w] ++ REPLICATE 30 (Word 0w) ++ [Loc 9 11])``;
val _ = check "ws_independent80_1" ``word_store (0w:80 word) (FEMPTY |+ (NextFree,Word (255w:1 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) = word_list_rev 0w ([Word 255w;Word 0w;Word 0w;Loc 5 7;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 0w;Word 1w] ++ REPLICATE 30 (Word 0w) ++ [Loc 9 11])``;
val _ = check "ws_unlisted" ``!(base:'a word) (store:store_name |-> 'b word_loc) (value:'b word_loc). word_store base (store |+ (CurrHeap,value)) = word_store base store``;
val _ = check "ws_length" ``LENGTH (MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:8 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list) = 48``;
val _ = vector "ws_values8" ``MAP (\value. case value of Word w => SOME (w2n w) | Loc label offset => NONE) (MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:8 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list)``;
val _ = vector "ws_values1" ``MAP (\value. case value of Word w => SOME (w2n w) | Loc label offset => NONE) (MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:1 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list)``;
val _ = vector "ws_values80" ``MAP (\value. case value of Word w => SOME (w2n w) | Loc label offset => NONE) (MAP (\name. case FLOOKUP (FEMPTY |+ (NextFree,Word (255w:80 word)) |+ (OtherHeap,Loc 5 7) |+ (CurrHeap,Word 77w) |+ (Temp 0w,Word 1w) |+ (Temp 31w,Loc 9 11)) name of NONE => Word 0w | SOME value => value) stack_remove$store_list)``;
