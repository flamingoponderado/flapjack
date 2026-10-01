load "bossLib";
load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocTheory word_allocProofTheory;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun holds label term tac =
  (TAC_PROOF (([], term), tac); print (label ^ "="); print "T\n")
  handle HOL_ERR _ =>
    ((TAC_PROOF (([], mk_neg term), tac); print (label ^ "="); print "F\n")
     handle HOL_ERR _ => (print (label ^ "="); print "UNDECIDED\n"));
fun rd t = ``(\(p:64 wordLang$prog, l:num_set, n:store_name list). (p, MAP FST (toAList l), n)) (^t)``;
val L13 = ``insert 1 () (insert 3 () LN) : num_set``;
val _ = observe "rd_move_partial" (rd ``remove_dead (Move 0 [(1,2);(5,4)]:64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_move_dead" (rd ``remove_dead (Move 0 [(5,2)]:64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_inst_dead" (rd ``remove_dead (Inst (Const 5 3w):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_inst_live" (rd ``remove_dead (Inst (Arith (Binop Add 1 2 (Reg 4))):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_get_dead" (rd ``remove_dead (Get 5 NextFree:64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_get_live" (rd ``remove_dead (Get 3 NextFree:64 wordLang$prog) ^L13 [NextFree; EndOfHeap] []``);
val _ = observe "rd_curr_heap" (rd ``remove_dead (OpCurrHeap Add 3 7:64 wordLang$prog) ^L13 [CurrHeap; NextFree] []``);
val _ = observe "rd_locvalue_dead" (rd ``remove_dead (LocValue 6 9:64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_set_dead_store" (rd ``remove_dead (Set NextFree (Var 3):64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_set_live_store" (rd ``remove_dead (Set NextFree (Var 6):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_set_exp" (rd ``remove_dead (Set NextFree (Op Add [Var 6; Var 7]):64 wordLang$prog) ^L13 [EndOfHeap] []``);
val _ = observe "rd_seq_drop" (rd ``remove_dead (Seq (Inst (Const 5 3w)) (Move 0 [(1,2)]):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_seq_both" (rd ``remove_dead (Seq (Move 0 [(3,8)]) (Move 0 [(1,3)]):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_must" (rd ``remove_dead (MustTerminate (Inst (Const 5 3w)):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_if_dead" (rd ``remove_dead (If Equal 4 (Reg 8) (Inst (Const 5 3w)) (Inst (Const 6 3w)):64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_if_imm" (rd ``remove_dead (If Less 4 (Imm 2w) (Set NextFree (Var 9)) (Move 0 [(1,2)]):64 wordLang$prog) ^L13 [] []``);
val _ = observe "rd_call_ret" (rd ``remove_dead (Call (SOME ([2], (insert 7 () LN, LN), Inst (Const 5 3w), 1, 2)) (SOME 9) [4] (SOME (11, Move 0 [(5,6)], 3, 4)):64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_call_tail" (rd ``remove_dead (Call NONE (SOME 9) [4;2] NONE:64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_alloc" (rd ``remove_dead (Alloc 2 (LN, insert 8 () LN):64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_loop" (rd ``remove_dead (Loop (insert 2 () LN) (Seq (Inst (Const 5 3w)) (Move 0 [(2,2)])) (insert 9 () LN):64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_break" (rd ``remove_dead (Break 0:64 wordLang$prog) ^L13 [NextFree] [(insert 4 () LN, insert 7 () LN)]``);
val _ = observe "rd_continue_missing" (rd ``remove_dead (Continue 3:64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_catchall" (rd ``remove_dead (Tick:64 wordLang$prog) ^L13 [NextFree] []``);
val _ = observe "rd_prog" ``remove_dead_prog (Seq (Inst (Const 5 3w)) (Move 0 [(1,2)]):64 wordLang$prog)``;
val _ = holds "lsr_agree" ``live_store_rel [NextFree] (FEMPTY |+ (NextFree, Word (1w:64 word)) |+ (EndOfHeap, Word 2w)) (FEMPTY |+ (EndOfHeap, Word 2w))``
  (rw [live_store_rel_def, FLOOKUP_UPDATE] >> rw [] >> fs []);
val _ = holds "lsr_differ" ``live_store_rel [NextFree] (FEMPTY |+ (EndOfHeap, Word (1w:64 word))) (FEMPTY |+ (EndOfHeap, Word 2w))``
  (rw [live_store_rel_def, FLOOKUP_UPDATE] >> qexists_tac `EndOfHeap` >> EVAL_TAC);
