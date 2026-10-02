(* Original HOL word_unreach (word_unreachScript.sml:12-73): types and EVAL results of
   dest_Seq_Move, merge_moves, SimpSeq, Seq_assoc_right and remove_unreach on small
   64-bit programs, including the source's remove_unreach_test, transfers that drop their
   continuation, a Call without return continuation, and nested If/Loop/MustTerminate. *)
load "bossLib";
load "preamble";
load "word_unreachTheory";
open bossLib HolKernel Parse preamble word_unreachTheory;
val _ = Globals.linewidth := 4000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label term = (print (label ^ "="); print_type (type_of term); print "\n");
val _ = observe_type "wu_ru_type" ``word_unreach$remove_unreach``;
val _ = observe_type "wu_mm_type" ``word_unreach$merge_moves``;
val _ = observe "wu_dsm_move" ``dest_Seq_Move (Move 3 [(1,2)] : 64 wordLang$prog)``;
val _ = observe "wu_dsm_seq" ``dest_Seq_Move (Seq (Move 3 [(1,2)]) (Raise 5) : 64 wordLang$prog)``;
val _ = observe "wu_dsm_other" ``dest_Seq_Move (Seq (Raise 5) (Move 3 [(1,2)]) : 64 wordLang$prog)``;
val _ = observe "wu_mm_basic" ``merge_moves [(1,11);(2,22);(3,33)] [(3,1);(2,99)]``;
val _ = observe "wu_mm_dup" ``merge_moves [(1,2);(1,3)] [(4,1);(4,5)]``;
val _ = observe "wu_ss_skip_r" ``SimpSeq (Raise 1) (Skip : 64 wordLang$prog)``;
val _ = observe "wu_ss_skip_l" ``SimpSeq Skip (Raise 1 : 64 wordLang$prog)``;
val _ = observe "wu_ss_raise" ``SimpSeq (Raise 1) (Return 2 [3] : 64 wordLang$prog)``;
val _ = observe "wu_ss_move_move" ``SimpSeq (Move 1 [(1,11)]) (Move 4 [(2,1)] : 64 wordLang$prog)``;
val _ = observe "wu_ss_move_rest" ``SimpSeq (Move 1 [(1,11)]) (Seq (Move 0 [(2,1)]) (Raise 7) : 64 wordLang$prog)``;
val _ = observe "wu_ss_move_other" ``SimpSeq (Move 1 [(1,11)]) (Raise 7 : 64 wordLang$prog)``;
val _ = observe "wu_ss_default" ``SimpSeq Tick (Raise 7 : 64 wordLang$prog)``;
val _ = observe "wu_test" ``remove_unreach (Seq (Move 1 [(1,11);(2,22);(3,33)]) (Move 1 [(3,1);(2,99)]) : 64 wordLang$prog)``;
val _ = observe "wu_after_return" ``remove_unreach (Seq (Seq (Return 1 [2]) (Raise 3)) (Move 0 [(4,5)]) : 64 wordLang$prog)``;
val _ = observe "wu_call_none" ``remove_unreach (Seq (Call NONE (SOME 7) [1] NONE) (Raise 3) : 64 wordLang$prog)``;
val _ = observe "wu_call_ret" ``remove_unreach (Seq (Call (SOME ([1],(LN,LN),Seq Skip (Move 0 [(5,1)]),2,3)) (SOME 7) [1] (SOME (9,Seq (Raise 9) Tick,4,5))) Tick : 64 wordLang$prog)``;
val _ = observe "wu_if" ``remove_unreach (Seq (If Equal 1 (Imm 0w) (Seq Skip (Break 2)) (Seq (Move 0 [(5,1)]) Skip)) Tick : 64 wordLang$prog)``;
val _ = observe "wu_loop" ``remove_unreach (Seq (Loop LN (Seq (Continue 0) Tick) LN) (MustTerminate (Seq Tick Skip)) : 64 wordLang$prog)``;
