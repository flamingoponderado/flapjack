(* Original word_alloc ssa_cc_trans over representative 64-bit programs: every
   clause family (Move/force_rename, StoreConsts, Inst, Assign, Get, Store, Seq,
   MustTerminate, If/fix_inconsistencies, Alloc, Raise, OpCurrHeap, Return,
   Tick, Set, LocValue, Install, buffer writes, FFI, Call with and without
   returns/handler, ShareInst, Loop/Break/Continue). CakeML remains read-only;
   sparse trees print raw. *)
load "bossLib";
load "wordsLib";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib word_allocTheory;
val _ = Globals.linewidth := 3000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val m = ``insert 2 10 (insert 3 11 (insert 4 12 LN)) : num num_map``;
val _ = observe "sc_skip" ``ssa_cc_trans ((Skip) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_move" ``ssa_cc_trans ((Move 1 [(2,3);(5,2)]) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_storeconsts" ``ssa_cc_trans ((StoreConsts 0 0 2 3 [(T,7w)]) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_inst" ``ssa_cc_trans ((Inst (Const 2 5w)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_assign" ``ssa_cc_trans ((Assign 3 (Op Add [Var 2; Var 4])) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_get" ``ssa_cc_trans ((Get 2 NextFree) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_store" ``ssa_cc_trans ((Store (Var 3) 4) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_seq" ``ssa_cc_trans ((Seq (Assign 3 (Var 2)) (Assign 2 (Var 3))) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_mustterminate" ``ssa_cc_trans ((MustTerminate (Assign 3 (Var 2))) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_if" ``ssa_cc_trans ((If Equal 2 (Reg 3) (Assign 3 (Var 2)) (Assign 5 (Var 4))) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_if_skip" ``ssa_cc_trans ((If Less 2 (Imm 1w) Skip (Assign 3 (Var 4))) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_alloc" ``ssa_cc_trans ((Alloc 3 ((insert 2 () LN, insert 4 () LN) : num_set # num_set)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_raise" ``ssa_cc_trans ((Raise 3) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_opcurrheap" ``ssa_cc_trans ((OpCurrHeap Add 5 3) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_return" ``ssa_cc_trans ((Return 2 [3;4]) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_tick" ``ssa_cc_trans ((Tick) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_set" ``ssa_cc_trans ((Set NextFree (Var 3)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_locvalue" ``ssa_cc_trans ((LocValue 3 9) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_install" ``ssa_cc_trans ((Install 2 3 4 9 ((insert 2 () LN, insert 4 () LN) : num_set # num_set)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_codebufferwrite" ``ssa_cc_trans ((CodeBufferWrite 2 3) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_databufferwrite" ``ssa_cc_trans ((DataBufferWrite 4 9) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_ffi" ``ssa_cc_trans ((FFI (strlit "f") 2 3 4 9 ((insert 2 () LN, insert 4 () LN) : num_set # num_set)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_call_tail" ``ssa_cc_trans ((Call NONE (SOME 7) [3;2] NONE) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_call_ret" ``ssa_cc_trans ((Call (SOME ([5], ((insert 2 () LN, insert 4 () LN) : num_set # num_set), Assign 3 (Var 5), 7, 8)) (SOME 7) [3] NONE) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_call_handler" ``ssa_cc_trans ((Call (SOME ([5], ((insert 2 () LN, insert 4 () LN) : num_set # num_set), Assign 3 (Var 5), 7, 8)) (SOME 7) [3] (SOME (9, Assign 4 (Var 9), 7, 9))) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_shareinst_load" ``ssa_cc_trans ((ShareInst Load 3 (Var 2)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_shareinst_store" ``ssa_cc_trans ((ShareInst Store 3 (Var 2)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_loop" ``ssa_cc_trans ((Loop (insert 2 () LN) (Seq (Assign 2 (Var 2)) (Continue 0)) (insert 3 () LN)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_loop_break" ``ssa_cc_trans ((Loop (insert 2 () (insert 9 () LN)) (Seq (Assign 3 (Var 2)) (Break 0)) (insert 3 () LN)) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_break_free" ``ssa_cc_trans ((Break 4) : 64 wordLang$prog) ^m 21 []``;
val _ = observe "sc_continue_free" ``ssa_cc_trans ((Continue 0) : 64 wordLang$prog) ^m 21 []``;
