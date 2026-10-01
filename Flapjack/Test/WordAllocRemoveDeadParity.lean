import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
namespace Flapjack.Test.WordAllocRemoveDeadParity
open Flapjack Flapjack.WordAlloc

/-! Kernel replay of `scripts/hol-probes/word_alloc_remove_dead_probe.out`: original HOL
`remove_dead` rows observed as (program, `toAList` keys of the live set, dead stores),
`remove_dead_prog`, and two `live_store_rel` instances. HOL prints `Move 0` as `Move0`
and a singleton `num_set` as `⦕ n ⦖`. -/

abbrev P := WordLangProgHOL (BitVec 64)
private def obs (r : P × NumSet × List WordStoreHOL) : P × List Nat × List WordStoreHOL :=
  (r.1, (sptToAList r.2.1).map Prod.fst, r.2.2)
private def L13 : NumSet := sptInsert 1 () (sptInsert 3 () .ln)
private def s2 : NumSet := sptInsert 2 () .ln
private def s4 : NumSet := sptInsert 4 () .ln
private def s7 : NumSet := sptInsert 7 () .ln
private def s8 : NumSet := sptInsert 8 () .ln
private def s9 : NumSet := sptInsert 9 () .ln

-- rd_move_partial=(Move0 [(1,2)],[3; 2],[])
example : obs (removeDead (.move 0 [(1, 2), (5, 4)] : P) L13 [] []) =
    (.move 0 [(1, 2)], [3, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, numsetListInsert, sptMkBN]
-- rd_move_dead=(Skip,[3; 1],[NextFree])
example : obs (removeDead (.move 0 [(5, 2)] : P) L13 [.nextFree] []) =
    (.skip, [3, 1], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- rd_inst_dead=(Skip,[3; 1],[])
example : obs (removeDead (.inst (.const 5 3) : P) L13 [] []) =
    (.skip, [3, 1], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, removeDeadInst, removeDeadInstCore]
-- rd_inst_live=(Inst (Arith (Binop Add 1 2 (Reg 4))),[3; 4; 2],[])
example : obs (removeDead (.inst (.arith (.binop .add 1 2 (.reg 4))) : P) L13 [] []) =
    (.inst (.arith (.binop .add 1 2 (.reg 4))), [3, 4, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, sptMkBN, getLiveInst, getLiveInstCore, removeDeadInst, removeDeadInstCore]
-- rd_get_dead=(Skip,[3; 1],[NextFree])
example : obs (removeDead (.get 5 .nextFree : P) L13 [.nextFree] []) =
    (.skip, [3, 1], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- rd_get_live=(Get 3 NextFree,[1],[EndOfHeap])
example : obs (removeDead (.get 3 .nextFree : P) L13 [.nextFree, .endOfHeap] []) =
    (.get 3 .nextFree, [1], [.endOfHeap]) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, sptMkBN, sptMkBS]
-- rd_curr_heap=(OpCurrHeap Add 3 7,[7; 1],[NextFree])
example : obs (removeDead (.opCurrHeap .add 3 7 : P) L13 [.currHeap, .nextFree] []) =
    (.opCurrHeap .add 3 7, [7, 1], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, sptMkBN, sptMkBS]
-- rd_locvalue_dead=(Skip,[3; 1],[])
example : obs (removeDead (.locValue 6 9 : P) L13 [] []) =
    (.skip, [3, 1], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- rd_set_dead_store=(Skip,[3; 1],[NextFree])
example : obs (removeDead (.set .nextFree (.var 3) : P) L13 [.nextFree] []) =
    (.skip, [3, 1], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext]
-- rd_set_live_store=(Set NextFree (Var 6),[3; 1; 6],[NextFree])
example : obs (removeDead (.set .nextFree (.var 6) : P) L13 [] []) =
    (.set .nextFree (.var 6), [3, 1, 6], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext]
-- rd_set_exp=(Set NextFree (Op Add [Var 6; Var 7]),[7; 3; 1; 6],[])
example : obs (removeDead (.set .nextFree (.op .add [.var 6, .var 7]) : P) L13 [.endOfHeap] []) =
    (.set .nextFree (.op .add [.var 6, .var 7]), [7, 3, 1, 6], []) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext, sptUnion, bigUnion, getLive, getLiveExp]
-- rd_seq_drop=(Move0 [(1,2)],[3; 2],[])
example : obs (removeDead (.seq (.inst (.const 5 3)) (.move 0 [(1, 2)]) : P) L13 [] []) =
    (.move 0 [(1, 2)], [3, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, numsetListInsert, sptMkBN, removeDeadInst, removeDeadInstCore]
-- rd_seq_both=(Seq (Move0 [(3,8)]) (Move0 [(1,3)]),[8],[])
example : obs (removeDead (.seq (.move 0 [(3, 8)]) (.move 0 [(1, 3)]) : P) L13 [] []) =
    (.seq (.move 0 [(3, 8)]) (.move 0 [(1, 3)]), [8], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, numsetListInsert, sptMkBN]
-- rd_must=(MustTerminate Skip,[3; 1],[])
example : obs (removeDead (.mustTerminate (.inst (.const 5 3)) : P) L13 [] []) =
    (.mustTerminate .skip, [3, 1], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, removeDeadInst, removeDeadInstCore]
-- rd_if_dead=(Skip,[3; 1; 8; 4],[NextFree])
example : obs (removeDead (.ite .equal 4 (.reg 8) (.inst (.const 5 3)) (.inst (.const 6 3)) : P) L13 [.nextFree] []) =
    (.skip, [3, 1, 8, 4], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptUnion, removeDeadInst, removeDeadInstCore]
-- rd_if_imm=(If Less 4 (Imm 2w) (Set NextFree (Var 9)) (Move0 [(1,2)]),[3; 1; 9; 4; 2],[])
example : obs (removeDead (.ite .less 4 (.imm 2) (.set .nextFree (.var 9)) (.move 0 [(1, 2)]) : P) L13 [] []) =
    (.ite .less 4 (.imm 2) (.set .nextFree (.var 9)) (.move 0 [(1, 2)]), [3, 1, 9, 4, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, numsetListInsert, sptMkBN, sptUnion]
-- rd_call_ret=(Call (SOME ([2],(⦕ 7 ⦖,LN),Skip,1,2)) (SOME 9) [4] (SOME (11,Skip,3,4)), [7; 4],[])
example : obs (removeDead (.call (some ([2], (s7, .ln), .inst (.const 5 3), 1, 2)) (some 9) [4] (some (11, .move 0 [(5, 6)], 3, 4)) : P) L13 [.nextFree] []) =
    (.call (some ([2], (s7, .ln), .skip, 1, 2)) (some 9) [4] (some (11, .skip, 3, 4)), [7, 4], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, numsetListInsert, sptUnion, removeDeadInst, removeDeadInstCore, s7]
-- rd_call_tail=(Call NONE (SOME 9) [4; 2] NONE,[4; 2],[])
example : obs (removeDead (.call none (some 9) [4, 2] none : P) L13 [.nextFree] []) =
    (.call none (some 9) [4, 2] none, [4, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext, numsetListInsert, getLive]
-- rd_alloc=(Alloc 2 (LN,⦕ 8 ⦖),[8; 2],[])
example : obs (removeDead (.alloc 2 (.ln, s8) : P) L13 [.nextFree] []) =
    (.alloc 2 (.ln, s8), [8, 2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext, sptUnion, getLive, s8]
-- rd_loop=(Loop ⦕ 2 ⦖ (Move0 [(2,2)]) ⦕ 9 ⦖,[2],[])
example : obs (removeDead (.loop s2 (.seq (.inst (.const 5 3)) (.move 0 [(2, 2)])) s9 : P) L13 [.nextFree] []) =
    (.loop s2 (.move 0 [(2, 2)]) s9, [2], []) := by
  simp [obs, removeDead, L13, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext, sptDelete, numsetListInsert, sptMkBN, removeDeadInst, removeDeadInstCore, s2, s9]
-- rd_break=(Break 0,[7],[])
example : obs (removeDead (.break 0 : P) L13 [.nextFree] [(s4, s7)]) =
    (.break 0, [7], []) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext, getLive, s7, s4]
-- rd_continue_missing=(Continue 3,[],[])
example : obs (removeDead (.continue 3 : P) L13 [.nextFree] []) =
    (.continue 3, [], []) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, getLive]
-- rd_catchall=(Tick,[3; 1],[NextFree])
example : obs (removeDead (.tick : P) L13 [.nextFree] []) =
    (.tick, [3, 1], [.nextFree]) := by
  simp [obs, removeDead, L13, sptInsert, sptToAList, sptFoldi, lrNext, getLive]
-- rd_prog=Skip
example : removeDeadProg (.seq (.inst (.const 5 3)) (.move 0 [(1, 2)]) : P) = .skip := by
  simp [removeDeadProg, removeDead, sptLookup, removeDeadInst,
    removeDeadInstCore]

-- lsr_agree=T
example : liveStoreRel [(WordStore.nextFree : WordStoreHOL)]
    ((HolFiniteMapExact.empty.updateEq (WordStore.nextFree, (1 : Nat))).updateEq (WordStore.endOfHeap, 2))
    (HolFiniteMapExact.empty.updateEq (WordStore.endOfHeap, 2)) := by
  intro n hn
  simp only [List.mem_singleton] at hn
  by_cases h : n = WordStore.endOfHeap <;>
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, HolFiniteMapExact.empty, h, hn]
-- lsr_differ=F
example : ¬ liveStoreRel [(WordStore.nextFree : WordStoreHOL)]
    (HolFiniteMapExact.empty.updateEq (WordStore.endOfHeap, (1 : Nat)))
    (HolFiniteMapExact.empty.updateEq (WordStore.endOfHeap, 2)) := fun h => by
  have := h .endOfHeap (by simp)
  simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at this

end Flapjack.Test.WordAllocRemoveDeadParity
