import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

namespace Flapjack.Test.WordAllocSSACcTransParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- One uniform rewrite set is used for every expression-bearing row; not every
-- lemma fires on every row.
set_option linter.unusedSimpArgs false

/-! Same-input replay by definitional equality of fresh original EVAL results
(`scripts/hol-probes/word_alloc_ssa_cc_trans_probe.out`) of `ssa_cc_trans`
over representative 64-bit programs covering every clause family, starting
from the same renaming map, counter 21 and empty loop-target list. HOL
`Move0`/`Move1` are `Move 0`/`Move 1`; the FFI name `strlit "f"` is the
byte list `[102]`. Finite observations do not establish cross-prover
equivalence. -/

abbrev m : Spt Nat := sptInsert 2 10 (sptInsert 3 11 (sptInsert 4 12 .ln))

-- sc_skip
example : ssaCcTrans (.skip : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.skip,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_move
example : ssaCcTrans (.move 1 [(2,3),(5,2)] : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.move 1 [(21,11), (25,10)],.bn (.bs .ln 21 (.ls 12)) (.bn (.ls 25) (.ls 21)),29) := by with_unfolding_all rfl
-- sc_storeconsts
example : ssaCcTrans (.storeConsts 0 0 2 3 [(true,7)] : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 1 [(4,10), (6,11)]) (.seq (.storeConsts 0 2 4 6 [(true,7)]) (.move 1 [(25,4), (21,6)])),.bn (.bs .ln 25 (.ls 12)) (.bn .ln (.ls 21)),29) := by with_unfolding_all rfl
-- sc_inst
example : ssaCcTrans (.inst (.const 2 5) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.inst (.const 21 5),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sc_assign
example : ssaCcTrans (.assign 3 (.op .add [.var 2, .var 4]) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.assign 21 (.op .add [.var 10, .var 12]),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 21)),25) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_get
example : ssaCcTrans (.get 2 .nextFree : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.get 21 .nextFree,.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sc_store
example : ssaCcTrans (.store (.var 3) 4 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.store (.var 11) 12,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_seq
example : ssaCcTrans (.seq (.assign 3 (.var 2)) (.assign 2 (.var 3)) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.assign 21 (.var 10)) (.assign 25 (.var 21)),.bn (.bs .ln 25 (.ls 12)) (.bn .ln (.ls 21)),29) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_mustterminate
example : ssaCcTrans (.mustTerminate (.assign 3 (.var 2)) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.mustTerminate (.assign 21 (.var 10)),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 21)),25) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_if
example : ssaCcTrans (.ite .equal 2 (.reg 3) (.assign 3 (.var 2)) (.assign 5 (.var 4)) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.ite .equal 10 (.reg 11) (.seq (.assign 21 (.var 10)) (.seq (.move 1 [(29,21)]) (.seq .skip (.inst (.const 33 0))))) (.seq (.assign 25 (.var 12)) (.seq (.move 1 [(29,11)]) (.seq .skip (.move 1 [(33,25)])))),.bn (.bs .ln 10 (.ls 12)) (.bn (.ls 33) (.ls 29)),37) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_if_skip
example : ssaCcTrans (.ite .less 2 (.imm 1) .skip (.assign 3 (.var 4)) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.ite .less 10 (.imm 1) (.seq .skip (.seq (.move 2 [(25,11)]) .skip)) (.seq (.assign 21 (.var 12)) (.seq (.move 1 [(25,21)]) .skip)),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 25)),29) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_alloc
example : ssaCcTrans (.alloc 3 (sptInsert 2 () .ln, sptInsert 4 () .ln) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(23,12), (27,10)]) (.seq (.move 1 [(2,11)]) (.seq (.alloc 2 (.bn .ln (.bn .ln (.bn (.bn (.ls ()) .ln) .ln)),.bn .ln (.bn .ln (.bn .ln (.bn (.ls ()) .ln))))) (.move 0 [(33,23), (37,27)]))),.bn (.bs .ln 37 (.ls 33)) .ln,41) := by with_unfolding_all rfl
-- sc_raise
example : ssaCcTrans (.raise 3 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 1 [(2,11)]) (.raise 2),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_opcurrheap
example : ssaCcTrans (.opCurrHeap .add 5 3 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.opCurrHeap .add 21 11,.bn (.bs .ln 10 (.ls 12)) (.bn (.ls 21) (.ls 11)),25) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_return
example : ssaCcTrans (.return 2 [3,4] : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(2,11), (4,12)]) (.return 10 [2, 4]),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_tick
example : ssaCcTrans (.tick : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.tick,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_set
example : ssaCcTrans (.set .nextFree (.var 3) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.set .nextFree (.var 11),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_locvalue
example : ssaCcTrans (.locValue 3 9 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.locValue 21 9,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 21)),25) := by with_unfolding_all rfl
-- sc_install
example : ssaCcTrans (.install 2 3 4 9 (sptInsert 2 () .ln, sptInsert 4 () .ln) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(23,12), (27,10)]) (.seq (.move 1 [(2,27), (4,11)]) (.seq (.install 2 4 23 0 (.bn .ln (.bn .ln (.bn (.bn (.ls ()) .ln) .ln)),.bn .ln (.bn .ln (.bn .ln (.bn (.ls ()) .ln))))) (.seq (.move 1 [(33,2)]) (.move 0 [(37,23), (41,33)])))),.bn (.bs .ln 41 (.ls 37)) .ln,45) := by with_unfolding_all rfl
-- sc_codebufferwrite
example : ssaCcTrans (.codeBufferWrite 2 3 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.codeBufferWrite 10 11,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_databufferwrite
example : ssaCcTrans (.dataBufferWrite 4 9 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.dataBufferWrite 12 0,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_ffi
example : ssaCcTrans (.ffi (.implode [102]) 2 3 4 9 (sptInsert 2 () .ln, sptInsert 4 () .ln) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(23,12), (27,10)]) (.seq (.move 1 [(2,27), (4,11), (6,23), (8,0)]) (.seq (.ffi (.implode [102]) 2 4 6 8 (.bn .ln (.bn .ln (.bn (.bn (.ls ()) .ln) .ln)),.bn .ln (.bn .ln (.bn .ln (.bn (.ls ()) .ln))))) (.move 0 [(33,23), (37,27)]))),.bn (.bs .ln 37 (.ls 33)) .ln,41) := by with_unfolding_all rfl
-- sc_call_tail
example : ssaCcTrans (.call none (some 7) [3,2] none : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 1 [(0,11), (2,10)]) (.call none (some 7) [0, 2] none),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_call_ret
example : ssaCcTrans (.call (some ([5], (sptInsert 2 () .ln, sptInsert 4 () .ln), .assign 3 (.var 5), 7, 8)) (some 7) [3] none : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(23,12), (27,10)]) (.seq (.move 1 [(2,11)]) (.call (some ([2],(.bn .ln (.bn .ln (.bn (.bn (.ls ()) .ln) .ln)),.bn .ln (.bn .ln (.bn .ln (.bn (.ls ()) .ln)))),.seq (.move 0 [(33,23), (37,27)]) (.seq (.move 1 [(41,2)]) (.assign 45 (.var 41))),7,8)) (some 7) [2] none)),.bn (.bs .ln 37 (.ls 33)) (.bn (.ls 41) (.ls 45)),49) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_call_handler
example : ssaCcTrans (.call (some ([5], (sptInsert 2 () .ln, sptInsert 4 () .ln), .assign 3 (.var 5), 7, 8)) (some 7) [3] (some (9, .assign 4 (.var 9), 7, 9)) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.move 0 [(23,12), (27,10)]) (.seq (.move 1 [(2,11)]) (.call (some ([2],(.bn .ln (.bn .ln (.bn (.bn (.ls ()) .ln) .ln)),.bn .ln (.bn .ln (.bn .ln (.bn (.ls ()) .ln)))),.seq (.seq (.move 0 [(33,23), (37,27)]) (.seq (.move 1 [(41,2)]) (.assign 45 (.var 41)))) (.seq (.move 1 [(57,33)]) (.seq (.seq (.seq .skip (.move 1 [(61,41)])) (.inst (.const 65 0))) (.move 1 [(69,45)]))),7,8)) (some 7) [2] (some (2,.seq (.seq (.move 0 [(33,23), (37,27)]) (.seq (.move 1 [(49,2)]) (.assign 53 (.var 49)))) (.seq (.move 1 [(57,53)]) (.seq (.seq (.seq .skip (.inst (.const 61 0))) (.move 1 [(65,49)])) (.inst (.const 69 0)))),7,9)))),.bn (.bs .ln 37 (.ls 57)) (.bn (.bs .ln 61 (.ls 65)) (.ls 69)),73) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_shareinst_load
example : ssaCcTrans (.shareInst .load 3 (.var 2) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.shareInst .load 21 (.var 10),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 21)),25) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_shareinst_store
example : ssaCcTrans (.shareInst .store 3 (.var 2) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.shareInst .store 11 (.var 10),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_loop
example : ssaCcTrans (.loop (sptInsert 2 () .ln) (.seq (.assign 2 (.var 2)) (.continue 0)) (sptInsert 3 () .ln) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.seq .skip (.move 0 [(21,11), (25,10)])) (.loop (.bn .ln (.bn (.bn .ln (.bn (.ls ()) .ln)) .ln)) (.seq (.seq (.assign 29 (.var 25)) (.seq (.move 1 [(25,29)]) (.continue 0))) (.move 1 [(25,29)])) (.bn .ln (.bn (.bn (.bn .ln (.ls ())) .ln) .ln))),.bn .ln (.bn .ln (.ls 21)),33) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_loop_break
example : ssaCcTrans (.loop (sptInsert 2 () (sptInsert 9 () .ln)) (.seq (.assign 3 (.var 2)) (.break 0)) (sptInsert 3 () .ln) : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.seq (.seq (.seq (.inst (.const 21 0)) .skip) (.move 0 [(25,11), (29,10)])) (.loop (.bn .ln (.bn (.bn (.bn (.ls ()) (.ls ())) .ln) .ln)) (.seq (.assign 33 (.var 29)) (.seq (.move 1 [(25,33)]) (.break 0))) (.bn .ln (.bn (.bn .ln (.bn (.ls ()) .ln)) .ln))),.bn .ln (.bn .ln (.ls 25)),37) := by
  simp only [ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- sc_break_free
example : ssaCcTrans (.break 4 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.break 4,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sc_continue_free
example : ssaCcTrans (.continue 0 : WordLangProgHOL (BitVec 64)) m 21 [] =
    (.continue 0,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl

end Flapjack.Test.WordAllocSSACcTransParity
