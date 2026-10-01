import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies

namespace Flapjack.Test.WordAllocFixInconsistenciesParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
/-! Same-input kernel replay (`rfl`) of fresh original EVAL results
(`scripts/hol-probes/word_alloc_fix_inconsistencies_probe.out`) for
`option_lookup`, `priority`, `fake_move`, `fake_moves` (empty, left-only,
right-only, mixed with a shared unequal name) and `fix_inconsistencies`
(equal maps, mixed maps), at 64-bit words with raw sparse trees. HOL `Move1`
is `Move 1`. Finite observations do not establish cross-prover equivalence. -/

-- ol_hit=9
example : optionLookup (sptInsert 3 9 .ln) 3 =
    9 := by with_unfolding_all rfl
-- ol_miss=0
example : optionLookup (sptInsert 3 9 .ln) 4 =
    0 := by with_unfolding_all rfl
-- pr_none=(1,1)
example : (priority none true, priority none false) =
    (1,1) := by with_unfolding_all rfl
-- pr_inl=(2,1)
example : (priority (some (.inl ())) true, priority (some (.inl ())) false) =
    (2,1) := by with_unfolding_all rfl
-- pr_inr=(1,2)
example : (priority (some (.inr ())) true, priority (some (.inr ())) false) =
    (1,2) := by with_unfolding_all rfl
-- fm=Inst (Const 7 0w)
example : (fakeMove 7 : (WordLangProgHOL (BitVec 64))) =
    .inst (.const 7 0) := by with_unfolding_all rfl
-- fms_empty=(Skip,Skip,13,BN LN (LS 5),LN)
example : (fakeMoves none [] (sptInsert 1 5 .ln) .ln 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat × Spt Nat) =
    (.skip,.skip,13,.bn .ln (.ls 5),.ln) := by with_unfolding_all rfl
-- fms_left_only=(Seq Skip (Move 2 [(13,5)]),Seq Skip (Inst (Const 13 0w)),17,BN LN (LS 13),BN LN (LS 13))
example : (fakeMoves (some (.inl ())) [1] (sptInsert 1 5 .ln) .ln 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat × Spt Nat) =
    (.seq .skip (.move 2 [(13,5)]),.seq .skip (.inst (.const 13 0)),17,.bn .ln (.ls 13),.bn .ln (.ls 13)) := by with_unfolding_all rfl
-- fms_right_only=(Seq Skip (Inst (Const 13 0w)),Seq Skip (Move 2 [(13,6)]),17,BN (LS 13) LN,BN (LS 13) LN)
example : (fakeMoves (some (.inr ())) [2] .ln (sptInsert 2 6 .ln) 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat × Spt Nat) =
    (.seq .skip (.inst (.const 13 0)),.seq .skip (.move 2 [(13,6)]),17,.bn (.ls 13) .ln,.bn (.ls 13) .ln) := by with_unfolding_all rfl
-- fms_both=(Seq (Seq Skip (Inst (Const 13 0w))) (Move1 [(17,5)]),Seq (Seq Skip (Move1 [(13,6)])) (Inst (Const 17 0w)),21,BN (LS 13) (BS LN 17 (LS 7)),BN (LS 13) (BS LN 17 (LS 8)))
example : (fakeMoves none [1, 2, 3] (sptInsert 1 5 (sptInsert 3 7 .ln)) (sptInsert 2 6 (sptInsert 3 8 .ln)) 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat × Spt Nat) =
    (.seq (.seq .skip (.inst (.const 13 0))) (.move 1 [(17,5)]),.seq (.seq .skip (.move 1 [(13,6)])) (.inst (.const 17 0)),21,.bn (.ls 13) (.bs .ln 17 (.ls 7)),.bn (.ls 13) (.bs .ln 17 (.ls 8))) := by with_unfolding_all rfl
-- fi_equal=(Seq (Move1 []) Skip,Seq (Move1 []) Skip,13,BN LN (LS 5))
example : (fixInconsistencies none (sptInsert 1 5 .ln) (sptInsert 1 5 .ln) 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat) =
    (.seq (.move 1 []) .skip,.seq (.move 1 []) .skip,13,.bn .ln (.ls 5)) := by with_unfolding_all rfl
-- fi_mixed=(Seq (Move 2 [(13,7)]) (Seq (Seq Skip (Inst (Const 17 0w))) (Move 2 [(21,5)])),Seq (Move1 [(13,8)]) (Seq (Seq Skip (Move1 [(17,6)])) (Inst (Const 21 0w))),25,BN (LS 17) (BS LN 21 (LS 13)))
example : (fixInconsistencies (some (.inl ())) (sptInsert 1 5 (sptInsert 3 7 .ln)) (sptInsert 2 6 (sptInsert 3 8 .ln)) 13 : (WordLangProgHOL (BitVec 64)) × (WordLangProgHOL (BitVec 64)) × Nat × Spt Nat) =
    (.seq (.move 2 [(13,7)]) (.seq (.seq .skip (.inst (.const 17 0))) (.move 2 [(21,5)])),.seq (.move 1 [(13,8)]) (.seq (.seq .skip (.move 1 [(17,6)])) (.inst (.const 21 0))),25,.bn (.ls 17) (.bs .ln 21 (.ls 13))) := by with_unfolding_all rfl

end Flapjack.Test.WordAllocFixInconsistenciesParity
