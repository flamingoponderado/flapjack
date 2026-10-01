import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.Test.WordAllocSSAHelpersParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
/-! Same-input replay by definitional equality of fresh original EVAL results
(`scripts/hol-probes/word_alloc_ssa_helpers_probe.out`) for
`list_next_var_rename_move`, `force_rename`, `mk_prio`, `ssa_reconcile`
(moves, identity-only, non-unit key payload) and `loop_setup`, at 64-bit
words with raw sparse trees. HOL `Move0`/`Move1` are `Move 0`/`Move 1`.
Finite observations do not establish cross-prover equivalence. -/

abbrev m : Spt Nat := sptInsert 2 10 (sptInsert 3 11 (sptInsert 4 12 .ln))

-- lnvrm_basic=(Move0 [(21,11); (25,0); (29,10)],BN (BS LN 29 (LS 12)) (BN (BN LN (LS 25)) (LS 21)),33)
example : (listNextVarRenameMove m 21 [3, 9, 2] : WordLangProgHOL (BitVec 64) × Spt Nat × Nat) =
    (.move 0 [(21,11), (25,0), (29,10)],.bn (.bs .ln 29 (.ls 12)) (.bn (.bn .ln (.ls 25)) (.ls 21)),33) := by with_unfolding_all rfl
-- lnvrm_empty=(Move0 [],BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (listNextVarRenameMove m 21 [] : WordLangProgHOL (BitVec 64) × Spt Nat × Nat) =
    (.move 0 [],.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- fr_basic=BN (BS LN 32 (LS 12)) (BN LN (BS LN 11 (LS 31)))
example : forceRename [(2, 30), (7, 31), (2, 32)] m =
    .bn (.bs .ln 32 (.ls 12)) (.bn .ln (.bs .ln 11 (.ls 31))) := by with_unfolding_all rfl
-- mp_left=SOME (INL ())
example : mkPrio (.skip : WordLangProgHOL (BitVec 64)) .tick =
    some (.inl ()) := by with_unfolding_all rfl
-- mp_right=SOME (INR ())
example : mkPrio (.tick : WordLangProgHOL (BitVec 64)) .skip =
    some (.inr ()) := by with_unfolding_all rfl
-- mp_both=SOME (INL ())
example : mkPrio (.skip : WordLangProgHOL (BitVec 64)) .skip =
    some (.inl ()) := by with_unfolding_all rfl
-- mp_none=NONE
example : mkPrio (.tick : WordLangProgHOL (BitVec 64)) (.raise 2) =
    none := by with_unfolding_all rfl
-- sr_moves=Move1 [(40,10)]
example : (ssaReconcile m (sptInsert 2 40 (sptInsert 3 11 .ln)) (sptInsert 2 () (sptInsert 3 () (sptInsert 9 () .ln))) : WordLangProgHOL (BitVec 64)) =
    .move 1 [(40,10)] := by with_unfolding_all rfl
-- sr_skip=Skip
example : (ssaReconcile m m (sptInsert 2 () (sptInsert 3 () .ln)) : WordLangProgHOL (BitVec 64)) =
    .skip := by with_unfolding_all rfl
-- sr_payload=Move1 [(50,12)]
example : (ssaReconcile m (sptInsert 4 50 .ln) (sptInsert 4 true .ln) : WordLangProgHOL (BitVec 64)) =
    .move 1 [(50,12)] := by with_unfolding_all rfl
-- ls_mixed=(Seq (Seq (Inst (Const 21 0w)) (Seq (Inst (Const 25 0w)) Skip)) (Move0 [(29,12); (33,10)]),BN (BS LN 33 (LS 29)) (BN (BN LN (LS 25)) (BS LN 11 (LS 21)
example : (loopSetup (sptInsert 2 () (sptInsert 9 () .ln)) (sptInsert 4 () (sptInsert 7 () .ln)) m 21 : WordLangProgHOL (BitVec 64) × Spt Nat × Nat) =
    (.seq (.seq (.inst (.const 21 0)) (.seq (.inst (.const 25 0)) .skip)) (.move 0 [(29,12), (33,10)]),.bn (.bs .ln 33 (.ls 29)) (.bn (.bn .ln (.ls 25)) (.bs .ln 11 (.ls 21))),37) := by with_unfolding_all rfl
-- ls_empty=(Seq Skip (Move0 []),BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (loopSetup .ln .ln m 21 : WordLangProgHOL (BitVec 64) × Spt Nat × Nat) =
    (.seq .skip (.move 0 []),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl

end Flapjack.Test.WordAllocSSAHelpersParity
