import Flapjack.Compiler.Backend.WordAlloc.SSATransInst

namespace Flapjack.Test.WordAllocSSATransInstParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
/-! Same-input replay by definitional equality of fresh original EVAL results
(`scripts/hol-probes/word_alloc_ssa_trans_inst_probe.out`) for every
`ssa_cc_trans_inst` clause (incl. fixed-register AddCarry/overflow/LongMul/
LongDiv moves, the Load16 and FP catchall, and both `dimindex` branches of
FPMovToReg/FPMovFromReg at 64 and 32 bits) and for `ssa_cc_trans_exp`. HOL
`Move0`/`Move1` are `Move 0`/`Move 1`. Finite observations do not establish
cross-prover equivalence. -/

abbrev m : Spt Nat := sptInsert 2 10 (sptInsert 3 11 (sptInsert 4 12 .ln))

-- sti_skip=(Skip,BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (ssaCcTransInst (.skip : WordLangInst (BitVec 64)) m 21) =
    (.skip,.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sti_const=(Inst (Const 21 5w),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.const 2 5 : WordLangInst (BitVec 64)) m 21) =
    (.inst (.const 21 5),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_binop_reg=(Inst (Arith (Binop Add 21 11 (Reg 12))),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.arith (.binop .add 2 3 (.reg 4)) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.arith (.binop .add 21 11 (.reg 12))),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_binop_imm=(Inst (Arith (Binop Sub 21 0 (Imm 7w))),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.arith (.binop .sub 2 9 (.imm 7)) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.arith (.binop .sub 21 0 (.imm 7))),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_shift_reg=(Seq (Move1 [(8,12)]) (Inst (Arith (Shift Lsl 21 11 (Reg 8)))),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.arith (.shift .lsl 2 3 (.reg 4)) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.move 1 [(8,12)]) (.inst (.arith (.shift .lsl 21 11 (.reg 8)))),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_shift_imm=(Inst (Arith (Shift Asr 21 11 (Imm 1w))),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.arith (.shift .asr 2 3 (.imm 1)) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.arith (.shift .asr 21 11 (.imm 1))),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_div=(Inst (Arith (Div 21 11 12)),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.arith (.div 2 3 4) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.arith (.div 21 11 12)),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_addcarry=(Seq (Move1 [(0,0)]) (Seq (Inst (Arith (AddCarry 21 11 12 0))) (Move1 [(25,0)])),BN (BS LN 21 (LS 12)) (BN (LS 25) (LS 11)),29)
example : (ssaCcTransInst (.arith (.addCarry 2 3 4 5) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.move 1 [(0,0)]) (.seq (.inst (.arith (.addCarry 21 11 12 0))) (.move 1 [(25,0)])),.bn (.bs .ln 21 (.ls 12)) (.bn (.ls 25) (.ls 11)),29) := by with_unfolding_all rfl
-- sti_addoverflow=(Seq (Inst (Arith (AddOverflow 21 11 12 0))) (Move1 [(25,0)]),BN (BS LN 21 (LS 12)) (BN (LS 25) (LS 11)),29)
example : (ssaCcTransInst (.arith (.addOverflow 2 3 4 5) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.inst (.arith (.addOverflow 21 11 12 0))) (.move 1 [(25,0)]),.bn (.bs .ln 21 (.ls 12)) (.bn (.ls 25) (.ls 11)),29) := by with_unfolding_all rfl
-- sti_suboverflow=(Seq (Inst (Arith (SubOverflow 21 11 12 0))) (Move1 [(25,0)]),BN (BS LN 21 (LS 12)) (BN (LS 25) (LS 11)),29)
example : (ssaCcTransInst (.arith (.subOverflow 2 3 4 5) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.inst (.arith (.subOverflow 21 11 12 0))) (.move 1 [(25,0)]),.bn (.bs .ln 21 (.ls 12)) (.bn (.ls 25) (.ls 11)),29) := by with_unfolding_all rfl
-- sti_longmul=(Seq (Move1 [(0,12); (4,0)]) (Seq (Inst (Arith (LongMul 6 0 0 4))) (Move1 [(25,0); (21,6)])),BN (BS LN 21 (LS 12)) (BN LN (LS 25)),29)
example : (ssaCcTransInst (.arith (.longMul 2 3 4 9) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.move 1 [(0,12), (4,0)]) (.seq (.inst (.arith (.longMul 6 0 0 4))) (.move 1 [(25,0), (21,6)])),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 25)),29) := by with_unfolding_all rfl
-- sti_longdiv=(Seq (Move1 [(6,12); (0,0)]) (Seq (Inst (Arith (LongDiv 0 6 6 0 11))) (Move1 [(21,6); (25,0)])),BN (BS LN 25 (LS 12)) (BN LN (LS 21)),29)
example : (ssaCcTransInst (.arith (.longDiv 2 3 4 9 3) : WordLangInst (BitVec 64)) m 21) =
    (.seq (.move 1 [(6,12), (0,0)]) (.seq (.inst (.arith (.longDiv 0 6 6 0 11))) (.move 1 [(21,6), (25,0)])),.bn (.bs .ln 25 (.ls 12)) (.bn .ln (.ls 21)),29) := by with_unfolding_all rfl
-- sti_load=(Inst (Mem Load 21 (Addr 11 8w)),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.mem .load 2 (.addr 3 8) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.mem .load 21 (.addr 11 8)),.bn (.bs .ln 21 (.ls 12)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_store=(Inst (Mem Store 10 (Addr 11 8w)),BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (ssaCcTransInst (.mem .store 2 (.addr 3 8) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.mem .store 10 (.addr 11 8)),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sti_load32=(Inst (Mem Load32 21 (Addr 0 0w)),BN (BS LN 10 (LS 21)) (BN LN (LS 11)),25)
example : (ssaCcTransInst (.mem .load32 4 (.addr 9 0) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.mem .load32 21 (.addr 0 0)),.bn (.bs .ln 10 (.ls 21)) (.bn .ln (.ls 11)),25) := by with_unfolding_all rfl
-- sti_store8=(Inst (Mem Store8 0 (Addr 12 1w)),BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (ssaCcTransInst (.mem .store8 9 (.addr 4 1) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.mem .store8 0 (.addr 12 1)),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sti_load16=(Inst (Mem Load16 2 (Addr 3 8w)),BN (BS LN 10 (LS 12)) (BN LN (LS 11)),21)
example : (ssaCcTransInst (.mem .load16 2 (.addr 3 8) : WordLangInst (BitVec 64)) m 21) =
    (.inst (.mem .load16 2 (.addr 3 8)),.bn (.bs .ln 10 (.ls 12)) (.bn .ln (.ls 11)),21) := by with_unfolding_all rfl
-- sti_fpless=(Inst (FP (FPLess 21 1 0)),BN (BS LN 21 (LS 12)) (BN LN (LS 11)),25)
example : ssaCcTransExp m (.var 3 : WordLangExpHOL (BitVec 64)) =
    .var 11 := by
  simp only [ssaCcTransExp]; with_unfolding_all rfl
-- ste_missing=Var 0
example : ssaCcTransExp m (.var 9 : WordLangExpHOL (BitVec 64)) =
    .var 0 := by
  simp only [ssaCcTransExp]; with_unfolding_all rfl
-- ste_nested=Op Add [Var 10; Load (Var 12); Const 3w; Shift Lsr (Var 11) (Var 10)]
example : ssaCcTransExp m (.op .add [.var 2, .load (.var 4), .const 3, .shift .lsr (.var 3) (.var 2)] : WordLangExpHOL (BitVec 64)) =
    .op .add [.var 10, .load (.var 12), .const 3, .shift .lsr (.var 11) (.var 10)] := by
  simp only [ssaCcTransExp_op, List.map, ssaCcTransExp]; with_unfolding_all rfl
-- ste_lookup=Lookup NextFree
example : ssaCcTransExp m (.lookup .nextFree : WordLangExpHOL (BitVec 64)) =
    .lookup .nextFree := by
  simp only [ssaCcTransExp]

end Flapjack.Test.WordAllocSSATransInstParity
