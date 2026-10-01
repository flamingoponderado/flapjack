import Flapjack.Compiler.Backend.WordAlloc.FullSSA

namespace Flapjack.Test.WordAllocFullSSAParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- One uniform rewrite set is used for every row; not every lemma fires on every row.
set_option linter.unusedSimpArgs false

/-! Same-input replay of fresh original EVAL results
(`scripts/hol-probes/word_alloc_full_ssa_probe.out`) of `full_ssa_cc_trans` at
64-bit words: the limit, the argument entry move and the renamed body.
Finite observations do not establish cross-prover equivalence. -/

-- fs_skip=Seq (Move1 []) Skip
example : fullSsaCcTrans 0 (.skip : WordLangProgHOL (BitVec 64)) =
    .seq (.move 1 []) .skip := by
  simp only [fullSsaCcTrans, ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- fs_args=Seq (Move1 [(5,0); (9,2)]) (Seq (Move0 [(2,9)]) (Return 5 [2]))
example : fullSsaCcTrans 2 (.return 0 [2] : WordLangProgHOL (BitVec 64)) =
    .seq (.move 1 [(5,0), (9,2)]) (.seq (.move 0 [(2,9)]) (.return 5 [2])) := by
  simp only [fullSsaCcTrans, ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- fs_assign=Seq (Move1 [(9,0); (13,2)]) (Seq (Assign 17 (Op Add [Var 9; Var 13])) (Seq (Move0 [(2,17)]) (Return 9 [2])))
example : fullSsaCcTrans 2 (.seq (.assign 6 (.op .add [.var 0, .var 2])) (.return 0 [6]) : WordLangProgHOL (BitVec 64)) =
    .seq (.move 1 [(9,0), (13,2)]) (.seq (.assign 17 (.op .add [.var 9, .var 13])) (.seq (.move 0 [(2,17)]) (.return 9 [2]))) := by
  simp only [fullSsaCcTrans, ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- fs_if=Seq (Move1 [(5,0)]) (Seq (If Equal 5 (Imm 0w) (Seq (Assign 9 (Const 1w)) (Seq (Move1 [(17,9)]) Skip)) (Seq (Assign 13 (Const 2w)) (Seq (Move1 [(17,13)
example : fullSsaCcTrans 1 (.seq (.ite .equal 0 (.imm 0) (.assign 2 (.const 1)) (.assign 2 (.const 2))) (.return 0 [2]) : WordLangProgHOL (BitVec 64)) =
    .seq (.move 1 [(5,0)]) (.seq (.ite .equal 5 (.imm 0) (.seq (.assign 9 (.const 1)) (.seq (.move 1 [(17,9)]) .skip)) (.seq (.assign 13 (.const 2)) (.seq (.move 1 [(17,13)]) .skip))) (.seq (.move 0 [(2,17)]) (.return 5 [2]))) := by
  simp only [fullSsaCcTrans, ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl
-- fs_big=Seq (Move1 [(25,0)]) (Seq (Assign 29 (Var 25)) (Seq (Move0 [(2,29)]) (Return 25 [2])))
example : fullSsaCcTrans 1 (.seq (.assign 21 (.var 0)) (.return 0 [21]) : WordLangProgHOL (BitVec 64)) =
    .seq (.move 1 [(25,0)]) (.seq (.assign 29 (.var 25)) (.seq (.move 0 [(2,29)]) (.return 25 [2]))) := by
  simp only [fullSsaCcTrans, ssaCcTrans, ssaCcTransExp_op, List.map, ssaCcTransExp]
  with_unfolding_all rfl

end Flapjack.Test.WordAllocFullSSAParity
