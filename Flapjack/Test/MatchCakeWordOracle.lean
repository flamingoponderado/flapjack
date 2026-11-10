-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.MatchCakeWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches14 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (92, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.assign 4 ((.const 4)))) ((.seq ((.seq ((.assign 1 ((.var 2)))) ((.seq ((.assign 3 ((.var 4)))) ((.seq ((.assign 5 ((.op .and [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.ite .equal 1 ((.reg 3)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live44, .ln), .skip, 92, 2))) ((some 21)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))))) ((.ite .equal 1 ((.reg 3)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))))))))))) ((.seq ((.ite .equal 6 ((.imm 18)) ((.seq ((.assign 8 ((.const 8)))) ((.move 0 [(12, 8)])))) ((.seq ((.assign 10 ((.const 12)))) ((.move 0 [(12, 10)])))))) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live45, live46))) .skip)))))) .skip)))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 12)) .skip)))) ((.assign 14 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 40)])) 14)) ((.assign 18 (.const 2))))) ((.return 0 [18]))))))))))))))), 3) =>
      decide (live44 = Flapjack.sptListInsert [0] .ln) &&
      decide (live45 = Flapjack.sptListInsert [0] .ln) &&
      decide (live46 = Flapjack.sptListInsert [12] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13, entry14] =>
      shared_matches0 entry0 &&
      shared_matches1 entry1 &&
      shared_matches2 entry2 &&
      shared_matches3 entry3 &&
      shared_matches4 entry4 &&
      shared_matches5 entry5 &&
      shared_matches6 entry6 &&
      shared_matches7 entry7 &&
      shared_matches8 entry8 &&
      shared_matches9 entry9 &&
      shared_matches10 entry10 &&
      shared_matches11 entry11 &&
      shared_matches12 entry12 &&
      shared_matches13 entry13 &&
      matches14 entry14
  | _ => false

end Flapjack.Test.MatchCakeWordOracle
