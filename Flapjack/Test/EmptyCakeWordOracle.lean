-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.EmptyCakeWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches13 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 0, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live43, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 2) =>
      decide (live43 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13] =>
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
      matches13 entry13
  | _ => false

end Flapjack.Test.EmptyCakeWordOracle
