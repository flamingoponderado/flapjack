-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.TmcOpsWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (0, 0, (.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 6)) .skip)))))) ((.seq ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 24)]))))))))))), 2) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (1, 0, (.assign 8 ((.const 34))), 2) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (2, 0, (.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln)))), 2) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (3, 0, (.assign 8 ((.var 4))), 2) =>
      true
  | _ => false

private def matches4 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (4, 0, (.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])) 8)) ((.assign 8 (.const 2)))), 2) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3 &&
      matches4 entry4
  | _ => false

end Flapjack.Test.TmcOpsWordOracle
