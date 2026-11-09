-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.InstallXorWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (29, 3, (.seq ((.assign 1 ((.lookup .bitmapBuffer)))) ((.seq ((.assign 3 ((.lookup .codeBuffer)))) ((.seq ((.set .bitmapBuffer ((.var 2)))) ((.seq ((.set .codeBuffer ((.var 4)))) ((.seq ((.install 3 4 1 2 (live0, .ln))) ((.return 0 [3]))))))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (30, 4, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 2 ((.lookup .bitmapBuffer)))) ((.call none ((some 31)) [0, 2, 4, 6] none)))) ((.seq ((.assign 3 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 2 ((.load ((.op .add [(.var 3), (.const 8)])))))) ((.seq ((.assign 2 ((.shift .lsr ((.var 2)) (.const 2))))) ((.seq ((.codeBufferWrite 6 2)) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 1)])))) ((.seq ((.assign 2 ((.load ((.op .add [(.var 3), (.const 16)])))))) ((.call none ((some 30)) [0, 2, 4, 6] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (31, 4, (.ite .test 4 ((.imm 1)) ((.call none ((some 29)) [0, 2, 6] none)) ((.seq ((.assign 3 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 3), (.const 8)])))))) ((.seq ((.assign 4 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.dataBufferWrite 2 4)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 8)])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 3), (.const 16)])))))) ((.call none ((some 31)) [0, 2, 4, 6] none))))))))))))))))), 0) =>
      true
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (36, 4, (.ite .lower 6 ((.imm 2)) ((.ite .equal 6 ((.imm 0)) ((.seq ((.assign 1 (.const 2))) ((.return 0 [1])))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.seq ((.assign 7 ((.op .xor [(.var 5), (.var 3)])))) ((.seq ((.store ((.var 2)) 7)) ((.seq ((.assign 1 (.const 2))) ((.return 0 [1])))))))))))))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.seq ((.assign 9 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.assign 7 ((.load ((.op .add [(.var 2), (.const 8)])))))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 2)])))) ((.seq ((.assign 5 ((.op .xor [(.var 5), (.var 3)])))) ((.seq ((.assign 9 ((.op .xor [(.var 9), (.var 7)])))) ((.seq ((.store ((.var 2)) 5)) ((.seq ((.store ((.op .add [(.var 2), (.const 8)])) 9)) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 16)])))) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 16)])))) ((.call none ((some 36)) [0, 2, 4, 6] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3
  | _ => false

end Flapjack.Test.InstallXorWordOracle
