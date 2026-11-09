-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.ByteCopyWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (26, 5, (.ite .lower 2 ((.imm 4)) ((.ite .lower 2 ((.imm 2)) ((.ite .equal 2 ((.imm 0)) ((.return 0 [8])) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.return 0 [8])))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 1)))))) ((.ite .equal 2 ((.imm 2)) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.return 0 [8])))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 2)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 2)))))) ((.return 0 [8])))))))))))))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 1)))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 2)))))) ((.seq ((.inst ((.mem .load8 7 ((.addr 4 3)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 2)))))) ((.seq ((.inst ((.mem .store8 7 ((.addr 6 3)))))) ((.seq ((.assign 9 ((.op .sub [(.var 2), (.const 4)])))) ((.seq ((.assign 11 ((.op .add [(.var 4), (.const 4)])))) ((.seq ((.assign 13 ((.op .add [(.var 6), (.const 4)])))) ((.call none ((some 26)) [0, 9, 11, 13, 8] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (27, 5, (.ite .lower 2 ((.imm 4)) ((.ite .lower 2 ((.imm 2)) ((.ite .equal 2 ((.imm 0)) ((.return 0 [8])) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.return 0 [8])))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 18446744073709551615)))))) ((.ite .equal 2 ((.imm 2)) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.return 0 [8])))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 18446744073709551614)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 18446744073709551614)))))) ((.return 0 [8])))))))))))))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 18446744073709551615)))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 18446744073709551614)))))) ((.seq ((.inst ((.mem .load8 7 ((.addr 4 18446744073709551613)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 18446744073709551614)))))) ((.seq ((.inst ((.mem .store8 7 ((.addr 6 18446744073709551613)))))) ((.seq ((.assign 9 ((.op .sub [(.var 2), (.const 4)])))) ((.seq ((.assign 11 ((.op .sub [(.var 4), (.const 4)])))) ((.seq ((.assign 13 ((.op .sub [(.var 6), (.const 4)])))) ((.call none ((some 27)) [0, 9, 11, 13, 8] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1] =>
      matches0 entry0 &&
      matches1 entry1
  | _ => false

end Flapjack.Test.ByteCopyWordOracle
