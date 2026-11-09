import Flapjack.Compiler.Backend.BvlToBvi
import Flapjack.Compiler.Backend.BvlToBvi.Analysis
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs

/-! Operation lowering for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private def zero : Bvi.Exp := .op (.intOp (.const 0)) []
private def argsOrZero (xs : List Bvi.Exp) : List Bvi.Exp := if xs.isEmpty then [zero] else xs
/-- Location of the list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ListLength_location_def"]
def listLengthLocation : Nat := initGlobalsLocation + 1
/-- Location of the byte-list conversion stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "FromListByte_location_def"]
def fromListByteLocation : Nat := listLengthLocation + 1
/-- Location of the byte-array to list stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ToListByte_location_def"]
def toListByteLocation : Nat := fromListByteLocation + 1
/-- Location of the combined list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "SumListLength_location_def"]
def sumListLengthLocation : Nat := toListByteLocation + 1
/-- Location of the byte-concatenation stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ConcatByte_location_def"]
def concatByteLocation : Nat := sumListLengthLocation + 1
private def listLength (x : Bvi.Exp) : Bvi.Exp := .call 0 (some listLengthLocation) [x, zero] none

/-- Lower an operation and its already compiled operands, retaining the
source's operand evaluation and stub-call conventions. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_op_def"]
def compileOp (op : ClosLang.Op) (xs : List Bvi.Exp) : Bvi.Exp :=
  match op with
  | .intOp (.const i) =>
      if xs.isEmpty then compileInt i else .let [.op (.intOp (.const 0)) xs] (compileInt i)
  | .globOp (.global n) =>
      if xs.isEmpty then .op (.globOp (.global (n + 1))) []
      else .let xs (.op (.memOp .el) [
        .op (.intOp .add) [.op (.intOp (.const 2)) [], .var 0], .op (.globOp .globalsPtr) []])
  | .globOp (.setGlobal n) => .op (.globOp (.setGlobal (n + 1))) xs
  | .globOp .allocGlobal => .call 0 (some allocGlobalLocation) xs none
  | .blockOp (.fromList n) =>
      .let (argsOrZero xs) (.op (.blockOp (.fromList n)) [.var 0, listLength (.var 0)])
  | .install =>
      .let (if xs.length ≠ 2 then [.let xs zero, zero] else xs)
        (.op .install [listLength (.var 0), listLength (.var 1), .var 0, .var 1])
  | .memOp .fromListByte =>
      .let (argsOrZero xs) (.call 0 (some fromListByteLocation)
        [.var 0, zero, .op (.memOp (.refByte true)) [zero, listLength (.var 0)]] none)
  | .memOp .toListByte =>
      .let (argsOrZero xs) (.call 0 (some toListByteLocation)
        [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)
  | .memOp .concatByteVec =>
      .let (argsOrZero xs) (.call 0 (some concatByteLocation)
        [.var 0, zero, .op (.memOp (.refByte true)) [zero,
          .call 0 (some sumListLengthLocation) [.var 0, zero] none]] none)
  | .memOp (.copyByte true) =>
      .let (if xs.length < 3 then xs ++ List.replicate 3 zero else xs)
        (.let [.op (.memOp (.refByte true)) [zero, .var 0]]
          (.let [.op (.memOp (.copyByte false)) [zero, .var 0, .var 1, .var 2, .var 3]] (.var 1)))
  | .label l => .op (.label (bvlNumStubs + bvlToBviNamespaces * l)) xs
  | .memOp (.mutCons _ _) | .memOp .updateCons | .memOp .finaliseCons => .let xs zero
  | op => .op op xs

end Flapjack.Compiler.Backend.BvlToBvi
