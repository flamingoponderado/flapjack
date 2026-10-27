import Flapjack.Compiler.Backend.BvlToBvi.CompileOp

/-! Runtime stubs inserted by BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private def int (n : Int) : Bvi.Exp := .op (.intOp (.const n)) []
private def el (i x : Bvi.Exp) : Bvi.Exp := .op (.memOp .el) [i, x]
private def add (x y : Bvi.Exp) : Bvi.Exp := .op (.intOp .add) [x, y]
private def sub (x y : Bvi.Exp) : Bvi.Exp := .op (.intOp .sub) [x, y]

/-- Grow the global array when necessary and copy the existing entries. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "AllocGlobal_code_def"]
def allocGlobalCode : Nat × Bvi.Exp := (1,
  .let [.op (.globOp .globalsPtr) []] <|
  .let [el (int 0) (.var 0)] <|
  .let [add (.var 0) (.var 2)] <|
  .let [.op (.memOp .length) [.var 2]] <|
  .let [.op (.memOp .update) [.var 1, int 0, .var 3]] <|
    .ifThenElse (.op (.intOp .less) [.var 1, .var 2]) (.var 0)
      (.let [.op (.memOp .refArray) [int 0, add (.var 2) (.var 2)]] <|
       .let [.op (.globOp .setGlobalsPtr) [.var 0]] <|
         .call 0 (some copyGlobalsLocation) [.var 1, .var 6, sub (int 1) (.var 3)] none))

/-- Copy globals from the old array to the new one. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "CopyGlobals_code_def"]
def copyGlobalsCode : Nat × Bvi.Exp := (3,
  .let [.op (.memOp .update) [el (.var 2) (.var 1), .var 2, .var 0]]
    (.ifThenElse (.op (.blockOp .equal) [int 0, .var 3]) (.var 0)
      (.call 0 (some copyGlobalsLocation) [.var 1, .var 2, sub (int 1) (.var 3)] none)))

/-- Upper limit for the initial global array size. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "InitGlobals_max_def"]
def initGlobalsMax : Nat := 10000

/-- Allocate and initialize globals before entering the program. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "InitGlobals_code_def"]
def initGlobalsCode (start n : Nat) : Nat × Bvi.Exp :=
  let n := min (max n 1) initGlobalsMax
  (0, .let [.op (.memOp .refArray) [int 0, int (Int.ofNat n)]]
    (.let [.op (.memOp .update) [int 1, int 0, .var 0]]
      (.let [.op (.globOp .setGlobalsPtr) [.var 1]] (.call 0 (some start) [] (some (.var 0))))))

/-- Accumulate the length of a list. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ListLength_code_def"]
def listLengthCode : Nat × Bvi.Exp := (2,
  .ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 1)
    (.call 0 (some listLengthLocation) [el (int 1) (.var 0), add (.var 1) (int 1)] none))

/-- Copy a byte list into an array. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "FromListByte_code_def"]
def fromListByteCode : Nat × Bvi.Exp := (3,
  .ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2)
    (.let [.op (.memOp .updateByte) [el (int 0) (.var 0), .var 1, .var 2]]
      (.call 0 (some fromListByteLocation) [el (int 1) (.var 1), add (.var 2) (int 1), .var 3] none)))

/-- Convert a byte array to a list. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ToListByte_code_def"]
def toListByteCode : Nat × Bvi.Exp := (3,
  .ifThenElse (.op (.blockOp (.equalConst (.int 0))) [.var 1]) (.var 0)
    (.let [sub (int 1) (.var 1)] <|
     .let [.op (.memOp .derefByte) [.var 0, .var 3]] <|
       .call 0 (some toListByteLocation) [.op (.blockOp (.cons 0)) [.var 2, .var 0], .var 1, .var 4] none))

/-- Sum the lengths of byte arrays in a list. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "SumListLength_code_def"]
def sumListLengthCode : Nat × Bvi.Exp := (2,
  .ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 1)
    (.call 0 (some sumListLengthLocation)
      [el (int 1) (.var 0), add (.var 1) (.op (.memOp .lengthByte) [el (int 0) (.var 0)])] none))

/-- Concatenate a list of byte arrays into a destination. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ConcatByte_code_def"]
def concatByteCode : Nat × Bvi.Exp := (3,
  .ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2)
    (.let [el (int 0) (.var 0)] <|
     .let [.op (.memOp .lengthByte) [.var 0]] <|
     .let [.op (.memOp (.copyByte false)) [.var 3, .var 4, .var 0, int 0, .var 1]] <|
       .call 0 (some concatByteLocation) [el (int 1) (.var 3), add (.var 4) (.var 1), .var 5] none))

/-- Enumerate all BVL-to-BVI runtime stubs in source order. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "stubs_def"]
def stubs (start n : Nat) : List (Nat × Nat × Bvi.Exp) :=
  [(allocGlobalLocation, allocGlobalCode.1, allocGlobalCode.2),
   (copyGlobalsLocation, copyGlobalsCode.1, copyGlobalsCode.2),
   (initGlobalsLocation, (initGlobalsCode start n).1, (initGlobalsCode start n).2),
   (listLengthLocation, listLengthCode.1, listLengthCode.2),
   (fromListByteLocation, fromListByteCode.1, fromListByteCode.2),
   (toListByteLocation, toListByteCode.1, toListByteCode.2),
   (sumListLengthLocation, sumListLengthCode.1, sumListLengthCode.2),
   (concatByteLocation, concatByteCode.1, concatByteCode.2)]

end Flapjack.Compiler.Backend.BvlToBvi
