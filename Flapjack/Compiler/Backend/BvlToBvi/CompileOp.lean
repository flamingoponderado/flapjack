module

public import Flapjack.Compiler.Backend.BvlToBvi
public import Flapjack.Compiler.Backend.BvlToBvi.Analysis
public import Flapjack.Compiler.Backend.BackendCommon.BvlStubs

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Operation lowering for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private def zero : Bvi.Exp := .op (.intOp (.const 0)) []
private def argsOrZero (xs : List Bvi.Exp) : List Bvi.Exp := if xs.isEmpty then [zero] else xs
/-- Location of the list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ListLength_location_def"]
def listLengthLocation : Nat := initGlobalsLocation + 1

/-- The evaluated location of the list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ListLength_location_eq"]
theorem listLengthLocation_eq : listLengthLocation = 65 := rfl

/-- Location of the byte-list conversion stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "FromListByte_location_def"]
def fromListByteLocation : Nat := listLengthLocation + 1

/-- The evaluated location of the byte-list conversion stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "FromListByte_location_eq"]
theorem fromListByteLocation_eq : fromListByteLocation = 66 := rfl

/-- Location of the byte-array to list stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ToListByte_location_def"]
def toListByteLocation : Nat := fromListByteLocation + 1

/-- The evaluated location of the byte-array to list stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ToListByte_location_eq"]
theorem toListByteLocation_eq : toListByteLocation = 67 := rfl

/-- Location of the combined list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "SumListLength_location_def"]
def sumListLengthLocation : Nat := toListByteLocation + 1

/-- The evaluated location of the combined list-length stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "SumListLength_location_eq"]
theorem sumListLengthLocation_eq : sumListLengthLocation = 68 := rfl

/-- Location of the byte-concatenation stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ConcatByte_location_def"]
def concatByteLocation : Nat := sumListLengthLocation + 1

/-- The evaluated location of the byte-concatenation stub. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "ConcatByte_location_eq"]
theorem concatByteLocation_eq : concatByteLocation = 69 := rfl
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

/-- The operation lowering written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_op_pmatch"]
theorem compileOp_pmatch (op : ClosLang.Op) (xs : List Bvi.Exp) :
    compileOp op xs = match op with
      | .intOp (.const i) =>
          match xs with
          | [] => compileInt i
          | _ => .let [.op (.intOp (.const 0)) xs] (compileInt i)
      | .globOp (.global n) =>
          if xs.isEmpty then .op (.globOp (.global (n + 1))) []
          else .let xs (.op (.memOp .el)
            [.op (.intOp .add) [.op (.intOp (.const 2)) [], .var 0],
              .op (.globOp .globalsPtr) []])
      | .globOp (.setGlobal n) => .op (.globOp (.setGlobal (n + 1))) xs
      | .globOp .allocGlobal => .call 0 (some allocGlobalLocation) xs none
      | .blockOp (.fromList n) =>
          .let (if xs.isEmpty then [.op (.intOp (.const 0)) []] else xs)
            (.op (.blockOp (.fromList n))
              [.var 0,
                .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none])
      | .install =>
          .let (if xs.length ≠ 2 then
              [.let xs (.op (.intOp (.const 0)) []), .op (.intOp (.const 0)) []]
            else xs)
            (.op .install
              [.call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none,
                .call 0 (some listLengthLocation) [.var 1, .op (.intOp (.const 0)) []] none,
                .var 0, .var 1])
      | .memOp .fromListByte =>
          .let (if xs.isEmpty then [.op (.intOp (.const 0)) []] else xs)
            (.call 0 (some fromListByteLocation)
              [.var 0, .op (.intOp (.const 0)) [],
                .op (.memOp (.refByte true))
                  [.op (.intOp (.const 0)) [],
                    .call 0 (some listLengthLocation)
                      [.var 0, .op (.intOp (.const 0)) []] none]]
              none)
      | .memOp .toListByte =>
          .let (if xs.isEmpty then [.op (.intOp (.const 0)) []] else xs)
            (.call 0 (some toListByteLocation)
              [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)
      | .memOp .concatByteVec =>
          .let (if xs.isEmpty then [.op (.intOp (.const 0)) []] else xs)
            (.call 0 (some concatByteLocation)
              [.var 0, .op (.intOp (.const 0)) [],
                .op (.memOp (.refByte true))
                  [.op (.intOp (.const 0)) [],
                    .call 0 (some sumListLengthLocation)
                      [.var 0, .op (.intOp (.const 0)) []] none]]
              none)
      | .memOp (.copyByte true) =>
          .let (if xs.length < 3 then
              xs ++ List.replicate 3 (.op (.intOp (.const 0)) [])
            else xs)
            (.let [.op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .var 0]]
              (.let [.op (.memOp (.copyByte false))
                [.op (.intOp (.const 0)) [], .var 0, .var 1, .var 2, .var 3]] (.var 1)))
      | .label l => .op (.label (bvlNumStubs + bvlToBviNamespaces * l)) xs
      | .blockOp (.build ps) => .op (.blockOp (.build ps)) xs
      | .blockOp (.equalConst p) => .op (.blockOp (.equalConst p)) xs
      | .memOp (.mutCons _ _) => .let xs (.op (.intOp (.const 0)) [])
      | .memOp .updateCons => .let xs (.op (.intOp (.const 0)) [])
      | .memOp .finaliseCons => .let xs (.op (.intOp (.const 0)) [])
      | _ => .op op xs := by
  cases op with
  | intOp i =>
    cases i
    all_goals simp [compileOp]
    all_goals cases xs
    all_goals simp_all
  | globOp g =>
    cases g
    all_goals simp [compileOp]
    all_goals cases xs
    all_goals simp_all
  | blockOp b =>
    cases b
    all_goals simp [compileOp, argsOrZero, listLength, zero]
    all_goals cases xs
    all_goals simp_all
  | memOp m =>
    cases m with
    | copyByte b =>
      cases b
      all_goals simp [compileOp, zero]
      all_goals cases xs
      all_goals simp_all
    | _ =>
      simp [compileOp, argsOrZero, listLength, zero]
      all_goals cases xs
      all_goals simp_all
  | install =>
    simp [compileOp, listLength, zero]
    all_goals cases xs
    all_goals simp_all
  | label l => simp [compileOp]
  | _ => simp [compileOp]

end Flapjack.Compiler.Backend.BvlToBvi
