import Flapjack.Compiler.Backend.FlatToClos.Arith
import Flapjack.Compiler.Backend.FlatToClos.CopyByte

/-! Translation of flat operators to closure operators and explicit checks. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendCommon

/-- Lower a flat operator, retaining the source's exception checks and fallback
for unsupported primitive/type combinations. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_op_def"]
def compileOp (t : Tra) (op : FlatLang.Op) (xs : List ClosLang.Exp) : ClosLang.Exp :=
  let fallback : ClosLang.Exp := .let .none xs (.var .none 0)
  let v := ClosLang.Exp.var t
  let int (i : Int) : ClosLang.Exp := .op t (.intOp (.const i)) []
  let fail (tag : Nat) : ClosLang.Exp := .raise t (.op t (.blockOp (.cons tag)) [])
  let checked (test : ClosLang.Op) (args : List ClosLang.Exp) (operation : ClosLang.Op)
      (operands : List ClosLang.Exp) : ClosLang.Exp :=
    .let t xs (.ifThenElse t (.op t test args) (.op t operation operands) (fail 3))
  match op with
  | .tagLenEq tag n => .op t (.blockOp (.tagLenEq tag n)) xs
  | .lenEq n => .op t (.blockOp (.lenEq n)) xs
  | .el n => arg1 xs (fun x => .op t (.memOp .el) [.op .none (.intOp (.const (Int.ofNat n))) [], x])
  | .globalVarAlloc n => .let t xs (.op t (.globOp .allocGlobal) [int (Int.ofNat n)])
  | .globalVarInit n => .op t (.globOp (.setGlobal (n + 1))) xs
  | .globalVarLookup n => .op t (.globOp (.global (n + 1))) xs
  | .id => arg1 xs id
  | .src .opapp => arg2 xs (fun x f => .app t none f [x])
  | .src .opassign => arg2 xs (fun x y => .op t (.memOp .update)
      [x, .op .none (.intOp (.const 0)) [], y])
  | .src .opref => .op t (.memOp .ref) xs
  | .src .configGC => .op t (.memOp .configGC) xs
  | .src .equality => .op t (.blockOp .equal) xs
  | .src (.ffi n) => .op t (.ffi n) xs
  | .src .listAppend => .op t (.blockOp .listAppend) xs
  | .src .vlength => .op t (.blockOp .lengthBlock) xs
  | .src .alength => .op t (.memOp .length) xs
  | .src .implode => .op t (.memOp .fromListByte) xs
  | .src .explode => .op t (.memOp .toListByte) xs
  | .src .strlen => .op t (.memOp .lengthByteVec) xs
  | .src .strcat => .op t (.memOp .concatByteVec) xs
  | .src .copyStrStr | .src .copyAw8Str => .let t xs (copyByteStr t)
  | .src .copyStrAw8 | .src .copyAw8Aw8 => .let t xs (copyByteAw8 t)
  | .src .xorAw8StrUnsafe => .op t (.memOp .xorByte) xs
  | .src .vfromList => .op t (.blockOp (.fromList 0)) xs
  | .src (.test test ty) =>
      match ty with
      | .boolT => .op t (.blockOp (.boolTest test)) xs
      | .charT | .wordT .w8 => .op t (.wordOp (.wordTest .w8 test)) xs
      | .intT =>
          match test with
          | .compare .lt => .op t (.intOp .less) xs
          | .compare .leq => .op t (.intOp .lessEq) xs
          | .compare .gt => .op t (.intOp .greater) xs
          | .compare .geq => .op t (.intOp .greaterEq) xs
          | _ => .op t (.blockOp .equal) xs
      | .float64T =>
          let cmp := match test with
            | .compare .lt => FpCmp.less
            | .compare .leq => FpCmp.lessEqual
            | .compare .gt => FpCmp.greater
            | .compare .geq => FpCmp.greaterEqual
            | _ => FpCmp.equal
          .op t (.wordOp (.fpCmp cmp)) xs
      | .strT =>
          match test with
          | .compare b => .op t (.memOp (.stringCmp false b)) xs
          | .altCompare b => .op t (.memOp (.stringCmp true b)) xs
          | _ => .op t (.blockOp .equal) xs
      | _ => .op t (.blockOp .equal) xs
  | .src .aw8length => .op t (.memOp .lengthByte) xs
  | .src .aallocFixed => .op t (.memOp .ref) xs
  | .src .aalloc => .let t xs (.ifThenElse t (.op t (.intOp .less) [int 0, v 1])
      (fail 3) (.op t (.memOp .refArray) [v 0, v 1]))
  | .src .aw8alloc => .let t xs (.ifThenElse t (.op t (.intOp .less) [int 0, v 1])
      (fail 3) (.op t (.memOp (.refByte false)) [v 0, v 1]))
  | .src .vsub => checked (.blockOp .boundsCheckBlock) [v 0, v 1] (.memOp .el) [v 0, v 1]
  | .src .vsubUnsafe | .src .asubUnsafe => .op t (.memOp .el) xs
  | .src .asub => checked (.memOp .boundsCheckArray) [v 0, v 1] (.memOp .el) [v 0, v 1]
  | .src .aupdate => checked (.memOp .boundsCheckArray) [v 1, v 2] (.memOp .update) [v 0, v 1, v 2]
  | .src .aupdateUnsafe => .op t (.memOp .update) xs
  | .src .aw8sub => checked (.memOp (.boundsCheckByte false)) [v 0, v 1] (.memOp .derefByte) [v 0, v 1]
  | .src .aw8subUnsafe => .op t (.memOp .derefByte) xs
  | .src .aw8update => checked (.memOp (.boundsCheckByte false)) [v 1, v 2] (.memOp .updateByte) [v 0, v 1, v 2]
  | .src .aw8updateUnsafe => .op t (.memOp .updateByte) xs
  | .src .strsub => checked (.memOp (.boundsCheckByte false)) [v 0, v 1] (.memOp .derefByteVec) [v 0, v 1]
  | .src (.shift ws sh n) => .op t (.wordOp (.wordShift ws sh n)) xs
  | .src .eval => .op t .install xs
  | .src (.thunkOp x) => .op t (.thunkOp x) xs
  | .src (.arith a ty) => compileArith t a ty xs
  | .src (.fromTo (.wordT .w8) .intT) => arg1 xs id
  | .src (.fromTo (.wordT .w64) .intT) => .op t (.wordOp .wordToInt) xs
  | .src (.fromTo .intT (.wordT .w8)) => arg1 xs (fun x => .op t (.intOp .mod) [int 256, x])
  | .src (.fromTo .intT (.wordT .w64)) => .op t (.wordOp .wordFromInt) xs
  | .src (.fromTo .intT .charT) =>
      .let t xs (.ifThenElse t (.op t (.intOp .less)
        [.op .none (.intOp (.const 0)) [], v 0]) (fail 1)
        (.ifThenElse t (.op t (.intOp .less)
          [v 0, .op .none (.intOp (.const 255)) []]) (fail 1) (v 0)))
  | .src _ => fallback

end Flapjack.Compiler.Backend.FlatToClos
