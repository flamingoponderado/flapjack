import Flapjack.CakeParser.FromSexp

/-! Operator decoding for the CakeML S-expression format. Untagged pending
complete source and carrier correspondence review. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.AstHOL

private def symbolName : Sexp → Option String
  | .sym bytes => some (toStringOfBytes (.implode bytes))
  | _ => none

def decodeArith (s : Sexp) : Option Arith := do
  match ← symbolName s with
  | "Add" => some .add | "Sub" => some .sub | "Mul" => some .mul
  | "Div" => some .div | "Mod" => some .mod | "Neg" => some .neg
  | "Abs" => some .abs | "And" => some .and | "Xor" => some .xor
  | "Or" => some .or | "Not" => some .not | "Sqrt" => some .sqrt
  | "FMA" => some .fma | _ => none

def decodePrimType (s : Sexp) : Option PrimType := do
  match ← symbolName s with
  | "BoolT" => some .boolT | "IntT" => some .intT | "CharT" => some .charT
  | "StrT" => some .strT | "Word8T" => some (.wordT .w8)
  | "Word64T" => some (.wordT .w64) | "Float64T" => some .float64T | _ => none

def decodeTest (s : Sexp) : Option Test := do
  match ← symbolName s with
  | "Equal" => some .equal | "Less" => some (.compare .lt)
  | "LessEq" => some (.compare .leq) | "Greater" => some (.compare .gt)
  | "GreaterEq" => some (.compare .geq) | "AltLess" => some (.altCompare .lt)
  | "AltLessEq" => some (.altCompare .leq) | "AltGreater" => some (.altCompare .gt)
  | "AltGreaterEq" => some (.altCompare .geq) | _ => none

def decodeLog (s : Sexp) : Option Lop := do
  match ← symbolName s with
  | "Andalso" => some .andalso | "Orelse" => some .orelse | _ => none

private def decodeSimpleOp (name : String) : Option Op :=
  match name with
  | "Equality" => some .equality | "Opapp" => some .opapp
  | "Opassign" => some .opassign | "Opref" => some .opref | "Opderef" => some .opderef
  | "Aw8alloc" => some .aw8alloc | "Aw8sub" => some .aw8sub
  | "Aw8length" => some .aw8length | "Aw8update" => some .aw8update
  | "Aw8subunsafe" => some .aw8subUnsafe | "Aw8updateunsafe" => some .aw8updateUnsafe
  | "CopyStrStr" => some .copyStrStr | "CopyStrAw8" => some .copyStrAw8
  | "CopyAw8Str" => some .copyAw8Str | "CopyAw8Aw8" => some .copyAw8Aw8
  | "XorAw8Strunsafe" => some .xorAw8StrUnsafe | "Implode" => some .implode
  | "Explode" => some .explode | "Strsub" => some .strsub | "Strlen" => some .strlen
  | "Strcat" => some .strcat | "VfromList" => some .vfromList | "Vsub" => some .vsub
  | "Vsubunsafe" => some .vsubUnsafe | "Vlength" => some .vlength
  | "ListAppend" => some .listAppend | "Aalloc" => some .aalloc
  | "AallocEmpty" => some .aallocEmpty | "AallocFixed" => some .aallocFixed
  | "Asub" => some .asub | "Alength" => some .alength | "Aupdate" => some .aupdate
  | "Asubunsafe" => some .asubUnsafe | "Aupdateunsafe" => some .aupdateUnsafe
  | "ForceThunk" => some (.thunkOp .forceThunk) | "ConfigGC" => some .configGC
  | "Eval" => some .eval | "Envid" => some .envId | _ => none

/-- Decode the original operator encoding, including its dotted-pair payloads. -/
def decodeOp (s : Sexp) : Option Op :=
  match s with
  | .sym _ => (symbolName s).bind decodeSimpleOp
  | .cons (.sym name) payload =>
    let name := toStringOfBytes (.implode name)
    match payload with
    | .str _ =>
      if name == "FFI" then (destString payload).map Op.ffi else none
    | .sym _ => do
      let mode ← match symbolName payload with
        | some "Evaluated" => some ThunkMode.evaluated
        | some "NotEvaluated" => some ThunkMode.notEvaluated
        | _ => none
      if name == "AllocThunk" then some (.thunkOp (.allocThunk mode))
        else if name == "UpdateThunk" then some (.thunkOp (.updateThunk mode)) else none
    | .num n =>
      match name with
        | "Shift8Lsl" => some (.shift .w8 .lsl n) | "Shift8Lsr" => some (.shift .w8 .lsr n)
        | "Shift8Asr" => some (.shift .w8 .asr n) | "Shift8Ror" => some (.shift .w8 .ror n)
        | "Shift64Lsl" => some (.shift .w64 .lsl n) | "Shift64Lsr" => some (.shift .w64 .lsr n)
        | "Shift64Asr" => some (.shift .w64 .asr n) | "Shift64Ror" => some (.shift .w64 .ror n)
        | _ => none
    | .cons x y =>
      if name == "Arith" then do some (.arith (← decodeArith x) (← decodePrimType y))
      else if name == "FromTo" then do some (.fromTo (← decodePrimType x) (← decodePrimType y))
      else if name == "Test" then do some (.test (← decodeTest x) (← decodePrimType y))
      else none
  | _ => none

end Flapjack.CakeParser.FromSexp
