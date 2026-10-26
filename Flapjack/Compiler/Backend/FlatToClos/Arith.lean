import Flapjack.Compiler.Backend.FlatToClos.Helpers

/-! Arithmetic lowering, including the source division-by-zero checks. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendCommon

/-- Translate the source arithmetic/type pair, including all fallback cases.
The exception constructor uses `backend_common$div_tag = 2`. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_arith_def"]
def compileArith (t : Tra) (a : AstHOL.Arith) (ty : AstHOL.PrimType)
    (xs : List ClosLang.Exp) : ClosLang.Exp :=
  let fallback : ClosLang.Exp := .let .none xs (.var .none 0)
  match ty with
  | .intT =>
      match a with
      | .add => .op t (.intOp .add) xs
      | .sub => .op t (.intOp .sub) xs
      | .mul => .op t (.intOp .mult) xs
      | .div | .mod =>
          let operation := if a = .div then ClosLang.IntOp.div else ClosLang.IntOp.mod
          .let t xs
            (.ifThenElse t (.op t (.blockOp .equal)
              [.var t 0, .op t (.intOp (.const 0)) []])
              (.raise t (.op t (.blockOp (.cons 2)) []))
              (.op t (.intOp operation) [.var t 0, .var t 1]))
      | _ => fallback
  | .float64T =>
      match a with
      | .abs => .op t (.wordOp (.fpUop .abs)) xs
      | .neg => .op t (.wordOp (.fpUop .neg)) xs
      | .sqrt => .op t (.wordOp (.fpUop .sqrt)) xs
      | .add => .op t (.wordOp (.fpBop .add)) xs
      | .sub => .op t (.wordOp (.fpBop .sub)) xs
      | .mul => .op t (.wordOp (.fpBop .mul)) xs
      | .div => .op t (.wordOp (.fpBop .div)) xs
      | .fma => .op t (.wordOp (.fpTop .fma)) xs
      | _ => fallback
  | .wordT ws =>
      match a with
      | .add => .op t (.wordOp (.wordOpw ws .add)) xs
      | .sub => .op t (.wordOp (.wordOpw ws .sub)) xs
      | .and => .op t (.wordOp (.wordOpw ws .andw)) xs
      | .or => .op t (.wordOp (.wordOpw ws .orw)) xs
      | .xor => .op t (.wordOp (.wordOpw ws .xor)) xs
      | _ => fallback
  | .boolT => .op t (.blockOp .boolNot) xs
  | _ => fallback

end Flapjack.Compiler.Backend.FlatToClos
