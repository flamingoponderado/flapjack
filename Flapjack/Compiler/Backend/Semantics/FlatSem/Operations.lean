import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.SemanticPrimitivesHOL.Operations

/-! Equality and function application in the original flat-language semantics.
The full flat evaluator and source-to-flat simulation remain open. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

mutual
/-- Compare flat values, including the original closure and type-error cases. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_eq_def"]
def doEq (first second : Value) : EqResult :=
  match first, second with
  | .litv a, .litv b => if litSameType a b then .val (decide (a = b)) else .typeError
  | .loc a x, .loc b y => if a && b then .val (x == y) else .typeError
  | .conv a xs, .conv b ys =>
    if a = b ∧ xs.length = ys.length then doEqList xs ys
    else if ctorSameType a b then .val false else .typeError
  | .vectorv xs, .vectorv ys =>
    if xs.length = ys.length then doEqList xs ys else .val false
  | .closure _ _ _, .closure _ _ _ => .val true
  | .closure _ _ _, .recclosure _ _ _ => .val true
  | .recclosure _ _ _, .closure _ _ _ => .val true
  | .recclosure _ _ _, .recclosure _ _ _ => .val true
  | _, _ => .typeError
termination_by sizeOf first

/-- Compare lists of flat values, short-circuiting on the first difference. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_eq_def"]
def doEqList (first second : List Value) : EqResult :=
  match first, second with
  | [], [] => .val true
  | x :: xs, y :: ys => match doEq x y with
    | .val false => .val false
    | .val true => doEqList xs ys
    | .typeError => .typeError
  | _, _ => .val false
termination_by sizeOf first
end

/-- Apply a flat closure or a distinct recursive-function bundle. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_opapp_def"]
def doOpApp : List Value → Option (Environment Value × FlatLang.Exp)
  | [.closure env name body, value] => some ({ env with v := (name, value) :: env.v }, body)
  | [.recclosure env funs name, value] =>
    if (funs.map Prod.fst).Nodup then
      match findRecFun name funs with
      | none => none
      | some (arg, body) =>
        some ({ env with v := (arg, value) :: buildRecEnv funs env env.v }, body)
    else none
  | _ => none

end Flapjack.Compiler.Backend.FlatSem
