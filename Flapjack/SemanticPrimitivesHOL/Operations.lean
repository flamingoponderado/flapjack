import Flapjack.SemanticPrimitivesHOL

/-! Source equality and function application. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "eq_result"]
inductive EqResult where
  | val : Bool → EqResult
  | typeError
  deriving DecidableEq

mutual
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_eq_def"]
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
  | .env _ (gen1, id1), .env _ (gen2, id2) => .val (gen1 == gen2 && id1 == id2)
  | _, _ => .typeError
termination_by sizeOf first

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_eq_def"]
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

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_opapp_def"]
def doOpApp : List Value → Option (SemEnv Value × AstHOL.Exp)
  | [.closure env name body, value] => some ({ env with v := nsBind name value env.v }, body)
  | [.recclosure env funs name, value] =>
    if (funs.map fun (f, _, _) => f).Nodup then
      match findRecFun name funs with
      | none => none
      | some (arg, body) =>
        some ({ env with v := nsBind arg value (buildRecEnv funs env env.v) }, body)
    else none
  | _ => none

end Flapjack.SemanticPrimitivesHOL
