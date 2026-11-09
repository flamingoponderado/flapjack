module

public import Flapjack.Compiler.Backend.ClosCall

@[expose] public section

/-! The original known-function free-variable traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang DbVars

mutual
/-- Annotate expressions and collect their source de Bruijn variable set. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "free_def"]
def freeHOL : List Exp → List Exp × DbVarSet
  | [] => ([], .empty)
  | e :: es =>
    let (e', vars) := freeExpHOL e
    let (es', rest) := freeHOL es
    (e' :: es', mkUnion vars rest)
termination_by es => sizeOf es

/-- Single-expression helper for the original list traversal. -/
def freeExpHOL : Exp → Exp × DbVarSet
  | .var trace index => (.var trace index, .var index)
  | .ifThenElse trace x y z =>
    let (x', a) := freeExpHOL x
    let (y', b) := freeExpHOL y
    let (z', c) := freeExpHOL z
    (.ifThenElse trace x' y' z', mkUnion a (mkUnion b c))
  | .let trace xs body =>
    let (xs', a) := freeHOL xs
    let (body', b) := freeExpHOL body
    (.let trace xs' body', mkUnion a (.shift xs.length b))
  | .raise trace body =>
    let (body', vars) := freeExpHOL body
    (.raise trace body', vars)
  | .tick trace body =>
    let (body', vars) := freeExpHOL body
    (.tick trace body', vars)
  | .op trace op xs =>
    let (xs', vars) := freeHOL xs
    (.op trace op xs', vars)
  | .app trace loc fn xs =>
    let (fn', a) := freeExpHOL fn
    let (xs', b) := freeHOL xs
    (.app trace loc fn' xs', mkUnion a b)
  | .fn name loc _ arity body =>
    let (body', vars) := freeExpHOL body
    let shifted := DbVarSet.shift arity vars
    (.fn name loc (some (varsToList shifted)) arity body', shifted)
  | .letrec names loc _ fns body =>
    let result := freeFunsHOL fns.length fns
    let vars := listMkUnion (result.map Prod.snd)
    let (body', bodyVars) := freeExpHOL body
    (.letrec names loc (some (varsToList vars)) (result.map Prod.fst) body',
      mkUnion vars (.shift fns.length bodyVars))
  | .handle trace body handler =>
    let (body', a) := freeExpHOL body
    let (handler', b) := freeExpHOL handler
    (.handle trace body' handler', mkUnion a (.shift 1 b))
  | .call trace ticks dest xs =>
    let (xs', vars) := freeHOL xs
    (.call trace ticks dest xs', vars)
termination_by e => sizeOf e

/-- Annotate recursive-function bodies with the common group size. -/
def freeFunsHOL (count : Nat) : List (Nat × Exp) → List ((Nat × Exp) × DbVarSet)
  | [] => []
  | (arity, body) :: rest =>
    let (body', vars) := freeExpHOL body
    ((arity, body'), .shift (arity + count) vars) :: freeFunsHOL count rest
termination_by fs => sizeOf fs
end

/-- A source expression is closed exactly when its source free-variable
tree is empty. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "closed_def"]
def closedHOL (e : Exp) : Bool := sptIsEmpty (dbToSet (freeHOL [e]).2)

end Flapjack.Compiler.Backend.ClosKnown
